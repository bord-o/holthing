open Absyn

type type_error =
  | UnboundVariable of string * pos
  | UnboundFunction of string * pos
  | UnboundType of string * pos
  | UnboundConstructor of string * pos
  | TypeMismatch of ty * ty * pos
  | ArityMismatch of int * int * pos
  | InvalidPattern of pattern * ty * pos
  | InvalidConstructor of string * ty list * ty list * pos
  | DivisionByZero of pos
  | Other of string * pos
[@@deriving show]

type 'a type_result = ('a, type_error) result [@@deriving show]

type constructor_info = { name : string; arg_types : ty list; return_type : ty }
[@@deriving show]

type type_info = {
  name : string;
  type_params : string list;
  constructors : constructor_info list;
  alias : ty option;
}
[@@deriving show]

type fun_info = {
  name : string;
  params : param list;
  return_type : ty option;
  body : exp;
  specs : proof_spec list;
}
[@@deriving show]

type env = {
  vals : (string * ty) list;
  funs : (string * fun_info) list;
  types : (string * type_info) list;
  type_params : string list;
}
[@@deriving show]

let ( let* ) = Result.bind

let empty_env = { vals = []; funs = []; types = []; type_params = [] }
[@@deriving show]

let builtin_types =
  [
    ("int", { name = "int"; type_params = []; constructors = []; alias = None });
    ( "bool",
      { name = "bool"; type_params = []; constructors = []; alias = None } );
    ( "string",
      { name = "string"; type_params = []; constructors = []; alias = None } );
    ( "unit",
      { name = "unit"; type_params = []; constructors = []; alias = None } );
  ]

let default_env = { empty_env with types = builtin_types }
let lookup_val name env = List.assoc_opt name env.vals
let lookup_fun name env = List.assoc_opt name env.funs
let lookup_type name env = List.assoc_opt name env.types
let add_val name ty env = { env with vals = (name, ty) :: env.vals }
let add_fun name fun_info env = { env with funs = (name, fun_info) :: env.funs }

let add_type name type_info env =
  { env with types = (name, type_info) :: env.types }

let add_type_param name env = { env with type_params = name :: env.type_params }
let is_type_param name env = List.mem name env.type_params

let rec types_equal ty1 ty2 =
  match (ty1, ty2) with
  | NameTy (n1, _), NameTy (n2, _) -> n1 = n2
  | GenericTy (n1, args1, _), GenericTy (n2, args2, _) ->
      n1 = n2
      && List.length args1 = List.length args2
      && List.for_all2 types_equal args1 args2
  | FunTy (a1, r1, _), FunTy (a2, r2, _) ->
      types_equal a1 a2 && types_equal r1 r2
  | _ -> false

let rec expand_type_alias env ty =
  match ty with
  | NameTy (name, _pos) -> (
      match lookup_type name env with
      | Some type_info -> (
          match type_info.alias with
          | Some aliased_type -> expand_type_alias env aliased_type
          | None -> ty)
      | None -> ty)
  | GenericTy (name, args, pos) -> (
      match lookup_type name env with
      | Some type_info -> (
          match type_info.alias with
          | Some _aliased_type ->
              (* TODO: substitute type parameters in aliased type *)
              GenericTy (name, List.map (expand_type_alias env) args, pos)
          | None -> GenericTy (name, List.map (expand_type_alias env) args, pos)
          )
      | None -> GenericTy (name, List.map (expand_type_alias env) args, pos))
  | FunTy (arg, ret, pos) ->
      FunTy (expand_type_alias env arg, expand_type_alias env ret, pos)

and validate_type env ty =
  let expanded_ty = expand_type_alias env ty in
  match expanded_ty with
  | NameTy (name, pos) ->
      if is_type_param name env || lookup_type name env <> None then
        Ok expanded_ty
      else Error (UnboundType (name, pos))
  | GenericTy (name, args, pos) -> (
      match lookup_type name env with
      | None -> Error (UnboundType (name, pos))
      | Some type_info ->
          if List.length args <> List.length type_info.type_params then
            Error
              (ArityMismatch
                 (List.length type_info.type_params, List.length args, pos))
          else
            let rec validate_args acc = function
              | [] -> Ok (List.rev acc)
              | arg :: rest ->
                  let* validated_arg = validate_type env arg in
                  validate_args (validated_arg :: acc) rest
            in
            let* validated_args = validate_args [] args in
            Ok (GenericTy (name, validated_args, pos)))
  | FunTy (arg, ret, pos) ->
      let* validated_arg = validate_type env arg in
      let* validated_ret = validate_type env ret in
      Ok (FunTy (validated_arg, validated_ret, pos))

let get_literal_type = function
  | IntLit _ -> NameTy ("int", Lexing.dummy_pos)
  | BoolLit _ -> NameTy ("bool", Lexing.dummy_pos)
  | StringLit _ -> NameTy ("string", Lexing.dummy_pos)
  | UnitLit -> NameTy ("unit", Lexing.dummy_pos)

let get_binop_type op =
  match op with
  | Add | Sub | Mul | Div ->
      ( NameTy ("int", Lexing.dummy_pos),
        NameTy ("int", Lexing.dummy_pos),
        NameTy ("int", Lexing.dummy_pos) )
  | Eq | Neq | Lt | Le | Gt | Ge ->
      ( NameTy ("int", Lexing.dummy_pos),
        NameTy ("int", Lexing.dummy_pos),
        NameTy ("bool", Lexing.dummy_pos) )
  | And | Or ->
      ( NameTy ("bool", Lexing.dummy_pos),
        NameTy ("bool", Lexing.dummy_pos),
        NameTy ("bool", Lexing.dummy_pos) )

let find_constructor name env =
  let rec search_types types =
    match types with
    | [] -> None
    | (_, (tinfo : type_info)) :: rest ->
        let constructors = tinfo.constructors in
        let rec search_constructors ctors =
          match (ctors : constructor_info list) with
          | [] -> search_types rest
          | ctor :: remaining ->
              if ctor.name = name then Some ctor
              else search_constructors remaining
        in
        search_constructors constructors
  in
  search_types env.types

let rec check_exp env exp =
  match exp with
  | VarExp (name, pos) -> (
      match lookup_val name env with
      | Some ty -> Ok ty
      | None -> Error (UnboundVariable (name, pos)))
  | LiteralExp (lit, _) -> Ok (get_literal_type lit)
  | CallExp (func_exp, args, pos) ->
      let* func_type = check_exp env func_exp in
      let rec check_args acc = function
        | [] -> Ok (List.rev acc)
        | arg :: rest -> (
            match check_exp env arg with
            | Ok arg_type -> check_args (arg_type :: acc) rest
            | Error e -> Error e)
      in
      let* arg_types = check_args [] args in
      let rec apply_args func_ty args_left =
        match (func_ty, args_left) with
        | _, [] -> Ok func_ty
        | FunTy (param_type, return_type, _), arg_type :: rest_args ->
            if types_equal param_type arg_type then
              apply_args return_type rest_args
            else Error (TypeMismatch (param_type, arg_type, pos))
        | _ ->
            Error
              (TypeMismatch
                 ( FunTy (NameTy ("?", pos), NameTy ("?", pos), pos),
                   func_ty,
                   pos ))
      in
      apply_args func_type arg_types
  | BinOpExp (left, op, right, pos) ->
      let* left_type = check_exp env left in
      let* right_type = check_exp env right in
      let expected_left, expected_right, result_type = get_binop_type op in
      if
        types_equal left_type expected_left
        && types_equal right_type expected_right
      then Ok result_type
      else if not (types_equal left_type expected_left) then
        Error (TypeMismatch (expected_left, left_type, pos))
      else Error (TypeMismatch (expected_right, right_type, pos))
  | UnaryOpExp ("-", exp, pos) ->
      let* exp_type = check_exp env exp in
      let int_type = NameTy ("int", pos) in
      if types_equal exp_type int_type then Ok int_type
      else Error (TypeMismatch (int_type, exp_type, pos))
  | UnaryOpExp (op, _, pos) ->
      Error (Other ("Unknown unary operator: " ^ op, pos))
  | IfExp (cond, then_exp, else_exp, pos) ->
      let* cond_type = check_exp env cond in
      let* then_type = check_exp env then_exp in
      let* else_type = check_exp env else_exp in
      let bool_type = NameTy ("bool", pos) in
      if not (types_equal cond_type bool_type) then
        Error (TypeMismatch (bool_type, cond_type, pos))
      else if not (types_equal then_type else_type) then
        Error (TypeMismatch (then_type, else_type, pos))
      else Ok then_type
  | LetExp (name, ty_opt, value_exp, body_exp, pos) -> (
      let* value_type = check_exp env value_exp in
      match ty_opt with
      | None ->
          let new_env = add_val name value_type env in
          check_exp new_env body_exp
      | Some declared_ty ->
          let* validated_ty = validate_type env declared_ty in
          if types_equal value_type validated_ty then
            let new_env = add_val name validated_ty env in
            check_exp new_env body_exp
          else Error (TypeMismatch (validated_ty, value_type, pos)))
  | BlockExp (exps, pos) -> (
      match List.rev exps with
      | [] -> Ok (NameTy ("unit", pos))
      | last :: rest ->
          let rec check_rest = function
            | [] -> Ok ()
            | exp :: remaining ->
                let* _ = check_exp env exp in
                check_rest remaining
          in
          let* () = check_rest (List.rev rest) in
          check_exp env last)
  | MatchExp (scrutinee, cases, pos) -> (
      let* scrutinee_type = check_exp env scrutinee in
      let rec check_cases acc = function
        | [] -> Ok (List.rev acc)
        | (pattern, exp) :: rest ->
            let* pattern_env = check_pattern env pattern scrutinee_type in
            let* exp_type = check_exp pattern_env exp in
            check_cases (exp_type :: acc) rest
      in
      let* case_types = check_cases [] cases in
      match case_types with
      | [] -> Error (Other ("Empty match expression", pos))
      | first_type :: rest_types ->
          let all_same = List.for_all (types_equal first_type) rest_types in
          if all_same then Ok first_type
          else Error (Other ("Match branches have different types", pos)))
  | ConstructorExp (name, args, pos) -> (
      match find_constructor name env with
      | None -> Error (UnboundConstructor (name, pos))
      | Some ctor ->
          let rec check_args acc expected_types actual_args =
            match (expected_types, actual_args) with
            | [], [] -> Ok (List.rev acc)
            | [], _ ->
                Error
                  (ArityMismatch
                     (List.length ctor.arg_types, List.length args, pos))
            | _, [] ->
                Error
                  (ArityMismatch
                     (List.length ctor.arg_types, List.length args, pos))
            | expected_type :: rest_expected, actual_arg :: rest_actual ->
                let* actual_type = check_exp env actual_arg in
                if types_equal expected_type actual_type then
                  check_args (actual_type :: acc) rest_expected rest_actual
                else Error (TypeMismatch (expected_type, actual_type, pos))
          in
          let* _ = check_args [] ctor.arg_types args in
          Ok ctor.return_type)
  | LambdaExp (params, body, pos) ->
      let rec validate_params acc = function
        | [] -> Ok (List.rev acc)
        | param :: rest ->
            let* validated_ty = validate_type env param.ty in
            validate_params ((param.name, validated_ty) :: acc) rest
      in
      let* param_types = validate_params [] params in
      let lambda_env =
        List.fold_left
          (fun env (name, ty) -> add_val name ty env)
          env param_types
      in
      let* body_type = check_exp lambda_env body in
      let lambda_type =
        List.fold_right
          (fun param acc_type -> FunTy (param.ty, acc_type, pos))
          params body_type
      in
      Ok lambda_type

and check_pattern env pattern expected_type =
  match pattern with
  | WildcardPat _ -> Ok env
  | VarPat (name, _) -> Ok (add_val name expected_type env)
  | LiteralPat (lit, pos) ->
      let literal_type = get_literal_type lit in
      if types_equal literal_type expected_type then Ok env
      else Error (InvalidPattern (pattern, expected_type, pos))
  | ConstructorPat (name, patterns, pos) -> (
      match find_constructor name env with
      | None -> Error (UnboundConstructor (name, pos))
      | Some ctor ->
          if not (types_equal ctor.return_type expected_type) then
            Error (TypeMismatch (expected_type, ctor.return_type, pos))
          else if List.length patterns <> List.length ctor.arg_types then
            Error
              (ArityMismatch
                 (List.length ctor.arg_types, List.length patterns, pos))
          else
            let rec check_patterns acc expected_types actual_patterns =
              match (expected_types, actual_patterns) with
              | [], [] -> Ok acc
              | expected_type :: rest_expected, actual_pattern :: rest_patterns
                ->
                  let* updated_env =
                    check_pattern acc actual_pattern expected_type
                  in
                  check_patterns updated_env rest_expected rest_patterns
              | _ ->
                  Error
                    (ArityMismatch
                       (List.length ctor.arg_types, List.length patterns, pos))
            in
            check_patterns env ctor.arg_types patterns)

let check_dec env dec =
  match dec with
  | LetDec { name; ty; value; pos } -> (
      let* value_type = check_exp env value in
      match ty with
      | None -> Ok (add_val name value_type env, value_type)
      | Some declared_ty ->
          let* validated_ty = validate_type env declared_ty in
          if types_equal value_type validated_ty then
            Ok (add_val name validated_ty env, validated_ty)
          else Error (TypeMismatch (validated_ty, value_type, pos)))
  | FunDec { name; params; return_ty; body; specs; pos } -> (
      let rec validate_params acc = function
        | [] -> Ok (List.rev acc)
        | param :: rest ->
            let* validated_ty = validate_type env param.ty in
            validate_params ((param.name, validated_ty) :: acc) rest
      in
      let* param_types = validate_params [] params in
      let param_env =
        List.fold_left
          (fun env (name, ty) -> add_val name ty env)
          env param_types
      in
      (* Add the function's own type for recursive calls *)
      let provisional_return_type =
        match return_ty with
        | Some declared_ty -> declared_ty
        | None -> NameTy ("unit", pos)
        (* Will be corrected after body type checking *)
      in
      let provisional_fun_type =
        List.fold_right
          (fun param acc_type -> FunTy (param.ty, acc_type, pos))
          params provisional_return_type
      in
      let func_env = add_val name provisional_fun_type param_env in

      let* body_type = check_exp func_env body in
      match return_ty with
      | None ->
          let fun_info =
            { name; params; return_type = Some body_type; body; specs }
          in
          let fun_type =
            List.fold_right
              (fun param acc_type -> FunTy (param.ty, acc_type, pos))
              params body_type
          in
          Ok (add_fun name fun_info (add_val name fun_type env), fun_type)
      | Some declared_ty ->
          let* validated_ty = validate_type env declared_ty in
          if types_equal body_type validated_ty then
            let fun_info =
              { name; params; return_type = Some validated_ty; body; specs }
            in
            let fun_type =
              List.fold_right
                (fun param acc_type -> FunTy (param.ty, acc_type, pos))
                params validated_ty
            in
            Ok (add_fun name fun_info (add_val name fun_type env), fun_type)
          else Error (TypeMismatch (validated_ty, body_type, pos)))
  | TypeDec { name; type_params; definition; pos } -> (
      let param_env =
        List.fold_left
          (fun env param -> add_type_param param env)
          env type_params
      in
      (* Add the type name to environment first for recursive references *)
      let recursive_type_info =
        { name; type_params; constructors = []; alias = None }
      in
      let recursive_env = add_type name recursive_type_info param_env in
      match definition with
      | VariantDef variants ->
          let rec validate_variants acc = function
            | [] -> Ok (List.rev acc)
            | variant :: rest ->
                let rec validate_args acc_args = function
                  | [] -> Ok (List.rev acc_args)
                  | arg_type :: rest_args ->
                      let* validated_ty =
                        validate_type recursive_env arg_type
                      in
                      validate_args (validated_ty :: acc_args) rest_args
                in
                let* validated_arg_types = validate_args [] variant.args in
                let return_type =
                  if type_params = [] then NameTy (name, pos)
                  else
                    GenericTy
                      ( name,
                        List.map (fun p -> NameTy (p, pos)) type_params,
                        pos )
                in
                let ctor_info =
                  {
                    name = variant.name;
                    arg_types = validated_arg_types;
                    return_type;
                  }
                in
                validate_variants (ctor_info :: acc) rest
          in
          let* constructors = validate_variants [] variants in
          let type_info = { name; type_params; constructors; alias = None } in
          Ok (add_type name type_info env, NameTy (name, pos))
      | AliasDef aliased_type ->
          let* validated_alias = validate_type recursive_env aliased_type in
          let type_info =
            {
              name;
              type_params;
              constructors = [];
              alias = Some validated_alias;
            }
          in
          Ok (add_type name type_info env, NameTy (name, pos)))

let rec check_all env program =
  match program with
  | [] -> Ok env
  | dec :: decs ->
      let* updated_env, _ = check_dec env dec in
      check_all updated_env decs
