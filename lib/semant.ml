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

let pp_type_error fmt = function
  | UnboundVariable (name, pos) ->
      Format.fprintf fmt "Unbound variable '%s' at %a" name pp_pos pos
  | UnboundFunction (name, pos) ->
      Format.fprintf fmt "Unbound function '%s' at %a" name pp_pos pos
  | UnboundType (name, pos) ->
      Format.fprintf fmt "Unbound type '%s' at %a" name pp_pos pos
  | UnboundConstructor (name, pos) ->
      Format.fprintf fmt "Unbound constructor '%s' at %a" name pp_pos pos
  | TypeMismatch (expected, actual, pos) ->
      Format.fprintf fmt "Type mismatch at %a: expected %a, got %a"
        pp_pos pos pp_ty expected pp_ty actual
  | ArityMismatch (expected, actual, pos) ->
      Format.fprintf fmt "Arity mismatch at %a: expected %d arguments, got %d"
        pp_pos pos expected actual
  | InvalidPattern (pat, ty, pos) ->
      Format.fprintf fmt "Invalid pattern %a for type %a at %a"
        pp_pattern pat pp_ty ty pp_pos pos
  | InvalidConstructor (name, expected, actual, pos) ->
      Format.fprintf fmt "Constructor '%s' at %a expects %d arguments, got %d"
        name pp_pos pos (List.length expected) (List.length actual)
  | DivisionByZero pos ->
      Format.fprintf fmt "Division by zero at %a" pp_pos pos
  | Other (msg, pos) ->
      Format.fprintf fmt "%s at %a" msg pp_pos pos

type 'a type_result = ('a, type_error) result

type constructor_info = {
  name : string;
  arg_types : ty list;
  return_type : ty;
}

type type_info = {
  name : string;
  type_params : string list;
  constructors : constructor_info list;
  alias : ty option;
}

type fun_info = {
  name : string;
  params : param list;
  return_type : ty option;
  body : exp;
  specs : proof_spec list;
}

type env = {
  vals : (string * ty) list;
  funs : (string * fun_info) list;
  types : (string * type_info) list;
  type_params : string list;
}

let empty_env = {
  vals = [];
  funs = [];
  types = [];
  type_params = [];
}

let builtin_types = [
  ("int", { name = "int"; type_params = []; constructors = []; alias = None });
  ("bool", { name = "bool"; type_params = []; constructors = []; alias = None });
  ("string", { name = "string"; type_params = []; constructors = []; alias = None });
  ("unit", { name = "unit"; type_params = []; constructors = []; alias = None });
]

let default_env = { empty_env with types = builtin_types }

let lookup_val name env =
  try Some (List.assoc name env.vals)
  with Not_found -> None

let lookup_fun name env =
  try Some (List.assoc name env.funs)
  with Not_found -> None

let lookup_type name env =
  try Some (List.assoc name env.types)
  with Not_found -> None

let add_val name ty env =
  { env with vals = (name, ty) :: env.vals }

let add_fun name fun_info env =
  { env with funs = (name, fun_info) :: env.funs }

let add_type name type_info env =
  { env with types = (name, type_info) :: env.types }

let add_type_param name env =
  { env with type_params = name :: env.type_params }

let is_type_param name env =
  List.mem name env.type_params

let rec types_equal ty1 ty2 =
  match (ty1, ty2) with
  | (NameTy (n1, _), NameTy (n2, _)) -> n1 = n2
  | (GenericTy (n1, args1, _), GenericTy (n2, args2, _)) ->
      n1 = n2 && List.length args1 = List.length args2 &&
      List.for_all2 types_equal args1 args2
  | (FunTy (a1, r1, _), FunTy (a2, r2, _)) ->
      types_equal a1 a2 && types_equal r1 r2
  | _ -> false

let rec expand_type_alias env ty =
  match ty with
  | NameTy (name, _pos) ->
      begin match lookup_type name env with
      | Some type_info ->
          begin match type_info.alias with
          | Some aliased_type -> expand_type_alias env aliased_type
          | None -> ty
          end
      | None -> ty
      end
  | GenericTy (name, args, pos) ->
      begin match lookup_type name env with
      | Some type_info ->
          begin match type_info.alias with
          | Some _aliased_type -> 
              (* TODO: substitute type parameters in aliased type *)
              GenericTy (name, List.map (expand_type_alias env) args, pos)
          | None -> GenericTy (name, List.map (expand_type_alias env) args, pos)
          end
      | None -> GenericTy (name, List.map (expand_type_alias env) args, pos)
      end
  | FunTy (arg, ret, pos) -> 
      FunTy (expand_type_alias env arg, expand_type_alias env ret, pos)

and validate_type env ty =
  let expanded_ty = expand_type_alias env ty in
  match expanded_ty with
  | NameTy (name, pos) ->
      if is_type_param name env || lookup_type name env <> None then
        Ok expanded_ty
      else
        Error (UnboundType (name, pos))
  | GenericTy (name, args, pos) ->
      begin match lookup_type name env with
      | None -> Error (UnboundType (name, pos))
      | Some type_info ->
          if List.length args <> List.length type_info.type_params then
            Error (ArityMismatch (List.length type_info.type_params, List.length args, pos))
          else
            let rec validate_args acc = function
              | [] -> Ok (List.rev acc)
              | arg :: rest ->
                  begin match validate_type env arg with
                  | Ok validated_arg -> validate_args (validated_arg :: acc) rest
                  | Error e -> Error e
                  end
            in
            begin match validate_args [] args with
            | Ok validated_args -> Ok (GenericTy (name, validated_args, pos))
            | Error e -> Error e
            end
      end
  | FunTy (arg, ret, pos) ->
      begin match validate_type env arg with
      | Ok validated_arg ->
          begin match validate_type env ret with
          | Ok validated_ret -> Ok (FunTy (validated_arg, validated_ret, pos))
          | Error e -> Error e
          end
      | Error e -> Error e
      end

let get_literal_type = function
  | IntLit _ -> NameTy ("int", Lexing.dummy_pos)
  | BoolLit _ -> NameTy ("bool", Lexing.dummy_pos)
  | StringLit _ -> NameTy ("string", Lexing.dummy_pos)
  | UnitLit -> NameTy ("unit", Lexing.dummy_pos)

let get_binop_type op =
  match op with
  | Add | Sub | Mul | Div -> 
      (NameTy ("int", Lexing.dummy_pos), NameTy ("int", Lexing.dummy_pos), NameTy ("int", Lexing.dummy_pos))
  | Eq | Neq | Lt | Le | Gt | Ge ->
      (NameTy ("int", Lexing.dummy_pos), NameTy ("int", Lexing.dummy_pos), NameTy ("bool", Lexing.dummy_pos))
  | And | Or ->
      (NameTy ("bool", Lexing.dummy_pos), NameTy ("bool", Lexing.dummy_pos), NameTy ("bool", Lexing.dummy_pos))

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
  | VarExp (name, pos) ->
      begin match lookup_val name env with
      | Some ty -> Ok ty
      | None -> Error (UnboundVariable (name, pos))
      end
      
  | LiteralExp (lit, _) ->
      Ok (get_literal_type lit)
      
  | CallExp (func_exp, args, pos) ->
      begin match check_exp env func_exp with
      | Error e -> Error e
      | Ok func_type ->
          let rec check_args acc = function
            | [] -> Ok (List.rev acc)
            | arg :: rest ->
                begin match check_exp env arg with
                | Ok arg_type -> check_args (arg_type :: acc) rest
                | Error e -> Error e
                end
          in
          begin match check_args [] args with
          | Error e -> Error e
          | Ok arg_types ->
              let rec apply_args func_ty args_left =
                match func_ty, args_left with
                | _, [] -> Ok func_ty
                | FunTy (param_type, return_type, _), arg_type :: rest_args ->
                    if types_equal param_type arg_type then
                      apply_args return_type rest_args
                    else
                      Error (TypeMismatch (param_type, arg_type, pos))
                | _ -> Error (TypeMismatch (FunTy (NameTy ("?", pos), NameTy ("?", pos), pos), func_ty, pos))
              in
              apply_args func_type arg_types
          end
      end
      
  | BinOpExp (left, op, right, pos) ->
      begin match check_exp env left with
      | Error e -> Error e
      | Ok left_type ->
          begin match check_exp env right with
          | Error e -> Error e
          | Ok right_type ->
              let (expected_left, expected_right, result_type) = get_binop_type op in
              if types_equal left_type expected_left && types_equal right_type expected_right then
                Ok result_type
              else if not (types_equal left_type expected_left) then
                Error (TypeMismatch (expected_left, left_type, pos))
              else
                Error (TypeMismatch (expected_right, right_type, pos))
          end
      end
        
  | UnaryOpExp ("-", exp, pos) ->
      begin match check_exp env exp with
      | Error e -> Error e
      | Ok exp_type ->
          let int_type = NameTy ("int", pos) in
          if types_equal exp_type int_type then
            Ok int_type
          else
            Error (TypeMismatch (int_type, exp_type, pos))
      end
        
  | UnaryOpExp (op, _, pos) ->
      Error (Other ("Unknown unary operator: " ^ op, pos))
      
  | IfExp (cond, then_exp, else_exp, pos) ->
      begin match check_exp env cond with
      | Error e -> Error e
      | Ok cond_type ->
          begin match check_exp env then_exp with
          | Error e -> Error e
          | Ok then_type ->
              begin match check_exp env else_exp with
              | Error e -> Error e
              | Ok else_type ->
                  let bool_type = NameTy ("bool", pos) in
                  if not (types_equal cond_type bool_type) then
                    Error (TypeMismatch (bool_type, cond_type, pos))
                  else if not (types_equal then_type else_type) then
                    Error (TypeMismatch (then_type, else_type, pos))
                  else
                    Ok then_type
              end
          end
      end
        
  | LetExp (name, ty_opt, value_exp, body_exp, pos) ->
      begin match check_exp env value_exp with
      | Error e -> Error e
      | Ok value_type ->
          begin match ty_opt with
          | None -> 
              let new_env = add_val name value_type env in
              check_exp new_env body_exp
          | Some declared_ty ->
              begin match validate_type env declared_ty with
              | Error e -> Error e
              | Ok validated_ty ->
                  if types_equal value_type validated_ty then
                    let new_env = add_val name validated_ty env in
                    check_exp new_env body_exp
                  else
                    Error (TypeMismatch (validated_ty, value_type, pos))
              end
          end
      end
      
  | BlockExp (exps, pos) ->
      begin match List.rev exps with
      | [] -> Ok (NameTy ("unit", pos))
      | last :: rest ->
          let rec check_rest = function
            | [] -> Ok ()
            | exp :: remaining ->
                begin match check_exp env exp with
                | Ok _ -> check_rest remaining
                | Error e -> Error e
                end
          in
          begin match check_rest (List.rev rest) with
          | Error e -> Error e
          | Ok () -> check_exp env last
          end
      end
      
  | MatchExp (scrutinee, cases, pos) ->
      begin match check_exp env scrutinee with
      | Error e -> Error e
      | Ok scrutinee_type ->
          let rec check_cases acc = function
            | [] -> Ok (List.rev acc)
            | (pattern, exp) :: rest ->
                begin match check_pattern env pattern scrutinee_type with
                | Error e -> Error e
                | Ok pattern_env ->
                    begin match check_exp pattern_env exp with
                    | Error e -> Error e
                    | Ok exp_type -> check_cases (exp_type :: acc) rest
                    end
                end
          in
          begin match check_cases [] cases with
          | Error e -> Error e
          | Ok case_types ->
              begin match case_types with
              | [] -> Error (Other ("Empty match expression", pos))
              | first_type :: rest_types ->
                  let all_same = List.for_all (types_equal first_type) rest_types in
                  if all_same then
                    Ok first_type
                  else
                    Error (Other ("Match branches have different types", pos))
              end
          end
      end
      
  | ConstructorExp (name, args, pos) ->
      begin match find_constructor name env with
      | None -> Error (UnboundConstructor (name, pos))
      | Some ctor ->
          let rec check_args acc expected_types actual_args =
            match expected_types, actual_args with
            | [], [] -> Ok (List.rev acc)
            | [], _ -> Error (ArityMismatch (List.length ctor.arg_types, List.length args, pos))
            | _, [] -> Error (ArityMismatch (List.length ctor.arg_types, List.length args, pos))
            | expected_type :: rest_expected, actual_arg :: rest_actual ->
                begin match check_exp env actual_arg with
                | Error e -> Error e
                | Ok actual_type ->
                    if types_equal expected_type actual_type then
                      check_args (actual_type :: acc) rest_expected rest_actual
                    else
                      Error (TypeMismatch (expected_type, actual_type, pos))
                end
          in
          begin match check_args [] ctor.arg_types args with
          | Error e -> Error e
          | Ok _ -> Ok ctor.return_type
          end
      end
      
  | LambdaExp (params, body, pos) ->
      let rec validate_params acc = function
        | [] -> Ok (List.rev acc)
        | param :: rest ->
            begin match validate_type env param.ty with
            | Ok validated_ty -> validate_params ((param.name, validated_ty) :: acc) rest
            | Error e -> Error e
            end
      in
      begin match validate_params [] params with
      | Error e -> Error e
      | Ok param_types ->
          let lambda_env = List.fold_left (fun env (name, ty) -> add_val name ty env) env param_types in
          begin match check_exp lambda_env body with
          | Error e -> Error e
          | Ok body_type ->
              let lambda_type = List.fold_right (fun param acc_type -> 
                FunTy (param.ty, acc_type, pos)
              ) params body_type in
              Ok lambda_type
          end
      end

and check_pattern env pattern expected_type =
  match pattern with
  | WildcardPat _ -> Ok env
  | VarPat (name, _) -> Ok (add_val name expected_type env)
  | LiteralPat (lit, pos) ->
      let literal_type = get_literal_type lit in
      if types_equal literal_type expected_type then
        Ok env
      else
        Error (InvalidPattern (pattern, expected_type, pos))
  | ConstructorPat (name, patterns, pos) ->
      begin match find_constructor name env with
      | None -> Error (UnboundConstructor (name, pos))
      | Some ctor ->
          if not (types_equal ctor.return_type expected_type) then
            Error (TypeMismatch (expected_type, ctor.return_type, pos))
          else if List.length patterns <> List.length ctor.arg_types then
            Error (ArityMismatch (List.length ctor.arg_types, List.length patterns, pos))
          else
            let rec check_patterns acc expected_types actual_patterns =
              match expected_types, actual_patterns with
              | [], [] -> Ok acc
              | expected_type :: rest_expected, actual_pattern :: rest_patterns ->
                  begin match check_pattern acc actual_pattern expected_type with
                  | Error e -> Error e
                  | Ok updated_env -> check_patterns updated_env rest_expected rest_patterns
                  end
              | _ -> Error (ArityMismatch (List.length ctor.arg_types, List.length patterns, pos))
            in
            check_patterns env ctor.arg_types patterns
      end

let check_dec env dec =
  match dec with
  | LetDec { name; ty; value; pos } ->
      begin match check_exp env value with
      | Error e -> Error e
      | Ok value_type ->
          begin match ty with
          | None -> Ok (add_val name value_type env, value_type)
          | Some declared_ty ->
              begin match validate_type env declared_ty with
              | Error e -> Error e
              | Ok validated_ty ->
                  if types_equal value_type validated_ty then
                    Ok (add_val name validated_ty env, validated_ty)
                  else
                    Error (TypeMismatch (validated_ty, value_type, pos))
              end
          end
      end
      
  | FunDec { name; params; return_ty; body; specs; pos } ->
      let rec validate_params acc = function
        | [] -> Ok (List.rev acc)
        | param :: rest ->
            begin match validate_type env param.ty with
            | Ok validated_ty -> validate_params ((param.name, validated_ty) :: acc) rest
            | Error e -> Error e
            end
      in
      begin match validate_params [] params with
      | Error e -> Error e
      | Ok param_types ->
          let func_env = List.fold_left (fun env (name, ty) -> add_val name ty env) env param_types in
          begin match check_exp func_env body with
          | Error e -> Error e
          | Ok body_type ->
              begin match return_ty with
              | None -> 
                  let fun_info = { name; params; return_type = Some body_type; body; specs } in
                  let fun_type = List.fold_right (fun param acc_type -> 
                    FunTy (param.ty, acc_type, pos)
                  ) params body_type in
                  Ok (add_fun name fun_info (add_val name fun_type env), fun_type)
              | Some declared_ty ->
                  begin match validate_type env declared_ty with
                  | Error e -> Error e
                  | Ok validated_ty ->
                      if types_equal body_type validated_ty then
                        let fun_info = { name; params; return_type = Some validated_ty; body; specs } in
                        let fun_type = List.fold_right (fun param acc_type -> 
                          FunTy (param.ty, acc_type, pos)
                        ) params validated_ty in
                        Ok (add_fun name fun_info (add_val name fun_type env), fun_type)
                      else
                        Error (TypeMismatch (validated_ty, body_type, pos))
                  end
              end
          end
      end
      
  | TypeDec { name; type_params; definition; pos } ->
      let param_env = List.fold_left (fun env param -> add_type_param param env) env type_params in
      (* Add the type name to environment first for recursive references *)
      let recursive_type_info = { name; type_params; constructors = []; alias = None } in
      let recursive_env = add_type name recursive_type_info param_env in
      begin match definition with
      | VariantDef variants ->
          let rec validate_variants acc = function
            | [] -> Ok (List.rev acc)
            | variant :: rest ->
                let rec validate_args acc_args = function
                  | [] -> Ok (List.rev acc_args)
                  | arg_type :: rest_args ->
                      begin match validate_type recursive_env arg_type with
                      | Ok validated_ty -> validate_args (validated_ty :: acc_args) rest_args
                      | Error e -> Error e
                      end
                in
                begin match validate_args [] variant.args with
                | Error e -> Error e
                | Ok validated_arg_types ->
                    let return_type = 
                      if type_params = [] then
                        NameTy (name, pos)
                      else
                        GenericTy (name, List.map (fun p -> NameTy (p, pos)) type_params, pos)
                    in
                    let ctor_info = {
                      name = variant.name;
                      arg_types = validated_arg_types;
                      return_type;
                    } in
                    validate_variants (ctor_info :: acc) rest
                end
          in
          begin match validate_variants [] variants with
          | Error e -> Error e
          | Ok constructors ->
              let type_info = { name; type_params; constructors; alias = None } in
              Ok (add_type name type_info env, NameTy (name, pos))
          end
      | AliasDef aliased_type ->
          begin match validate_type recursive_env aliased_type with
          | Error e -> Error e
          | Ok validated_alias ->
              let type_info = { name; type_params; constructors = []; alias = Some validated_alias } in
              Ok (add_type name type_info env, NameTy (name, pos))
          end
      end

let rec check_all env program =
  match program with
  | [] -> Ok env
  | dec :: decs ->
      begin match check_dec env dec with
      | Error e -> Error e
      | Ok (updated_env, _) -> check_all updated_env decs
      end
