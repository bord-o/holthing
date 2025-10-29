open Semant

(* let generate (env : env) =  *)
(*     let gen_obligations fun_def =  *)
(*         fun_def.body *)
(*     in *)
(*     let updated = List.map gen_obligations env.funs in *)
(*     { env with funs=updated} *)

type hol_state = string list [@@deriving show]

let sanitize_hol_name s = s

let rec intersperse sep ls =
  match ls with [] | [ _ ] -> ls | x :: xs -> x :: sep :: intersperse sep xs

let rec string_of_list = function [] -> "" | x :: xs -> x ^ string_of_list xs

let pattern_hol_def ~(name : string) ~(args : string list) ~(body : string) =
  let term_args = intersperse " " args |> string_of_list in

  Printf.sprintf "let %s_def = define `%s %s = %s`;;" name name term_args body

let pattern_hol_call ~(caller : string) ~(args : string list) =
  let term_args = intersperse " " args |> string_of_list in
  Printf.sprintf "(%s %s)" caller term_args

(*
    Need an complete semantic map into HOL Light's term language
 *)

let hol_of_lit (lit : Absyn.literal) =
  match lit with
  | Absyn.IntLit i -> string_of_int i
  | Absyn.BoolLit b -> string_of_bool b
  | Absyn.StringLit s -> s
  | Absyn.UnitLit -> "one"

let rec hol_of_pat (pat : Absyn.pattern) =
  match pat with
  | Absyn.WildcardPat _ -> "_"
  | Absyn.VarPat (name, _) -> name
  | Absyn.LiteralPat (lit, _) -> hol_of_lit lit
  | Absyn.ConstructorPat (name, pats, _) ->
      let pats_hol = List.map hol_of_pat pats in
      let pat_hol = intersperse " " pats_hol |> string_of_list in
      Printf.sprintf "(%s %s)" name pat_hol

let rec hol_of_exp (body : Absyn.exp) =
  match body with
  | Absyn.VarExp (name, _) -> sanitize_hol_name name
  | Absyn.LiteralExp (lit, _) -> hol_of_lit lit
  | Absyn.CallExp (caller, args, _) ->
      let caller_hol = hol_of_exp caller in
      let args_hol = List.map hol_of_exp args in
      pattern_hol_call ~caller:caller_hol ~args:args_hol
  | Absyn.BinOpExp (left, oper, right, _) -> (
      let left_hol = hol_of_exp left in
      let right_hol = hol_of_exp right in
      let pattern_hol_op o = Printf.sprintf "(%s %s %s)" left_hol o right_hol in
      match oper with
      | Absyn.Add -> pattern_hol_op "+"
      | Absyn.Sub -> pattern_hol_op "-"
      | Absyn.Mul -> pattern_hol_op "*"
      | Absyn.Div -> pattern_hol_op "/"
      | Absyn.Eq -> pattern_hol_op "="
      | Absyn.Neq -> pattern_hol_op "!="
      | Absyn.Lt -> pattern_hol_op "<"
      | Absyn.Le -> pattern_hol_op "<="
      | Absyn.Gt -> pattern_hol_op ">"
      | Absyn.Ge -> pattern_hol_op ">="
      | Absyn.And -> pattern_hol_op {|/\|}
      | Absyn.Or -> pattern_hol_op {|\/|})
  | Absyn.UnaryOpExp (oper, expr, _) ->
      let expr_hol = hol_of_exp expr in
      Printf.sprintf "(%s%s)" oper expr_hol
  | Absyn.IfExp (if', then', else', _) ->
      let if'_hol = hol_of_exp if' in
      let then'_hol = hol_of_exp then' in
      let else'_hol = hol_of_exp else' in
      Printf.sprintf "(if %s then %s else %s)" if'_hol then'_hol else'_hol
  | Absyn.LetExp (name, _, binding, rest, _) ->
      let binding_hol = hol_of_exp binding in
      let rest_hol = hol_of_exp rest in
      Printf.sprintf "(let %s = %s in %s)" name binding_hol rest_hol
  | Absyn.BlockExp (exprs, _) ->
      if List.length exprs <> 1 then failwith "TODO"
      else hol_of_exp (List.hd exprs)
  | Absyn.LambdaExp (params, body, _) ->
      let param_names = List.map (fun (p : Absyn.param) -> p.name) params in
      let params_hol = intersperse " " param_names |> string_of_list in
      let body_hol = hol_of_exp body in
      Printf.sprintf "(\\%s.%s)" params_hol body_hol
  | Absyn.ConstructorExp (name, args, _) ->
      let args_hol = List.map hol_of_exp args  in
      pattern_hol_call ~caller:name ~args:args_hol
  | Absyn.MatchExp (matchee, patterns, _) ->
      let patterns_hol =
        List.map
          (fun (pat, expr) ->
            let pat_hol = hol_of_pat pat in
            let expr_hol = hol_of_exp expr in
            Printf.sprintf "%s -> %s" pat_hol expr_hol)
          patterns
      in
      let pattern_hol = intersperse " | " patterns_hol |> string_of_list in
      let matchee_hol = hol_of_exp matchee in
      Printf.sprintf "(match %s with %s)" matchee_hol pattern_hol

let hol_of_ty (ty : Absyn.ty) =
  match ty with
  | Absyn.NameTy (name, _) -> name
  | Absyn.GenericTy (_, _, _) -> failwith "TODO Generic types to hol"
  | Absyn.FunTy (_, _, _) -> failwith "TODO function types to hol"

let hol_of_def (f_def : fun_info) =
  let hol_name = sanitize_hol_name f_def.name  in
  let args_hol =
    f_def.params |> List.map (fun (p : Absyn.param) -> p.name)
  in
  let hol_body = hol_of_exp f_def.body in
  pattern_hol_def ~name:hol_name ~args:args_hol ~body:hol_body

let hol_of_ty_def (ty_def : type_info) =
    (*
        new_type_abbrev("state", `:string -> num`);;
     *)
  if ty_def.alias |> Option.is_some then failwith "TODO: type abbrev"
  else
    let hol_name = ty_def.name in
    let hol_defs =
      ty_def.constructors
      |> List.map (fun cons ->
             let args = cons.arg_types in
             let args_hol = List.map hol_of_ty args in
             let arg_hol = intersperse " " args_hol |> string_of_list in
             Printf.sprintf "%s %s" cons.name arg_hol)
    in
    let hol_def = intersperse " | " hol_defs |> string_of_list in
    Printf.sprintf {|let %s_INDUCT, %s_RECURSION = define_type "%s = %s";;|} hol_name  hol_name hol_name hol_def

let hol_of_env (env : Semant.env) =
  let hol_defs =
    List.map (fun (_, td) -> hol_of_ty_def td) env.types |> List.rev
  in
  let hol_funs = List.map (fun (_, fd) -> hol_of_def fd) env.funs |> List.rev in
  (List.append hol_defs hol_funs) |> List.iter (Fun.compose print_newline print_endline )
