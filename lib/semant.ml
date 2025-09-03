open Absyn

(* TODO: make this better *)
type env = {
  vals : (string * ty option) list;
  funs : (string * param list * ty option) list;
  types : (string * string list) list;
}

let check_exp (exp : exp) env =
    match exp with
    | VarExp (_, _) ->
		(*
            lookup the var and error if it isn't in env
		*)
		env 
    | LiteralExp (_, _) ->
		(*
            evaluate to its type
		*)
		env 
    | CallExp (_, _, _) ->
		(*
            check all args and evaluate to its return types
		*)
		env 
    | BinOpExp (_, _, _, _) ->
		(*
            evaluate to its type
		*)
		env 
    | UnaryOpExp (_, _, _) ->
		(*
            evaluate to its type
		*)
		env 
    | IfExp (_, _, _, _) ->
		(*
            check the first branch to be boolean, check that branch types match
		*)
		env 
    | LetExp (_, _, _, _, _) ->
		(*
            evaluate to bound type and add to env
		*)
		env 
    | BlockExp (_, _) ->
		(*
            evaluate to last type, env updates throughout the nested expressions
		*)
		env 
    | MatchExp (_, _, _) ->
		(*
            Ensure all patterns are properly typed
		*)
		env 
    | ConstructorExp (_, _, _) ->
		(*
            ensure that param type is correct and evaluate to Constructor type
		*)
		env 


let check_dec (dec : dec) env =
  match dec with
  | LetDec { name; ty; value=_; pos=_ } ->
      (*
            Type-check
           *)
      { env with vals = (name, ty) :: env.vals }
  | FunDec { name; params; return_ty; body=_; specs=_; pos=_ } ->
      (* 
             Type-check
             For any specs [REQUIRE SHOW] 
                Add them to our proof state
             Look inside the body
                for any function calls:
                    Lookup the function in the env
                        Instantiate the functions REQUIRES with the arguments in the function call
                            These might require calculation of a precondition on the current function in order to satisfy
                            If we can't figure that out, quantify over them generically
                        Add the instantiated term as a MUST
                        Instantiate the functions SHOWS with the binding of the function call
                        Add the instantiated term as a HAVE 
           *)
      { env with funs = (name, params, return_ty) :: env.funs }
  | TypeDec { name; type_params; definition=_; pos=_ } ->
      (*
            Type-check
           *)
      { env with types = (name, type_params) :: env.types }

let rec check_all (p : program) (env : env) =
  match p with
  | [] -> env
  | d :: decs ->
      let updated = check_dec d env in
      check_all decs updated
