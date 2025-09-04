type pos = Lexing.position
type symbol = string [@@deriving show]

let pp_pos fmt (p : pos) =
  let column = p.pos_cnum - p.pos_bol in
  Format.fprintf fmt "line:%i column:%i" p.pos_lnum column

let show_pos p = Format.asprintf "%a" pp_pos p

type binop = Add | Sub | Mul | Div | Eq | Neq | Lt | Le | Gt | Ge | And | Or
[@@deriving show]

type hol_term = string [@@deriving show]

type ty =
  | NameTy of symbol * pos
  | GenericTy of symbol * ty list * pos
  | FunTy of ty * ty * pos
[@@deriving show]

and type_def = VariantDef of variant list | AliasDef of ty [@@deriving show]
and variant = { name : symbol; args : ty list; pos : pos } [@@deriving show]

type pattern =
  | WildcardPat of pos
  | VarPat of symbol * pos
  | LiteralPat of literal * pos
  | ConstructorPat of symbol * pattern list * pos
[@@deriving show]

and literal = IntLit of int | BoolLit of bool | StringLit of string | UnitLit
[@@deriving show]

type proof_spec =
  | Requires of hol_term * pos
  | Ensures of hol_term * pos
  | Must of hol_term * pos
  | Have of hol_term * pos
  | Prove of hol_term * pos
  | Measure of hol_term * pos
[@@deriving show]

type param = { name : symbol; ty : ty; pos : pos } [@@deriving show]

and exp =
  | VarExp of symbol * pos
  | LiteralExp of literal * pos
  | CallExp of exp * exp list * pos
  | BinOpExp of exp * binop * exp * pos
  | UnaryOpExp of symbol * exp * pos
  | IfExp of exp * exp * exp * pos
  | LetExp of symbol * ty option * exp * exp * pos
  | BlockExp of exp list * pos
  | MatchExp of exp * (pattern * exp) list * pos
  | ConstructorExp of symbol * exp list * pos
  | LambdaExp of param list * exp * pos
[@@deriving show]

type dec =
  | LetDec of { name : symbol; ty : ty option; value : exp; pos : pos }
  | FunDec of {
      name : symbol;
      params : param list;
      return_ty : ty option;
      body : exp;
      specs : proof_spec list;
      pos : pos;
    }
  | TypeDec of {
      name : symbol;
      type_params : symbol list;
      definition : type_def;
      pos : pos;
    }
[@@deriving show]

type program = dec list [@@deriving show]
