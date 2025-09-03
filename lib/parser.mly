%{
	open Absyn

%}

%token EOF
%token <string> ID
%token <int> INT
%token <string> STRING
%token <string> HOL_TERM
%token LET IN DEF TYPE MATCH IF THEN ELSE TRUE FALSE
%token REQUIRES ENSURES MUST HAVE PROVE MEASURE
%token COMMA COLON SEMICOLON LPAREN RPAREN LBRACK RBRACK
%token LBRACE RBRACE DOT ARROW DARROW BAR UNDERSCORE
%token PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE AND OR
%token ASSIGN

%type <program> program
%type <dec> declaration
%type <dec list> declaration_list
%type <exp> expression
%type <ty> type_expr
%type <pattern> pattern
%type <proof_spec> proof_spec
%type <proof_spec list> proof_spec_list
%type <param> parameter
%type <param list> parameter_list
%type <variant> variant
%type <variant list> variant_list
%type <literal> literal

%right ASSIGN
%left OR
%left AND
%nonassoc EQ NEQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIVIDE
%nonassoc UMINUS

%start <program> main

%%

main:
  | program EOF { $1 }

program:
  | declaration_list { List.rev $1 }

declaration_list:
  | declaration { [$1] }
  | declaration_list declaration { $2 :: $1 }

declaration:
  | LET ID ASSIGN expression {
      LetDec { name = $2; ty = None; value = $4; pos = $startpos }
    }
  | LET ID COLON type_expr ASSIGN expression {
      LetDec { name = $2; ty = Some $4; value = $6; pos = $startpos }
    }
  | DEF ID LPAREN parameter_list RPAREN LBRACE expression RBRACE proof_spec_list {
      FunDec { name = $2; params = $4; return_ty = None; body = $7; specs = $9; pos = $startpos }
    }
  | DEF ID LPAREN parameter_list RPAREN ARROW type_expr LBRACE expression RBRACE proof_spec_list {
      FunDec { name = $2; params = $4; return_ty = Some $7; body = $9; specs = $11; pos = $startpos }
    }
  | TYPE ID ASSIGN variant_list {
      TypeDec { name = $2; type_params = []; definition = VariantDef $4; pos = $startpos }
    }
  | TYPE ID LT ID GT ASSIGN variant_list {
      TypeDec { name = $2; type_params = [$4]; definition = VariantDef $7; pos = $startpos }
    }

expression:
  | ID { VarExp ($1, $startpos) }
  | literal { LiteralExp ($1, $startpos) }
  | expression LPAREN expression_list RPAREN {
      CallExp ($1, $3, $startpos)
    }
  | expression PLUS expression { BinOpExp ($1, Add, $3, $startpos) }
  | expression MINUS expression { BinOpExp ($1, Sub, $3, $startpos) }
  | expression TIMES expression { BinOpExp ($1, Mul, $3, $startpos) }
  | expression DIVIDE expression { BinOpExp ($1, Div, $3, $startpos) }
  | expression EQ expression { BinOpExp ($1, Eq, $3, $startpos) }
  | expression NEQ expression { BinOpExp ($1, Neq, $3, $startpos) }
  | expression LT expression { BinOpExp ($1, Lt, $3, $startpos) }
  | expression LE expression { BinOpExp ($1, Le, $3, $startpos) }
  | expression GT expression { BinOpExp ($1, Gt, $3, $startpos) }
  | expression GE expression { BinOpExp ($1, Ge, $3, $startpos) }
  | expression AND expression { BinOpExp ($1, And, $3, $startpos) }
  | expression OR expression { BinOpExp ($1, Or, $3, $startpos) }
  | MINUS expression %prec UMINUS { UnaryOpExp ("-", $2, $startpos) }
  | IF expression THEN expression ELSE expression {
      IfExp ($2, $4, $6, $startpos)
    }
  | LET ID ASSIGN expression IN expression {
      LetExp ($2, None, $4, $6, $startpos)
    }
  | LET ID COLON type_expr ASSIGN expression IN expression {
      LetExp ($2, Some $4, $6, $8, $startpos)
    }
  | LBRACE expression_list RBRACE { BlockExp ($2, $startpos) }
  | MATCH expression LBRACE match_cases RBRACE {
      MatchExp ($2, $4, $startpos)
    }
  | ID LPAREN expression_list RPAREN {
      ConstructorExp ($1, $3, $startpos)
    }
  | LPAREN expression RPAREN { $2 }

expression_list:
  | { [] }
  | expression { [$1] }
  | expression COMMA expression_list { $1 :: $3 }

match_cases:
  | match_case { [$1] }
  | match_case match_cases { $1 :: $2 }

match_case:
  | pattern DARROW expression { ($1, $3) }

pattern:
  | UNDERSCORE { WildcardPat $startpos }
  | ID { VarPat ($1, $startpos) }
  | literal { LiteralPat ($1, $startpos) }
  | ID LPAREN pattern_list RPAREN {
      ConstructorPat ($1, $3, $startpos)
    }

pattern_list:
  | { [] }
  | pattern { [$1] }
  | pattern COMMA pattern_list { $1 :: $3 }

literal:
  | INT { IntLit $1 }
  | TRUE { BoolLit true }
  | FALSE { BoolLit false }
  | STRING { StringLit $1 }
  | LPAREN RPAREN { UnitLit }

type_expr:
  | ID { NameTy ($1, $startpos) }
  | ID LT type_list GT { GenericTy ($1, $3, $startpos) }
  | type_expr ARROW type_expr { FunTy ($1, $3, $startpos) }
  | LPAREN type_expr RPAREN { $2 }

type_list:
  | type_expr { [$1] }
  | type_expr COMMA type_list { $1 :: $3 }

parameter_list:
  | { [] }
  | parameter { [$1] }
  | parameter COMMA parameter_list { $1 :: $3 }

parameter:
  | ID COLON type_expr { { name = $1; ty = $3; pos = $startpos } }

variant_list:
  | variant { [$1] }
  | variant BAR variant_list { $1 :: $3 }

variant:
  | ID { { name = $1; args = []; pos = $startpos } }
  | ID LPAREN type_list RPAREN { { name = $1; args = $3; pos = $startpos } }

proof_spec_list:
  | { [] }
  | proof_spec proof_spec_list { $1 :: $2 }

proof_spec:
  | REQUIRES HOL_TERM { Requires ($2, $startpos) }
  | ENSURES HOL_TERM { Ensures ($2, $startpos) }
  | MUST HOL_TERM { Must ($2, $startpos) }
  | HAVE HOL_TERM { Have ($2, $startpos) }
  | PROVE HOL_TERM { Prove ($2, $startpos) }
  | MEASURE HOL_TERM { Measure ($2, $startpos) }