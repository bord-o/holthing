{
  open Parser
  open Lexing

  exception Error of string
  let debug = false
  let pp = if debug then print_endline else (fun _ -> ())

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                pos_lnum = pos.pos_lnum + 1}
}

let digit = ['0'-'9']
let digits = digit+
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper
let ws = [' ' '\t']
let nl = "\r\n" | '\n' | '\r'

rule token = parse
| ws+
    { token lexbuf }

| nl
    { next_line lexbuf; token lexbuf }

| "//" [^ '\n']*
    { token lexbuf }

| "/*"
    { comment lexbuf }

| "let"
    { pp "LET"; LET }
| "in"
    { pp "IN"; IN }
| "def"
    { pp "DEF"; DEF }
| "type"
    { pp "TYPE"; TYPE }
| "match"
    { pp "MATCH"; MATCH }
| "if"
    { pp "IF"; IF }
| "then"
    { pp "THEN"; THEN }
| "else"
    { pp "ELSE"; ELSE }
| "true"
    { pp "TRUE"; TRUE }
| "false"
    { pp "FALSE"; FALSE }
| "requires"
    { pp "REQUIRES"; REQUIRES }
| "ensures"
    { pp "ENSURES"; ENSURES }
| "must"
    { pp "MUST"; MUST }
| "have"
    { pp "HAVE"; HAVE }
| "prove"
    { pp "PROVE"; PROVE }
| "measure"
    { pp "MEASURE"; MEASURE }

| lower (alpha | digit | "_")* as id
    { pp ("ID: " ^ id); ID id }
| upper (alpha | digit | "_")* as id
    { pp ("CONSTRUCTOR: " ^ id); CONSTRUCTOR id }

| digits as num
    { pp ("INT: " ^ num); INT (int_of_string num) }

| '"'
    { read_string (Buffer.create 64) lexbuf }

| '`'
    { read_hol_term (Buffer.create 64) lexbuf }

| "=="
    { pp "EQ"; EQ }
| "!="
    { pp "NEQ"; NEQ }
| "<="
    { pp "LE"; LE }
| ">="
    { pp "GE"; GE }
| "<"
    { pp "LT"; LT }
| ">"
    { pp "GT"; GT }
| "&&"
    { pp "AND"; AND }
| "||"
    { pp "OR"; OR }

| "+"
    { pp "PLUS"; PLUS }
| "-"
    { pp "MINUS"; MINUS }
| "*"
    { pp "TIMES"; TIMES }
| "/"
    { pp "DIVIDE"; DIVIDE }

| "="
    { pp "ASSIGN"; ASSIGN }
| ":"
    { pp "COLON"; COLON }
| ","
    { pp "COMMA"; COMMA }
| ";"
    { pp "SEMICOLON"; SEMICOLON }
| "."
    { pp "DOT"; DOT }

| "("
    { pp "LPAREN"; LPAREN }
| ")"
    { pp "RPAREN"; RPAREN }
| "{"
    { pp "LBRACE"; LBRACE }
| "}"
    { pp "RBRACE"; RBRACE }
| "["
    { pp "LBRACK"; LBRACK }
| "]"
    { pp "RBRACK"; RBRACK }

| "->"
    { pp "ARROW"; ARROW }
| "=>"
    { pp "DARROW"; DARROW }
| "|"
    { pp "BAR"; BAR }
| "_"
    { pp "UNDERSCORE"; UNDERSCORE }

| eof
    { pp "EOF"; EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character '%s'" 
                   (Lexing.lexeme_start lexbuf) (Lexing.lexeme lexbuf))) }

and read_string buf = parse
  | '"'       { pp ("STRING: " ^ Buffer.contents buf); STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf }
  | _ { raise (Error ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Error ("String is not terminated")) }

and read_hol_term buf = parse
  | '`'       { pp ("HOL_TERM: " ^ Buffer.contents buf); HOL_TERM (Buffer.contents buf) }
  | [^ '`']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_hol_term buf lexbuf }
  | eof { raise (Error ("HOL term is not terminated")) }

and comment = parse
  | "*/"    { token lexbuf }
  | nl      { next_line lexbuf; comment lexbuf }
  | _       { comment lexbuf }