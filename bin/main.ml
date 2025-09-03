open Holthing
open Lexing

let parse_file filename =
  let ic = open_in filename in
  let lexbuf = from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  try
    let ast = Parser.main Lexer.token lexbuf in
    close_in ic;
    Printf.printf "Parse successful!\n%s\n" (Absyn.show_program ast);
    ast
  with
  | Parser.Error ->
      close_in ic;
      let pos = lexbuf.lex_curr_p in
      Printf.eprintf "Parse error at line %d, column %d\n" pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol);
      exit 1
  | Lexer.Error msg ->
      close_in ic;
      Printf.eprintf "Lexer error: %s\n" msg;
      exit 1

let () =
  if Array.length Sys.argv < 2 then
    Printf.eprintf "Usage: %s <filename>\n" Sys.argv.(0)
  else
    let _ = parse_file Sys.argv.(1) in
    ()
