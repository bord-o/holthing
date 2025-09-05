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
    let ast = parse_file Sys.argv.(1) in
    Printf.printf "Running type checker...\n";
    match Semant.check_all Semant.default_env ast with
    | Ok env ->
        Printf.printf "Type checking successful!\n";
        Printf.printf
          "Final environment has %d values, %d functions, %d types\n"
          (List.length env.vals) (List.length env.funs) (List.length env.types);
        (* let hol = Proof.hol_of_def (snd (List.hd env.funs)) in *)
        (* print_endline hol *)
        Proof.hol_of_env env
    | Error error ->
        Printf.eprintf "Type checking failed: %s\n"
          (Format.asprintf "%a" Semant.pp_type_error error);
        exit 1
