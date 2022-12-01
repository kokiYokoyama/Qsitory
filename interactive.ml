open Syntax
open Tools
module F = Format
module P = Pprint

       
         
(* parser *)
let parse_oneline str =
  let cache =
    let l = ref [] in
    fun lexbuf -> match !l with
                  | x::xs -> l := xs; x
                  | [] -> match Lexer.tokens lexbuf with
                          | [] -> failwith ""
                          | x::xs -> l := xs; x
  in
  let lexbuf = Lexing.from_string str in
  try
    (*
    Parser.oneline_expression Lexer.token lexbuf
     *)
    Parser.main cache lexbuf
  with
  |  Parsing.Parse_error ->
      F.printf "@[Parse error: %s@." (Lexing.lexeme lexbuf);
      exit 0
  | _ ->
     F.printf "@[Unknown Parse error@.";
     exit 0

let interpreter () =
  F.printf "@[*****************************@.";
  F.printf "@[Interactive Qsitory interpreter@.";
  doIfDebug "LEXING" F.printf "@[- Lexing debug mode: ON@.";
  F.printf "@[*****************************\n@.";  
  let accepting = ref true in
  let line = ref "" in
  let isFreshLine = ref true in
  let prompt () = if !isFreshLine then "##" else ".." in
  while !accepting do
    F.printf "@[%s @?" (prompt ());
    let ln = read_line () in
    if ln = ""
    then
       (accepting := false;
       F.printf "@[%s@." !line)
    else
      (try
         (*         
         let _ = parse_oneline ln in
         match parse_oneline !line with
         | Prog e ->
            F.printf "@[%a@." P.pp_expr e;
            isFreshLine := true
         | ProgHead hd ->
            let _ = hd in            
            isFreshLine := false;
            ()
          *)
         ()
       with
         _ -> isFreshLine := false
      )
  done
