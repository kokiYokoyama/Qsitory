open Syntax
open Tools
open Evaluation
module F = Format
module P = Pprint

(* read from file *)
let inputstr_file filename =
  let x = ref "" in
  let ic = open_in filename in
  try
	while true do
	  x := !x ^ (input_line ic) ^ "\n"
	done ;
	"" (* dummy *)
  with
  | End_of_file -> close_in ic;!x
  | _ -> print_endline "Exception: No File..."; exit 0

(* parser *)
let parse str =
  let cache =
    let l = ref [] in
    fun lexbuf -> match !l with
                  | x::xs -> l := xs; x
                  | [] -> match Lexer.tokens lexbuf with
                          | [] -> print_endline "\nFAIL\n"; failwith ""
                          | x::xs -> l := xs; x
  in
  let lexbuf = Lexing.from_string str in
  Lexer.inIndent := Lexer.nextCharIs [' ';'\t'] lexbuf;
  try
    doIfDebug "LEXING" print_endline ">> Lexed Result";
    Parser.main cache lexbuf
  with
  | Parsing.Parse_error ->
      F.printf "@[\n\nParse error: \"%s\"@." (Lexing.lexeme lexbuf);
      exit 0
  | ParseError mes ->
     F.printf "@[\n\nParse error: %s@." mes;
     exit 0
  | _ ->
     F.printf "@[\n\nUnknown Parse error: \"%s\"@." (Lexing.lexeme lexbuf);
     exit 0

let rec main_eval (ee: Program.e list) (env:Program.env) (tenv:Program.tenv) =
  match ee with
  |[] -> Format.printf "finish"
  |e::[] -> print_evalResult (expr_eval e env tenv)  
  |e::ee1 ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) ->
        begin
          match print_evalResult (v1,env1,tenv1) with
          |_ -> main_eval ee1 env1 tenv1
        end
    end
    
let interpreter filename =
  F.printf "@[*****************************@.";
  F.printf "@[Qsitory interpreter@.";
  doIfDebug "LEXING" F.printf "@[- Lexing debug mode: ON@.";
  doIfDebug "PARSING" F.printf "@[- Parsing debug mode: ON@.";  
  F.printf "@[*****************************\n@.";
  try
    let str = inputstr_file filename in (* filename の中身を読む *)
    let ee = parse str in (* 読んだ中身を構文解析して結果を e とする *)
    doIfDebug "PARSING" print_endline ">> Parsed Result (internal data)";
    doIfDebug "PARSING" (F.printf "@[%a\n@." (pp_list "" "\n" (fun _ -> print_expr))) ee; (* expr 型 e を表示する *)
    main_eval ee [] []          
            
        
    (*
    match (Syntax.tval e [] [] 0) with
    |(tequals,tn) -> Syntax.unif tequals [];
                     print_newline ();
                     print_endline "result:";               
                     Value.println (Syntax.eval e []);
                     print_newline ();
     *)
  with
(*    
  | AddTypeError -> print_endline "can only int+int"; exit 0
  | SubTypeError -> print_endline "can only int-int"; exit 0
  | MulTypeError -> print_endline "can only int*int"; exit 0
  | LtTypeError -> print_endline "can only int<int"; exit 0
  | BoolTypeError -> print_endline "conditionsExpression not return bool"; exit 0
  | NotFunClosError -> print_endline "can't found FunClos"; exit 0
  | NotDfunError -> print_endline "can't found function's definition"; exit 0
  | NoMatchPatternError -> print_endline "can't found Match Pattern"; exit 0
  | NotMatchExpressionError -> print_endline "this expression not MatchExp"; exit 0
  | UnifFail -> print_endline "fail unif program"; exit 0
 *)
  | _ -> print_endline "Exception: Eval error"; exit 0
