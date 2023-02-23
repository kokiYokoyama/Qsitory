open Syntax
open Tools
open Evaluation
module F = Format
module P = Pprint

exception TypeError

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
    fun lexbuf ->
    match !l with
    | x::xs -> l := xs; x
    | [] ->
       match Lexer.tokens lexbuf with
       | [] -> failwith ""
       | x::xs -> l := xs; x
  in
  let lexbuf = Lexing.from_string str in
  Lexer.inIndent := Lexer.nextCharIs [' ';'\t'] lexbuf;
  try
    doIfDebug "LEXING" print_endline ">> Input";
    doIfDebug "LEXING" (F.printf "@[%S@.") str;
    
    doIfDebug "LEXING" print_endline ">> Lexed Result";
    clearMemo ();
    let e = Parser.main cache lexbuf in
    doIfDebug "LEXING" (F.printf "@[%s@.") !tokenMemo;
    e
  with
  | Parsing.Parse_error ->
     doIfDebug "LEXING" (F.printf "@[%s@.") !tokenMemo;
     F.printf "@[\n\nParse error: %S@." (Lexing.lexeme lexbuf);
     exit 0
  | ParseError mes ->
     doIfDebug "LEXING" (F.printf "@[%s@.") !tokenMemo;
     F.printf "@[\n\nParse error: %S@." mes;
     exit 0
  | _ ->
     doIfDebug "LEXING" (F.printf "@[%s@.") !tokenMemo;
     F.printf "@[\n\nUnknown Parse error: %S@." (Lexing.lexeme lexbuf);
     exit 0

let rec main_interpreter (ee: Program.e list) (env:Program.env) (tenv:Program.tenv) =
  match ee with
  |[] -> Format.printf "finish"
  |e::ee1 ->
    Format.printf "@[式\n%a\n@." P.pp_expr e;
    let (tequals,n) = expr_tval e [env] tenv [] 0 in
    Format.printf "@[制約リスト\n%a\n@." P.pp_tequals tequals;
    begin
      match unif tequals [] with
      |Some solutions ->
        Format.printf "@[単一化後\n%a\n@." P.pp_tequals solutions;
        let (env1,tenv1) = arrange_EnvAndTenv e solutions env tenv in
        Format.printf "@[環境情報整理\n[%a]\n@." P.pp_env env1;
        Format.printf "@[型環境情報整理\n[%a]\n@." P.pp_tenv tenv1;
        
        let (v,env2,tenv2) = expr_eval e env1 tenv1 in
        Format.printf "@[評価後\n%a\n" (fun _ -> print_evalResult) (v,env2,tenv2);
        (* Format.printf "@[ローカル環境数\n%i\n@." (List.length env2); *)
        begin
          match ee1 with
          |[] -> print_evalResult (v,env2,tenv2)
          |_ -> main_interpreter ee1 env2 tenv2
        end
      |None -> raise TypeError
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
    main_interpreter ee [] []
    (* match main_tval ee [] [] with
     * |tenv -> main_eval ee [] tenv *)
    (* main_eval ee [] [] *)
    (* print_env (main_tval ee [] []) *)
    
        
    (*
    match (Syntax.tval e [] [] 0) with
    |(tequals,tn) -> Syntax.unif tequals [];
                     print_newline ();
                     print_endline "result:";               
                     Value.println (Syntax.eval e []);
                     print_newline ();
     *)
  with
  | TypeError -> F.printf "@[raise type error done@."
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
  |Error1 -> print_endline "Exception: Error1"; exit 0
  |Error2 -> print_endline "Exception: Error2"; exit 0
  |Error3 -> print_endline "Exception: Error3"; exit 0
  |Error4 -> print_endline "Exception: Error4"; exit 0
  |Error5 -> print_endline "Exception: Error5"; exit 0
  |Error6 -> print_endline "Exception: Error6"; exit 0
  (* |NoValueError -> print_endline "Exception: NoValueError"; exit 0 *)
  |OperateTypeError -> print_endline "Exception: OperateTypeError"; exit 0
  | _ -> print_endline "Exception: Eval error"; exit 0
;;


                                                  
