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
     F.printf "@[\n\nParse error: \"%s\"@." (Lexing.lexeme lexbuf);
     exit 0
  | ParseError mes ->
     doIfDebug "LEXING" (F.printf "@[%s@.") !tokenMemo;
     F.printf "@[\n\nParse error: %s@." mes;
     exit 0
  | _ ->
     doIfDebug "LEXING" (F.printf "@[%s@.") !tokenMemo;
     F.printf "@[\n\nUnknown Parse error: \"%s\"@." (Lexing.lexeme lexbuf);
     exit 0
           
(* envのT(s)を具体的なtypeに直す *)
let rec arrange_env (env:Program.env) (solutions:Program.tequals) (fenv:Program.env) :Program.env =
  match env with
  |(s,t,v)::env1 -> arrange_env env1 solutions ((s,(find_type_solutions t solutions),v)::fenv)
  |[] -> fenv

and find_type_solutions (t:Program.t) (solutions:Program.tequals) :Program.t =
  match find_type_solutions2 t solutions with
  |t2 ->
    begin
      match t2 with
      |List (T s2) -> List (find_type_solutions (find_type_solutions2 (T s2) solutions) solutions)
      |Tuple (tlist) -> Tuple(tuple_fts tlist solutions)
      |_ -> t2
    end

and find_type_solutions2 (t:Program.t) (solutions:Program.tequals) :Program.t =
  match solutions with
  |(t1,t2)::solutions1 ->
    begin
      match t1,t with
      |T s1,T s2 -> if String.equal s1 s2 then t2 else find_type_solutions2 t solutions1
      |T s1,_ -> t
      |_ -> raise Error
    end
  |[] -> raise Error

and tuple_fts (tlist:Program.t list) (solutions:Program.tequals) :Program.t list =
  List.map (fun t1 -> find_type_solutions t1 solutions) tlist

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

let rec main_tval (ee: Program.e list) (env:Program.env) (tenv:Program.tenv) =
  match ee with
  |[] -> tenv
  |e::ee1 ->
    begin
      match expr_tval e env tenv [] 0 with
      |(env1,tenv1,tequals,n) -> print_tequals tequals;
        begin
          match unif tequals [] with
          |Some solutions ->
            (* print_tequals solutions; *)
            main_tval ee1 (arrange_env env1 solutions []) tenv1
          |None -> raise TypeError
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
    match main_tval ee [] [] with
    |tenv -> main_eval ee [] tenv
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
  | TypeError -> F.printf "raise type error done"
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
  | _ -> print_endline "Exception: Eval error"; exit 0
