open Syntax
open Tools
module F = Format
module P = Pprint
                
(* parser *)
let parse_opt str =
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
  try
    Lexer.inIndent := Lexer.nextCharIs [' ';'\t'] lexbuf;
    Some (Parser.main cache lexbuf)
  with
  | _ ->
     (* doIfDebug "LEXING" print_newline (); *)
     None (* Parse error *)
;;

(* Interactive Interpreter
Prepare a scanner sc
(a) Scan one input line under the default prompt "##" & record the line to sc.input
(a1) 空文字列 --> 何もせず (a) に戻る
(a2) 最初の1文字がスペースかタブ --> fail．(a) に戻る
(a3) 特殊命令 (:quit など) --> 特殊動作
(a4) それ以外 --> 入力は終了か続行．input をパース
(a4.1) パース成功 --> 終了．eval して結果を表示．(a)に戻る
(a4.2) パース失敗 --> 続行．(b) へ
(b) 続行プロンプト >> で1行読む
(b1) 空文字列 --> 入力終了． input をパース
(b1.1) パース成功 --> eval して結果を表示．(a)に戻る
(b1.2) パース失敗 --> fail．(a) に戻る
(b2) それ以外 --> 続行．input に追記．(b) に戻る
*)
exception GotoNextA
exception GotoNextB

type scanner =
  {
    mutable freshLine: bool; (* true: ##, false: >> *)
    mutable readFinish: bool;
    mutable input: string;
    mutable line: string;
    mutable env: Program.env;
    mutable tenv: Program.tenv;
  }
;;
let sc: scanner = { freshLine = true; readFinish = false; input = ""; line = ""; env = []; tenv = [] }
;;
let resetScanner() =
  sc.freshLine <- true;
  sc.readFinish <- false;
  sc.readFinish <- false;
  sc.input <- "";
  sc.line <- ""
;;
let special: (string * string * (unit->unit)) list ref = ref []
;;                
let exec_quit(): unit = exit 0
;;
let exec_help(): unit =
  List.iter
    (fun (command,explanation,_) -> F.printf "@[%s\t%s@." command explanation)
    !special
;;
special :=
  [
    (":quit", "Quit", exec_quit);
    (":q", "Quit", exec_quit);
    (":help", "Help", exec_help);
    (":h", "Help", exec_help);
    (":?", "Help", exec_help);
  ]
;;
type linestate = Normal | Empty | Ident | Special of string * (unit->unit)
;;
let analyzeLine str =
  let isIndent = if str = "" then false else List.mem (String.get sc.line 0) [' ';'\t'] in
  match str = "", isIndent, list_assoc3_opt str !special with
  | true,_,_ -> Empty
  | _,true,_ -> Ident
  | _,_,Some(sp,com) -> Special (sp,com)
  | _,_,_ -> Normal
;;
let interpreter () =
  F.printf "@[*****************************@.";
  F.printf "@[Interactive Qsitory interpreter@.";
  doIfDebug "LEXING" F.printf "@[- Lexing debug mode: ON@.";
  doIfDebug "PARSING" F.printf "@[- Parsing debug mode: ON@.";  
  F.printf "@[*****************************\n@.";
  let showPrompt () = F.printf "@[%s @?" (if sc.freshLine then "##" else "..") in
  let showFail mes = F.printf "@[Unexpected Input (%s)@." mes in
  let parse_then_EvalAndGotoNextA str =
    clearMemo ();
    match parse_opt str with
    | Some ee ->
       doIfDebug "LEXING" (F.printf "@[Token: %s@.") !tokenMemo;
       doIfDebug "PARSING" (F.printf "@[Expr: %a@." (pp_list "" "\n" P.pp_expr)) ee;
       F.printf "@[Env : [%a]@." Pprint.pp_env sc.env;
       F.printf "@[TEnv: [%a]@." Pprint.pp_tenv sc.tenv;       
       (* eval *)
       resetScanner(); 
       raise GotoNextA
    | None -> ()       
  in
  while true do
    try
      (* (a) *)
      showPrompt ();
      sc.line <- F.sprintf "%s" (read_line ()) ;
      match analyzeLine sc.line with
      | Empty -> raise GotoNextA (* (a1) *)
      | Ident -> showFail "Illegal Indent"; raise GotoNextA (* (a2) *)
      | Special(_,command) -> command () (* (a3) *)
      | Normal -> (* (a4) *)
         sc.input <- F.sprintf "%s" sc.line;
         parse_then_EvalAndGotoNextA sc.input;
         (* (b) *)
         sc.freshLine <- false;
         while not (sc.readFinish) do
           try
             showPrompt ();
             sc.line <- F.sprintf "%s" (read_line ()) ;
             match analyzeLine sc.line with
             | Special(_,command) -> command ()               
             | Empty -> (* (b1) *)
                sc.input <- sc.input ^ "\n";
                F.printf "@[Input: %S@." sc.input;
                parse_then_EvalAndGotoNextA sc.input;
                doIfDebug "LEXING" (F.printf "@[Token: %s@.") !tokenMemo;
                showFail "Parsing Failure";
                raise GotoNextA 
             | _ -> (* (b2) *)
                sc.input <- F.sprintf "%s\n%s" sc.input sc.line;
                raise GotoNextB 
           with
           | GotoNextB -> ()
         done
    with
    | GotoNextA ->       
       resetScanner ()
  done
;;
