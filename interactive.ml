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
    Some (Parser.main cache lexbuf)
  with
  | _ -> None (* Parse error *)
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
(b2) 最初の1文字がスペースかタブ --> 続行．input に追記．(b) に戻る
(b3) それ以外 --> fail．(a) に戻る
*)
exception GotoNextA
exception GotoNextB

type scanner =
  {
    mutable freshLine: bool; (* true: ##, false: >> *)
    mutable readFinish: bool;
    mutable input: string;
    mutable line: string;
    (* env と tenv はここに入れる *)
  }
;;
let sc: scanner = { freshLine = true; readFinish = false; input = ""; line = "" }
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
let checkSpecial () =
  try
    let (_,exec) = list_assoc3 sc.line !special in
    exec ();
    raise GotoNextA
  with
  | Not_found -> ()
;;

let interpreter () =
  F.printf "@[*****************************@.";
  F.printf "@[Interactive Qsitory interpreter@.";
  doIfDebug "LEXING" F.printf "@[- Lexing debug mode: ON@.";
  doIfDebug "PARSING" F.printf "@[- Parsing debug mode: ON@.";  
  F.printf "@[*****************************\n@.";
  let showPrompt () = F.printf "@[%s @?" (if sc.freshLine then "##" else ">>") in
  let showFail () = F.printf "@[Unexpected input (illegal indent)@?" in
  let parse_then_EvalAndGotoNextA str =
    match parse_opt str with
    | Some ee ->
       F.printf "@[%a@." (pp_list "" "\n" P.pp_expr) ee;
       (* eval *)
       (* env と tenv を更新して表示 *)
       resetScanner(); 
       raise GotoNextA
       
    | None -> ()       
  in
  while true do
    try
      (* (a) *)
      showPrompt ();
      sc.line <- read_line ();
      (* (a1) *)
      if sc.line = "" then raise GotoNextA else ();
      (* (a2) *)
      if List.mem (String.get sc.line 0) [' ';'\t'] then (showFail(); raise GotoNextA) else ();
      checkSpecial ();
      parse_then_EvalAndGotoNextA sc.line;
      (* (b) *)
      sc.freshLine <- false;
      while not (sc.readFinish) do
        try
          showPrompt ();
          sc.line <- read_line ();
          (* (b1) *)
          if sc.line = "" then parse_then_EvalAndGotoNextA sc.input else (showFail(); raise GotoNextA);
          (* (b2) *)
          if List.mem (String.get sc.line 0) [' ';'\t'] then (sc.input <- sc.input ^ sc.line; raise GotoNextB) else ();
          (* (b3) *)
          showFail(); raise GotoNextA
        with
        | GotoNextB -> ()
      done
    with
    | GotoNextA -> resetScanner ()
  done
;;
