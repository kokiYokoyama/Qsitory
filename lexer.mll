(*
 Lexer for Qsitory
*)
{
  open Parser
  open Tools
  module F = Format

  exception Issue of token list
                  
  let pp str = doIfDebug "LEXING" print str
             
  (* INDENT と DEDENT トークンの発行
- indent record は各ブロックのインデントレベルの列 ([5;2;0] は 0,2,5 と読み，|__|___| の縦棒の位置がブロック先頭)
- タブストップは8の倍数
- 改行される度に indent mode に入る．(new)indent mode 時は常に現在地を覚えておく．
- (new)indent mode の間は次の文字を先読みする．空白/タブ以外の文字を発見したら normal mode に移行
- normal mode 移行時に現在地と indent record の数値が不整合なら fail．indent record の末尾から N個手前と整合したら N 個の DEDENT トークンを発行
- indent record の最大値を越えたら INDENT トークンを発行して newindent mode に入る
- newindent mode から normal mode への移行時に現在地の数値を indent record の末尾に追加
   *)

  let inIndent = ref true
           
  let record = ref [0]
             
  let pushRecord n = record := n::!record
                   
  let popRecord () = record := List.tl !record
                   
  let pos = ref 0
          
  let inclPos () = pos := !pos + 1
                 
  let jumpPos () =
    let rec aux i = if !pos < i then i else aux (i+8) in
    pos := aux 0
    
  let revertPos lexbuf =
    pos := !pos - 1;
    lexbuf.Lexing.lex_start_pos <- lexbuf.Lexing.lex_start_pos - 1;
    lexbuf.Lexing.lex_curr_pos <- lexbuf.Lexing.lex_curr_pos - 1;
    lexbuf.Lexing.lex_last_pos <- lexbuf.Lexing.lex_last_pos - 1
    
  let getNextChar lexbuf =
    try
      Some (Bytes.get lexbuf.Lexing.lex_buffer lexbuf.Lexing.lex_curr_pos)
    with
      _ -> None

  let nextCharIs cc lexbuf =
    match getNextChar lexbuf with
    | Some c -> List.mem c cc
    | None -> false

  let rec popRecord toks n record =
    match record with
    | m::record1 when n < m -> popRecord (DEDENT::toks) n record1
    | m::_ when n = m -> (toks,record)
    | _ -> failwith ""
                           
  let doNewLine lexbuf =
    pos := 0;
    inIndent := nextCharIs [' ';'\t'] lexbuf;    
    match List.hd !record <> 0 && not !inIndent with
    | false -> pp "NEWLINE "; raise (Issue [NEWLINE])
    | true ->
       let (dedents,_) = popRecord [] 0 !record in
       record := [0];
       pp "NEWLINE ";       
       List.iter (fun _ -> pp "DEDENT ") dedents;
       raise (Issue (NEWLINE::dedents))

  let doEof lexbuf =
    pos := 0;
    match List.hd !record <> 0 with
    | false -> pp "NEWLINE EOF\n\n"; raise (Issue [NEWLINE;EOF])
    | true ->
       let (dedents,_) = popRecord [] 0 !record in
       record := [0];
       pp "NEWLINE ";
       List.iter (fun _ -> pp "DEDENT ") dedents;
       pp "NEWLINE EOF\n\n";
       raise (Issue (NEWLINE::dedents@[NEWLINE;EOF]))
       
  let doSpaceTab lexbuf sptab =
    if not !inIndent then raise Exit
    else
      if sptab = ' ' then inclPos () else jumpPos ();
      let isIndentLast = not (nextCharIs [' ';'\t'] lexbuf) in
      let inDeeperIndent = List.hd !record < !pos in
      let onBorder = List.mem !pos !record in
      (* Format.printf "@[(\'%c\',L:%b,D:%b,B:%b)@." (getNextChar lexbuf) isIndentLast inDeeperIndent onBorder; *)
      match isIndentLast, inDeeperIndent, onBorder with
      | false,_,_ -> raise Exit
      | _,true,_ -> inIndent := false; pushRecord !pos; pp "INDENT "; raise (Issue [INDENT])
      | _,_,true ->
         inIndent := false;
         let (dedents,newRecord) = popRecord [] !pos !record in
         record := newRecord;
         List.iter (fun _ -> pp "DEDENT ") dedents;
         raise (if dedents = [] then Exit else Issue(dedents))
      | _,_,_ -> raise (ParseError "Indent mismatch")
                 
}

let space = [' ']
let tab = [' ']
let newline = ['\n']
let eol = ['\n' '\r']
let digit = ['0'-'9']
let posdigit = ['1'-'9']
let alpha = ['A'-'Z' 'a'-'z']
let alpha0 = ['a'-'z']          
let alpha1 = ['A'-'Z']
let alnum = digit | alpha | ['_' '\'' '%' '#']
let ident0 = (alpha0 | ['$' '#' '_']) alnum*
let ident1 = alpha1 alnum*
let string = "\"" (alnum | [' ' '\n' '\t'])* "\""
let comment = "//"
let natnum = '0' | posdigit digit*
let float = natnum '.' digit*
                               
rule tokens = parse
  | "int"     { pp "tpINT "; [TpINT] }
  | "double"  { pp "tpDOUBLE "; [TpDOUBLE] }
  | "bool"    { pp "tpBOOL "; [TpBOOL] }
  | "unit"    { pp "tpUNIT "; [TpUNIT] }
  | "list"    { pp "tpLIST "; [TpLIST] }
  
  | "true"    { pp "TRUE "; [TRUE] }
  | "false"   { pp "FALSE "; [FALSE] }
  | "while"   { pp "WHILE "; [WHILE] }
  | "for"     { pp "FOR "; [FOR] }
  | "fordict" { pp "FORDICT "; [FORDICT] }
  | "if"      { pp "IF "; [IF]  }
  | "else"    { pp "ELSE "; [ELSE] }
  | "return"  { pp "RETURN "; [RETURN] }
  | "struct"  { pp "STRUCT "; [STRUCT] }  
  | "fun"     { pp "FUN "; [FUN] }
  | "def"     { pp "DEF "; [DEF] }  
  | "match"   { pp "MATCH "; [MATCH] }
  | "with"    { pp "WITH "; [WITH] }
  | "in"      { pp "IN "; [IN] }  
  | "nil"     { pp "NIL "; [NIL] }
  | "null"    { pp "NULL "; [NULL] }
  | "not"     { pp "NOT "; [NOT] }
  | "and"     { pp "AND "; [AND] }  
  | "or"      { pp "OR "; [OR] }  
  | "+="      { pp "PLUSEQ "; [PLUSEQ] }
  | "-="      { pp "MINUSEQ "; [MINUSEQ] }
  | ".-="     { pp "DOTMINUSEQ "; [DOTMINUSEQ] }  
  | "*="      { pp "MULEQ "; [MULEQ] }
  | "/="      { pp "DIVEQ "; [DIVEQ] }
  | '+'       { pp "PLUS "; [PLUS] }
  | '-'       { pp "MINUS "; [MINUS] }
  | ".-"      { pp "DOTMINUS "; [DOTMINUS] }  
  | '*'       { pp "AST "; [AST] }
  | '('       { pp "LPAREN "; [LPAREN] }
  | ')'       { pp "RPAREN "; [RPAREN] }
  | "["       { pp "LBRACKET "; [LBRACKET] }
  | "]"       { pp "RBRACKET "; [RBRACKET] }
  | '='       { pp "EQ "; [EQ] }
  | "=="      { pp "EQEQ "; [EQEQ] }
  | "!="      { pp "NEQ "; [NEQ] }  
  | '<'       { pp "LT "; [LT] }
  | '>'       { pp "GT "; [GT] }
  | "<="      { pp "LE "; [LE] }
  | ">="      { pp "GE "; [GE] }  
  | "->"      { pp "ARROW "; [ARROW] }
  | '|'       { pp "BAR "; [BAR] }
  | ':'       { pp "COLON "; [COLON] }
  | ';'       { pp "SEMICOLON "; [SEMICOLON] }
  | '.'       { pp "DOT "; [DOT] }
  | ".."      { pp "DOTDOT "; [DOTDOT] }
  | ','       { pp "COMMA "; [COMMA] }  
  | "_"       { pp "WILD "; [WILD] }
  | ident0    { let id = Lexing.lexeme lexbuf in
                doIfDebug "LEXING" (F.printf "@[Id(%s)@? ") id;
                [IDENT0 id] }
  | ident1    { let id = Lexing.lexeme lexbuf in
                doIfDebug "LEXING" (F.printf "@[ID(%s)@? ") id;
                [IDENT1 id] }
  | string    { let str = Lexing.lexeme lexbuf in
                doIfDebug "LEXING" (F.printf "@[STRING(%s)@? ") str;
                [STRING str] }
  | float     { let f = float_of_string (Lexing.lexeme lexbuf) in
                doIfDebug "LEXING" (F.printf "@[FLOAT(%f)@? ") f;
                [FLOAT f] }
  | natnum    { let n = int_of_string (Lexing.lexeme lexbuf) in
                doIfDebug "LEXING" (F.printf "@[INT(%d)@? ") n;
                [INT n] }
  | eof       { try doEof lexbuf with Issue toks -> toks }
  | '\n'      { try doNewLine lexbuf with Issue toks -> toks }
  | ' '       { try doSpaceTab lexbuf ' ' with Issue toks -> toks | Exit -> tokens lexbuf }
  | '\t'      { try doSpaceTab lexbuf '\t' with Issue toks -> toks | Exit -> tokens lexbuf }
  | comment [^ '\n' '\r']* eol { tokens lexbuf }
  | _
    {
      let message = Printf.sprintf
        "unknown token %s near characters %d-%d"
        (Lexing.lexeme lexbuf)
        (Lexing.lexeme_start lexbuf)
        (Lexing.lexeme_end lexbuf)
      in
      failwith message
    }

and comment = parse
  | eol     { tokens lexbuf }
  | eof     { try doEof lexbuf with Issue toks -> toks }
  | _       { comment lexbuf }    
