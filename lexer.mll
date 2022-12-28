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
- 行頭の | (match式のパターン) もタブと同じ扱い
- 改行される度に indent mode に入る．(new)indent mode 時は常に現在地を覚えておく．
- (new)indent mode の間は次の文字を先読みする．空白/タブ以外の文字を発見したら normal mode に移行
- normal mode 移行時に現在地と indent record の数値が不整合なら fail．indent record の末尾から N個手前と整合したら N 個の DEDENT トークンを発行
- indent record の最大値を越えたら INDENT トークンを発行して newindent mode に入る
- newindent mode から normal mode への移行時に現在地の数値を indent record の末尾に追加
   *)

  let inIndent = ref true
           
  let record = ref [0]

  let pp_record fmt rcd = Format.printf "[%a]" (pp_list "" "," pp_int) rcd
             
  let pushRecord n = record := n::!record
                   
  let popRecord () = record := List.tl !record
                   
  let pos = ref 0
          
  let inclPos () = pos := !pos + 1

  let prev_eol_record = ref 0
                 
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
    | m::record1 when n < m -> popRecord (DEDENT::NEWLINE::toks) n record1
    | m::_ when n = m -> (toks,record)
    | _ -> failwith ""

  let itsNewLine lexbuf =
    Lexing.new_line lexbuf;
    prev_eol_record := lexbuf.Lexing.lex_curr_pos
         
  let doNewLine lexbuf =
    itsNewLine lexbuf;
    pos := 0;
    inIndent := nextCharIs [' ';'\t'] lexbuf;
    let nextIsCommentLine = nextCharIs ['/'] lexbuf in
    match nextIsCommentLine, List.hd !record <> 0 && not !inIndent with
    | true,_ -> raise Exit
    | _,false -> addMemo "NEWLINE"; raise (Issue [NEWLINE])
    | _,true ->
       let (dedents,_) = popRecord [] 0 !record in
       record := [0];
       addMemo "NEWLINE";
       List.iter (function NEWLINE -> addMemo "NEWLINE" | DEDENT -> addMemo "DEDENT" | _ -> failwith "") dedents;
       raise (Issue (NEWLINE::dedents))

  let doEof lexbuf =
    pos := 0;
    match List.hd !record <> 0 with
    | false -> addMemo "NEWLINE EOF"; raise (Issue [NEWLINE;EOF])
    | true ->
       let (dedents,_) = popRecord [] 0 !record in
       record := [0];
       addMemo "NEWLINE";
       List.iter (function NEWLINE -> addMemo "NEWLINE" | DEDENT -> addMemo "DEDENT" | _ -> failwith "") dedents;
       addMemo "NEWLINE EOF";
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
      | _,true,_ -> inIndent := false; pushRecord !pos; addMemo "INDENT"; raise (Issue [INDENT])
      | _,_,true ->
         inIndent := false;
         let (dedents,newRecord) = popRecord [] !pos !record in
         record := newRecord;
         List.iter (function NEWLINE -> addMemo "NEWLINE" | DEDENT -> addMemo "DEDENT" | _ -> failwith "") dedents;
         raise (if dedents = [] then Exit else Issue(dedents))
      | _,_,_ -> raise (ParseError "Indent mismatch")

}

let space = [' ']
let tab = [' ']
let newline = ['\n']
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
  | "int"     { addMemo "tpINT"; [TpINT] }
  | "string"  { addMemo "tpSTRING"; [TpSTRING] }
  | "double"  { addMemo "tpDOUBLE"; [TpDOUBLE] }
  | "bool"    { addMemo "tpBOOL"; [TpBOOL] }
  | "unit"    { addMemo "tpUNIT"; [TpUNIT] }
  | "list"    { addMemo "tpLIST"; [TpLIST] }
  
  | "true"    { addMemo "TRUE"; [TRUE] }
  | "false"   { addMemo "FALSE"; [FALSE] }
  | "while"   { addMemo "WHILE"; [WHILE] }
  | "for"     { addMemo "FOR"; [FOR] }
  | "fordict" { addMemo "FORDICT"; [FORDICT] }
  | "if"      { addMemo "IF"; [IF]  }
  | "else"    { addMemo "ELSE"; [ELSE] }
  | "pass"    { addMemo "PASS"; [PASS] } 
  | "return"  { addMemo "RETURN"; [RETURN] }
  | "struct"  { addMemo "STRUCT"; [STRUCT] }  
  | "fun"     { addMemo "FUN"; [FUN] }
  | "def"     { addMemo "DEF"; [DEF] }  
  | "match"   { addMemo "MATCH"; [MATCH] }
  | "in"      { addMemo "IN"; [IN] }  
  | "nil"     { addMemo "NIL"; [NIL] }
  | "null"    { addMemo "NULL"; [NULL] }
  | "not"     { addMemo "NOT"; [NOT] }
  | "and"     { addMemo "AND"; [AND] }  
  | "or"      { addMemo "OR"; [OR] }  
  | "+="      { addMemo "PLUSEQ"; [PLUSEQ] }
  | "-="      { addMemo "MINUSEQ"; [MINUSEQ] }
  | ".-="     { addMemo "DOTMINUSEQ"; [DOTMINUSEQ] }  
  | "*="      { addMemo "MULEQ"; [MULEQ] }
  | "/="      { addMemo "DIVEQ"; [DIVEQ] }
  | '+'       { addMemo "PLUS"; [PLUS] }
  | '-'       { addMemo "MINUS"; [MINUS] }
  | ".-"      { addMemo "DOTMINUS"; [DOTMINUS] }  
  | '*'       { addMemo "AST"; [AST] }
  | '/'       { addMemo "DIV"; [DIV] }
  | "mod"     { addMemo "MOD"; [MOD] }  
  | '('       { addMemo "LPAREN"; [LPAREN] }
  | ')'       { addMemo "RPAREN"; [RPAREN] }
  | "["       { addMemo "LBRACKET"; [LBRACKET] }
  | "]"       { addMemo "RBRACKET"; [RBRACKET] }
  | '='       { addMemo "EQ"; [EQ] }
  | "=="      { addMemo "EQEQ"; [EQEQ] }
  | "!="      { addMemo "NEQ"; [NEQ] }  
  | '<'       { addMemo "LT"; [LT] }
  | '>'       { addMemo "GT"; [GT] }
  | "<="      { addMemo "LE"; [LE] }
  | ">="      { addMemo "GE"; [GE] }  
  | "->"      { addMemo "ARROW"; [ARROW] }
  | '|'       { addMemo "BAR"; [BAR] }
  | ':'       { addMemo "COLON"; [COLON] }
  | ';'       { addMemo "SEMICOLON"; [SEMICOLON] }
  | '.'       { addMemo "DOT"; [DOT] }
  | ".."      { addMemo "DOTDOT"; [DOTDOT] }
  | ','       { addMemo "COMMA"; [COMMA] }  
  | "_"       { addMemo "WILD"; [WILD] }
  | ident0    { let id = Lexing.lexeme lexbuf in
                addMemo (F.sprintf "Id(%s)" id);
                [IDENT0 id] }
  | ident1    { let id = Lexing.lexeme lexbuf in
                addMemo (F.sprintf "ID(%s)" id);
                [IDENT1 id] }
  | string    { let str = Lexing.lexeme lexbuf in
                addMemo (F.sprintf "STRING(%s) " str);
                [STRING str] }
  | float     { let f = float_of_string (Lexing.lexeme lexbuf) in
                addMemo (F.sprintf "FLOAT(%f)" f);
                [FLOAT f] }
  | natnum    { let n = int_of_string (Lexing.lexeme lexbuf) in
                addMemo (F.sprintf "INT(%d)" n);
                [INT n] }
  | eof       { try doEof lexbuf with Issue toks -> toks | Exit -> tokens lexbuf }
  | '\n'      { try doNewLine lexbuf with Issue toks -> toks | Exit -> tokens lexbuf }
  | ' '       { try doSpaceTab lexbuf ' ' with Issue toks -> toks | Exit -> tokens lexbuf }
  | '\t'      { try doSpaceTab lexbuf '\t' with Issue toks -> toks | Exit -> tokens lexbuf }
  | comment [^ '\n']* '\n' { try doNewLine lexbuf with Issue toks -> toks | Exit -> tokens lexbuf }
  | "/*"      { comment lexbuf }
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
  | "*/"    { tokens lexbuf }
  | eof     { try doEof lexbuf with Issue toks -> toks }
  | '\n'    { itsNewLine lexbuf; comment lexbuf }
  | _       { comment lexbuf }    
