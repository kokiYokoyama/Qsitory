// Qsitory Parser
%{
  open Syntax
  open Tools
  type patexp = pat option * exp option

  let pp_pat p = doIfDebug "PARSING" print_pat p
  let pp_expr e = doIfDebug "PARSING" print_expr e

  let unpackExp (q:patexp): exp = match q with (_,Some e) -> e | _ -> raise (ParseError "Failed to get an expression")
  let unpackPat (q:patexp): pat = match q with (Some p,_) -> p | _ -> raise (ParseError "Failed to get an pattern")
  let packExp (e:exp) = (None,Some e)
  let packPat (p:pat) = (Some p,None)
  let packPatExp (p:pat) (e:exp): patexp = (Some p,Some e)

  let tMergeTuple (t1:P.t) (t2:P.t): P.t =
    match t1,t2 with
    | P.Tuple tt1, P.Tuple tt2 -> P.Tuple (tt1@tt2)
    | P.Tuple tt, _ -> P.Tuple (tt@[t2])
    | _,P.Tuple tt -> P.Tuple (t1::tt)
    | _,_ -> P.Tuple [t1;t2]
                                         
(*
  type oneline = Prog of Program.e list | ProgHead of Program.e list -> Program.e
 *)
%}

%token <string> IDENT0  // x, y, 
%token <string> IDENT1  // Abc, Pqr
%token <string> STRING  // "abc", "a #8 "
%token <int> INT
%token <float> FLOAT
%token INDENT
%token DEDENT            
%token TRUE     // "true"           
%token FALSE    // "false"
%token WHILE    // "while"
%token FOR      // "for"
%token FORDICT  // "fordict"
%token IF       // "if"
%token ELSE     // "else"
%token PASS     // "pass" 
%token FUN      // "fun"
%token DEF      // "def"
%token MATCH    // "match"
%token RETURN   // "return"
%token STRUCT   // "struct"
%token IN       // "in"            
%token PLUS     // '+'
%token MINUS    // '-'
%token DOTMINUS // ".-"
%token AST      // '*'
%token DIV      // '/'
%token MOD      // "mod"
%token LPAREN   // '('
%token RPAREN   // ')'
%token LBRACKET // '['
%token RBRACKET // ']'
%token EQ       // '='
%token EQEQ     // "=="
%token NEQ      // "!="
%token AND      // "and"
%token OR       // "or"
%token NOT      // "not"
%token PLUSEQ   // "+="
%token MINUSEQ  // "-="
%token DOTMINUSEQ // ".-="            
%token MULEQ    // "*="
%token DIVEQ    // "/="
%token LT       // '<'
%token LE       // "<="
%token GT       // '>'
%token GE       // ">="
%token COMMA    // ","
%token ARROW    // "->"
%token WILD     // '_'
%token COLON    // ':'
%token COLCOL   // '::' 
%token SEMICOLON// ';'
%token DOT      // '.'
%token DOTDOT   // ".."
%token BAR      // '|'
%token NIL      // "nil"
%token NULL     // "()"
%token TpINT    // "int"
%token TpDOUBLE // "double"
%token TpSTRING // "string"            
%token TpBOOL   // "bool"
%token TpUNIT   // "unit"
%token TpLIST   // "list"

            
%token NEWLINE  // '\n'
%token EOF 
            
// 結合力(優先度が低い順)
%left AND OR
%nonassoc NOT
%left EQ LT LE GT GE PLUSEQ MINUSEQ MULEQ DIVEQ EQEQ NEQ
%right COLCOL 
%left PLUS MINUS
%right ARROW
%left AST
%left DOTDOT
%nonassoc LPAREN

%start main
%type <Syntax.Program.e list> main;
%type <Syntax.Program.t> qtype
//%type <exp> expression              
//%type <pat> pattern
%type <patexp> patexp
%%
// 
main:  
  | eee = list(expression_newline); eof { List.flatten eee }
;
expression:
  | q = patexp { unpackExp q }
expression_newline:
  | NEWLINE { [] }
  | e = expression; NEWLINE { [e] }
;
pattern:
  | q = patexp { unpackPat q }
;          
blank:
  | NEWLINE { () }
  | INDENT NEWLINE DEDENT { () }
;
eof:
  | list(blank); EOF { () }
;                   
qtype:
/// Base types / Atomic types
  | TpINT    { tInt }
  | TpDOUBLE { tDouble }
  | TpSTRING { tString }
  | TpBOOL   { tBool }
  | TpUNIT   { tUnit }
  | tname = IDENT1 { P.MT tname }
  | LPAREN; t = qtype; RPAREN { t }
/// List types
  | t = qtype; TpLIST { P.List t }
/// Function types
  | t0 = qtype; ARROW; t1 = qtype { P.Fun(t0,t1) }
/// Tuple types  
  | t1 = qtype; AST; t2 = qtype { tMergeTuple t1 t2 }
/// Struct types
  | STRUCT; tName = IDENT1 { P.T tName }    
  | STRUCT; tName = IDENT1; LPAREN; RPAREN; COLON; ee = py_suite
      { let mkEnv1 e =
         match e with
         | P.Declrt1(tp,x,_) -> (x,tp,None)
         | P.Declrt2(tp,x)   -> (x,tp,None)
         | _ ->
            let mes = "Non assignment-form cannot appear in a struct body" in
            raise (ParseError ("Unexpected struct definition: " ^ mes))
        in
        tStruct (List.map mkEnv1 ee)
      }
;
tpprm:
/// For func-params
  | x = IDENT0 { (P.Any,x) }
  | t = qtype COLON x = IDENT0 { (t,x) }
;    
patexp:
/// Numeral / String / Wild
  | n = INT    { packPatExp (pInt n) (eInt n) }
  | d = FLOAT  { packPatExp (pDouble d) (eDouble d) }
  | x = IDENT0 { packPatExp (pVar x) (eVar x) }
  | s = STRING { packPatExp (pString s) (eString s) }
  | WILD   { packPat P.Wild }  
/// Boolean
  | TRUE  { packPatExp pTrue eTrue }
  | FALSE { packPatExp pFalse eFalse }
  | q1 = patexp; LT;   q2 = patexp { packExp @@ P.Operate(P.Lt,unpackExp q1,unpackExp q2) }
  | q1 = patexp; GT;   q2 = patexp { packExp @@ P.Operate(P.Gt,unpackExp q1,unpackExp q2) }
  | q1 = patexp; LE;   q2 = patexp { packExp @@ P.Operate(P.LtEq,unpackExp q1,unpackExp q2) }
  | q1 = patexp; GE;   q2 = patexp { packExp @@ P.Operate(P.GtEq,unpackExp q1,unpackExp q2) }
  | q1 = patexp; EQEQ; q2 = patexp { packExp @@ P.Operate(P.CEq,unpackExp q1,unpackExp q2) }
  | q1 = patexp; NEQ;  q2 = patexp { packExp @@ P.Not (P.Operate(P.CEq,unpackExp q1,unpackExp q2)) }
  | q1 = patexp; AND;  q2 = patexp { packExp @@ P.Operate(P.And,unpackExp q1,unpackExp q2) }
  | q1 = patexp; OR;   q2 = patexp { packExp @@ P.Operate(P.Or,unpackExp q1,unpackExp q2) }
  | NOT pe = patexp { packExp @@ P.Not (unpackExp pe) }
/// Lists
  | NIL { packPatExp pNil eNil }
  | q1 = patexp; COLCOL; q2 = patexp
        {
         let pOpt = try Some (pCons(unpackPat q1,unpackPat q2)) with _ -> None in 
         let eOpt = try Some (eCons(unpackExp q1,unpackExp q2)) with _ -> None in 
         (pOpt,eOpt)
        }
  | LBRACKET; qq = separated_list(COMMA,patexp); RBRACKET
        {
         let pOpt = try Some (List.fold_right (fun q p:pat -> P.Cons(unpackPat q,p)) qq pNil) with _ -> None in 
         let eOpt = try Some (List.fold_right (fun q e:exp -> P.Cons(unpackExp q,e)) qq eNil) with _ -> None in 
         (pOpt,eOpt)
        }
/// Tuple / Null / Single
  | NULL           { packExp P.Null }    
  | LPAREN; RPAREN { packExp P.Null }
  | LPAREN; q = patexp; RPAREN { q }
  | LPAREN; q1 = patexp; COMMA; q2 = patexp; qq = list(COMMA; q = patexp {q}); RPAREN
       {
         let qq = q1::q2::qq in
         let pOpt = try Some (pTuple (List.fold_right (fun q pp -> (unpackPat q)::pp) qq [])) with _ -> None in 
         let eOpt = try Some (eTuple (List.fold_right (fun q ee -> (unpackExp q)::ee) qq [])) with _ -> None in 
         (pOpt,eOpt)
       }
/// Binop
  | q1 = patexp; PLUS;  q2 = patexp { packExp @@ P.Operate(P.Add,unpackExp q1,unpackExp q2) }
  | q1 = patexp; MINUS; q2 = patexp { packExp @@ P.Operate(P.Sub,unpackExp q1,unpackExp q2) }
  | q1 = patexp; AST;   q2 = patexp { packExp @@ P.Operate(P.Mul,unpackExp q1,unpackExp q2) }
  | q1 = patexp; DIV;   q2 = patexp { packExp @@ P.Operate(P.Div,unpackExp q1,unpackExp q2) }
  | q1 = patexp; MOD;   q2 = patexp { packExp @@ P.Operate(P.Mod,unpackExp q1,unpackExp q2) }
/// Assignments
  | q1 = patexp; PLUSEQ;  q2 = patexp { packExp @@ P.AOperate(P.Add,unpackExp q1,unpackExp q2) }
  | q1 = patexp; MINUSEQ; q2 = patexp { packExp @@ P.AOperate(P.Sub,unpackExp q1,unpackExp q2) }
  | q1 = patexp; MULEQ;   q2 = patexp { packExp @@ P.AOperate(P.Mul,unpackExp q1,unpackExp q2) }
  | q1 = patexp; DIVEQ;   q2 = patexp { packExp @@ P.AOperate(P.Div,unpackExp q1,unpackExp q2) }
/// Assignments: p = e / aa.fld = e / "aa".."fld" = e
  | q0 = patexp; EQ; q = patexp 
        { let e = unpackExp q in
          match q0 with
          | (Some p0,_) -> packExp @@ P.Formu (p0,e)
          | (_,Some e0) -> packExp @@ P.Formu2(e0,e)
          | (_,_) -> raise (ParseError "Unexpected assignment")
        }
/// Pattern-substaction e.-p / Pattern-substaction-assignment e .= p
  | q1 = patexp; DOTMINUS;   q2 = patexp { packExp @@ P.Sub(unpackExp q1,unpackPat q2) }
  | q1 = patexp; DOTMINUSEQ; q2 = patexp { packExp @@ P.SubFormu(unpackExp q1,unpackPat q2) }
/// Structs ## aa.fld / "aa".."fld" /  StructName()
  | aa = IDENT0; ssFld = nonempty_list(DOT; sFld=IDENT0 {sFld})
         { packExp @@ (List.fold_left (fun e fld -> P.UseIns1(e,fld)) (eVar aa) ssFld) }
//  | qStr = patexp; DOTDOT; qFld = patexp { packExp @@ P.UseIns2(unpackExp qStr, unpackExp qFld) }
  | sStr = STRING; DOTDOT; sFld = STRING { packExp @@ P.UseIns2(unpackExp sStr, unpackExp sFld) }                               
  | sStr = IDENT1; LPAREN; RPAREN        { packExp @@ P.MakeIns sStr }
  | STRUCT; sStr = IDENT1; LPAREN; RPAREN        { packExp @@ P.MakeIns sStr }    
/// Functions:
  | FUN; prm = separated_list(COMMA,tpprm); ARROW; ee = py_suite
       {
         let prm = if prm = [] then [(P.Any,"")] else prm in
         let eFun = List.hd (List.fold_right (fun (t,s) ee -> [P.Dfun(t,s,P.Block ee)]) prm ee) in
         packExp @@ eFun
       }
  | FUN; LPAREN; prm = separated_list(COMMA,tpprm); RPAREN; ARROW; ee = py_suite
       {
         let prm = if prm = [] then [(P.Any,"")] else prm in
         let eFun = List.hd (List.fold_right (fun (t,s) ee -> [P.Dfun(t,s,P.Block ee)]) prm ee) in
         packExp @@ eFun
       }
  | qFun = patexp; LPAREN; qArg = patexp; RPAREN
       { packExp @@ P.Fun(unpackExp qFun,unpackExp qArg) }
  | DEF; fname = IDENT0; LPAREN; prm = separated_list(COMMA,tpprm); RPAREN; COLON; ee = py_suite
       {
         let prm = if prm = [] then [(P.Any,"")] else prm in
         let eFun = List.hd (List.fold_right (fun (t,s) ee -> [P.Dfun(t,s,P.Block ee)]) prm ee) in
         packExp @@ P.Formu(pVar fname, eFun)
       }
/// Return
  | RETURN; q = patexp { packExp @@ P.Return (unpackExp q) }
/// Match-expression
  | MATCH; q = patexp; COLON; cc = match_clauses_suite
       { packExp @@ P.Match(unpackExp q,cc) }
/// Declaration / Declaration+Initialization
  | tp = qtype; COLON; x = IDENT0; qOpt = option(EQ; q = patexp {q})
          {
            match qOpt with
            | None -> packExp @@ P.Declrt2(tp,x)
            | Some q -> packExp @@ P.Declrt1(tp,x,unpackExp q)
          }
/// If-expression ## if e : block (else if e: block )* | (else : block)? )
  | IF; q = patexp; COLON; eeThen = py_suite; nonempty_list(NEWLINE); ELSE; COLON; eeElse = py_suite
        { packExp @@ P.If (unpackExp q, P.Block eeThen, P.Block eeElse) }
/// While-expression
  | WHILE; qCond = patexp; COLON; eeBody = py_suite
       { packExp @@ P.While(unpackExp qCond, P.Block eeBody) }
/// For-expression ## for x,y,z in e : block   
  | FOR; ss = separated_list(COMMA,IDENT0); IN; qq = separated_list(COMMA,patexp); COLON; eeBody = py_suite
       { packExp @@ P.For(ss, List.map unpackExp qq, P.Block eeBody) }
/// Fordict-expression ## fordict x,y,z in e : block
  | FORDICT; ss = separated_list(COMMA,IDENT0); IN; q = patexp; COLON; eeBody = py_suite
       { packExp @@ P.For_dict (ss, unpackExp q, P.Block eeBody) }
/// Struct expression
  | STRUCT; sName = IDENT1; COLON; eeBody = py_suite
      { packExp @@ P.Dstruct (sName, P.Block eeBody) }
/// Pass
  | PASS { packExp @@ P.Block [] }
;

/// block (Python-style, See: https://docs.python.org/ja/3/reference/compound_stmts.html)
py_stmt_list:
  | e = expression; ee = list(SEMICOLON; e = expression { e }) { e::ee }
;      
py_statement:
  | ee = py_stmt_list; nonempty_list(NEWLINE) { ee }
;
py_suite:
  | ee = py_stmt_list; { ee }
  | NEWLINE; INDENT; eee = nonempty_list(py_statement); DEDENT { List.flatten eee }
  | NEWLINE; INDENT; NEWLINE; DEDENT { [] }
;
match_clause_simple:
  | p = pattern; ARROW; body = expression { (p,P.Block [body]) }    
;
match_clause:
  | p = pattern; ARROW; ee = py_suite; list(NEWLINE) { (p,P.Block ee) }
;
match_clauses_suite:
  | option(BAR); cc = separated_nonempty_list(BAR, c = match_clause_simple { c }) { cc }
  | NEWLINE; INDENT; cc = nonempty_list(BAR; c = match_clause {c}); DEDENT { cc }
;
