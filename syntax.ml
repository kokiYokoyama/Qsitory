exception Error
exception Error6
open Tools
        
module Program = struct
  (* Definition------------------------------------------------------------*)

  (* operator *)
  type op = Add | Sub | Sub2 | Mul | Div | Mod | Lt | LtEq | Gt | GtEq | CEq
          | And | Or
  (* assignment operator *)
  type aop = Add | Sub | Mul | Div | Eq

  (* type *)
  type t = T of string | A of string | Any | MT of string
         | Int | Double | Bool | String | Ind | Unit
         | List of t | Tuple of t list
         | Fun of t * t
         | Struct of structEnv
         | Operate of op * t * t
         | Return of t
  (* value *)       
  and v = Int of int | Double of float | Bool of bool
        | String of string | Null | Nil
        | Cons of v * v | Tuple of v list
        | FunClos of env * string * bk (* FunClos(E,x,e) is (E)[fun x-> e] *)
        | Struct of string * env
  (* pattern *)
  and p = Int of int | Double of float | Bool of bool | String of string
        | Var of string | Nil | Wild | Cons of p * p
        | Tuple of p list
  (* expr *)
  and e = Int of int | Double of float | Bool of bool | String of string
        | Var of string | Null | Nil | Cons of e * e | Tuple of e list
        | Declrt1 of t * string * e | Declrt2 of t * string | Formu of p * e
        | Formu2 of t * e * e | AOperate of aop * e * e | SubFormu of e * p
        | Operate of op * e * e | Sub of e * p | Not of e | If of e * bk * bk
        | Match of e * ( (p * bk) list )
        | For of ( string list) * ( e list ) * bk
        | For_dict of ( string list ) * e * bk
        | While of e * bk | Dfun of t * string * bk | Fun of e * e
        | Return of e | Dstruct of string * bk
        | UseIns1 of e * string | UseIns2 of e * e
  (* block *)
  and bk = Block of e list
  (* environment *)
  and env = (string * t * v option) list
  (* type environment *)
  and tenv = ( t * t ) list
  (* struct environment *)
  and structEnv = (string * t) list
  (* type equals *)
  and tequals = ( t * t ) list

  (* other *)
  type evalResult =(v * env * tenv )
  type tvalResult =(tequals * int )
  type patternop = Some of env | None

end;;

module P = Program
type exp = P.e
type pat = P.p
type value = P.v
type tp = P.t
let pNil: pat = P.Nil
let eNil: exp = P.Nil
let vNil: value = P.Nil
let eCons(e1,e2): exp = P.Cons(e1,e2)                
let pCons(p1,p2): pat = P.Cons(p1,p2)
let vCons(v1,v2): value = P.Cons(v1,v2)
let eVar v: exp = P.Var v
let pVar v: pat = P.Var v                
let eTrue: exp = P.Bool true
let pTrue: pat = P.Bool true
let vTrue: value = P.Bool true
let eFalse: exp = P.Bool false
let pFalse: pat = P.Bool false
let vFalse: value = P.Bool false
let eInt n: exp = P.Int n
let pInt n: pat = P.Int n
let vInt n: value = P.Int n
let eDouble d: exp = P.Double d
let pDouble d: pat = P.Double d
let vDouble d: value = P.Double d
let eString s: exp = P.String s
let pString s: pat = P.String s
let vString s: P.v = P.String s
let eTuple ee: exp = P.Tuple ee
let pTuple pp: pat = P.Tuple pp
let tTuple tt: tp = P.Tuple tt
let tInt: tp = P.Int
let tDouble: tp = P.Double
let tBool: tp = P.Bool
let tString: tp = P.String
let tUnit: tp = P.Unit
let tStruct env: tp = P.Struct env
let tTuple tt : tp = P.Tuple tt
let vTuple vv : value = P.Tuple vv
let eNull: exp = P.Null                      
let vNull: value = P.Null
let tMT s: tp = P.MT s

module Result = struct

  type t = { mutable value: P.v option; mutable eenv: P.env option; mutable tenv: P.tenv option }
         
  let from_evalResult ((v,eenv,tenv):P.evalResult): t =
    { value = Some v; eenv = Some eenv; tenv = Some tenv }

  let doubleValue = ref false
  let doubleTenv = ref false
  let doubleEenv = ref false
            
  let setValue result v =
    (if result.value <> None then doubleValue := true else ());
    result.value <- Some v

  let setEenv result eenv =
    (if result.eenv <> None then doubleEenv := true else ());
    result.eenv <- Some eenv

  let setTenv result tenv =
    (if result.tenv <> None then doubleTenv := true else ());
    result.tenv <- Some tenv

end
module R = Result
                    
(* print------------------------------------------------------------------ *)

(* operator *)
let rec print_op (op:Program.op) =
  match op with
  |Add -> Format.printf "+"
  |Sub -> Format.printf "-"
  |Sub2 -> Format.printf "-"
  |Mul -> Format.printf "*"
  |Div -> Format.printf "/"
  |Mod -> Format.printf "mod"
  |Lt -> Format.printf "<"
  |LtEq -> Format.printf "<="
  |Gt -> Format.printf ">"
  |GtEq -> Format.printf ">="
  |CEq -> Format.printf "=="
  |And -> Format.printf "&&"
  |Or -> Format.printf "||"

(* assignment operator *)
and print_aop (aop:Program.aop) =
  match aop with
  |Add -> Format.printf "+="
  |Sub -> Format.printf "-="
  |Mul -> Format.printf "*="
  |Div -> Format.printf "/="
  |Eq -> Format.printf "="

(* type *)
and print_type (t:Program.t) =
  match t with
  |T s -> Format.printf "T(%s)" s
  |A s -> Format.printf "A(%s)" s
  |MT s -> Format.printf "MT(%s)" s
  |Unit -> Format.printf "Unit"
  |Int -> Format.printf "Int"
  |Double -> Format.printf "Double"      
  |Bool -> Format.printf "Bool"
  |String -> Format.printf "String"
  |List t1 -> Format.printf "List(%a)" (fun _ -> print_type) t1
  |Tuple list -> Format.printf "Tuple(%a)" (fun _ -> type_tuple_print) list
  |Fun(t1,t2) -> Format.printf "Fun(%a->%a)" (fun _ ->print_type) t1 (fun _ ->print_type) t2
  |Struct list -> Format.printf "[%a]" ( fun _ -> type_struct_print ) list
  |Any -> Format.printf "Any"
  |Ind -> Format.printf "Ind"
  |Operate(op,t1,t2) -> Format.printf "Operate(%a %a %a)" (fun _ -> print_type) t1 (fun _ ->print_op) op (fun _ -> print_type) t2
  |Return t1 -> Format.printf "Return(%a)" (fun _ -> print_type) t1

and type_tuple_print list =
  match list with
  |t::[] -> Format.printf "%a" (fun _ -> print_type) t
  |t::list1 -> Format.printf "%a,%a" (fun _ -> print_type) t (fun _ -> type_tuple_print) list1
  | _ -> raise Error

and type_struct_print list =
  match list with
  |(s,t)::[] -> Format.printf "(%s,%a)" s (fun _ -> print_type) t
  |(s,t)::list1 -> Format.printf "(%s,%a),%a" s (fun _ -> print_type) t (fun _ -> type_struct_print) list1
  | _ -> raise Error

(* value *)
and print_value (v:Program.v) =
  match v with
  |Int i -> Format.printf "%d" i
  |Double d -> Format.printf "%f" d
  |Bool b -> Format.printf "%B" b
  |String s -> Format.printf "%s" s
  |Null -> Format.printf "()"
  |Nil -> Format.printf "[]" 
  |Cons(v1,v2) -> Format.printf "%a::%a" (fun _ -> print_value) v1 (fun _ -> print_value) v2
  |Tuple list -> Format.printf "(%a)" (fun _ -> value_tuple_print) list
  |FunClos(env,s,bk) -> Format.printf "FunClos(%a,%s,%a)" (fun _ -> print_env) env s (fun _ -> print_block ) bk
  |Struct (s,list) -> Format.printf "Struct(%s,[%a])" s (fun _ -> value_struct_print) list

and value_tuple_print list =
  match list with
  |v::[] -> Format.printf "%a" (fun _ -> print_value) v
  |v::list1 -> Format.printf "%a,%a" (fun _ -> print_value) v (fun _ -> value_tuple_print) list1
  | _ -> raise Error

and value_struct_print list =
  match list with
  |(s,t,Some v)::[] -> Format.printf "(%s,%a,%a)" s (fun _ -> print_type) t (fun _ -> print_value) v
  |(s,t,None)::[] -> Format.printf "(%s,%a,None)" s (fun _ -> print_type) t
  |(s,t,Some v)::list1 -> Format.printf "(%s,%a,%a),%a" s (fun _ -> print_type) t (fun _ -> print_value) v (fun _ -> value_struct_print) list1
  |(s,t,None)::list1 -> Format.printf "(%s,%a,None),%a" s (fun _ -> print_type) t (fun _ -> value_struct_print) list1
  | _ -> raise Error

(* pattern *)
and print_pat (p:Program.p) =
  match p with
  | Int i -> Format.printf "%d" i
  | Double d -> Format.printf "%f" d
  | Bool b -> Format.printf "%B" b
  | String s -> Format.printf "%s" s
  | Var s -> Format.printf "Var(%s)" s
  | Nil -> Format.printf "[]"
  | Wild -> Format.printf "_"
  | Cons(p1,p2) -> Format.printf "%a::%a" (fun _ -> print_pat) p1 (fun _ -> print_pat) p2
  | Tuple list -> Format.printf "(%a)" (fun _ -> pat_tuple_print) list

and pat_tuple_print list =
  match list with
  |p::[] -> Format.printf "%a" (fun _ -> print_pat) p
  |p::list1 -> Format.printf "%a,%a" (fun _ -> print_pat) p (fun _ -> pat_tuple_print) list1
  | _ -> raise Error

(* expr *)
and print_expr (e:Program.e) =
  match e with
  |Int i -> Format.printf "Int(%d)" i
  |Double d -> Format.printf "Double(%f)" d
  |Bool b -> Format.printf "Bool(%B)" b
  |String s -> Format.printf "String(%s)" s
  |Var s -> Format.printf "Var(%s)" s
  |Null -> Format.printf "Null"
  |Nil -> Format.printf "Nil"
  |Cons(e1,e2) -> Format.printf "Cons(%a,%a)" (fun _ -> print_expr) e1 (fun _ -> print_expr) e2
  |Tuple list -> Format.printf "Tuple(%a)" (fun _ -> expr_tuple_print) list
  |Declrt1(t,s,e) -> Format.printf "Declrt1(%a,%s,%a)" (fun _ -> print_type) t s (fun _ -> print_expr) e
  |Declrt2(t,s) -> Format.printf "Declrt2(%a,%s)" (fun _ -> print_type) t s
  |Formu(p,e) -> Format.printf "Formu(%a,%a)" (fun _ -> print_pat) p (fun _ -> print_expr) e
  |Formu2(t,e1,e2) -> Format.printf "Formu2(%a,%a,%a)" (fun _ -> print_type) t (fun _ -> print_expr) e1 (fun _ -> print_expr) e2
  |AOperate(aop,e1,e2) -> Format.printf "AOperate(%a,%a,%a)" (fun _ -> print_aop) aop (fun _ -> print_expr) e1 (fun _ -> print_expr) e2
  |SubFormu(e,p) -> Format.printf "SubFormu(%a,%a)" (fun _ -> print_expr) e (fun _ -> print_pat ) p
  |Operate(op,e1,e2) -> Format.printf "Operate(%a,%a,%a)" (fun _ -> print_op) op (fun _ -> print_expr) e1 (fun _ -> print_expr) e2
  |Sub(e,p) -> Format.printf "Sub(%a,%a)" (fun _ -> print_expr) e (fun _ -> print_pat) p
  |Not(e) -> Format.printf "Not(%a)" (fun _ -> print_expr) e
  |If(e1,bk1,bk2) -> Format.printf "If(%a,%a,%a)" (fun _ -> print_expr) e1 (fun _ -> print_block) bk1 (fun _ -> print_block) bk2
  |Match(e,list) -> Format.printf "Match(%a,[%a])" (fun _ -> print_expr) e (fun _ -> expr_patlist_print) list
  |For(list1,list2,bk) -> Format.printf "For([%a],[%a],%a)" (fun _ -> expr_parlist_print) list1 (fun _ -> expr_arglist_print) list2 (fun _ -> print_block) bk
  |For_dict(list1,e1,bk) -> Format.printf "For_dict([%a],%a,%a)" (fun _ -> expr_parlist_print) list1 (fun _ -> print_expr) e1 (fun _ -> print_block) bk
  |While(e1,bk) -> Format.printf "While(%a,%a)" (fun _ -> print_expr) e1 (fun _ -> print_block) bk
  |Dfun(t,s,bk) -> Format.printf "Dfun(%a,%s,%a)" (fun _ -> print_type) t s (fun _ -> print_block) bk
  |Fun(e1,e2) -> Format.printf "Fun(%a,%a)" (fun _ -> print_expr) e1 (fun _ -> print_expr) e2
  |Return(e) -> Format.printf "Return(%a)" (fun _ -> print_expr) e
  |Dstruct(s,bk) -> Format.printf "Dstruct(%s,%a)" s (fun _ -> print_block) bk
  |UseIns1(e,s) -> Format.printf "UseIns1(%a,%s)" (fun _ -> print_expr) e s
  |UseIns2(e1,e2) -> Format.printf "UseIns2(%a,%a)" (fun _ -> print_expr) e1 (fun _ -> print_expr) e2

(* block *)
and print_block (bk:Program.bk) =
  match bk with
  |Block(elist) -> Format.printf "Block([%a])" (fun _ -> expr_arglist_print) elist

and expr_tuple_print list =
  match list with
  |e::[] -> Format.printf "%a" (fun _ -> print_expr) e
  |e::list1 -> Format.printf "%a,%a" (fun _ -> print_expr) e (fun _ -> expr_tuple_print) list1
  | _ -> raise Error

and expr_patlist_print list =
  match list with
  |(p,bk)::[] -> Format.printf "(%a,%a)" (fun _ -> print_pat) p (fun _ -> print_block) bk
  |(p,bk)::list1 -> Format.printf "(%a,%a),%a" (fun _ -> print_pat) p (fun _ -> print_block) bk (fun _ -> expr_patlist_print) list1
  | _ -> raise Error

and expr_parlist_print list =
  match list with
  |s::[] -> Format.printf "%s" s
  |s::list1 -> Format.printf "%s,%a" s (fun _ -> expr_parlist_print) list1
  | _ -> raise Error

and expr_arglist_print list =
  match list with
  |e::[] -> Format.printf "%a" (fun _ -> print_expr) e
  |e::list1 -> Format.printf "%a,%a" (fun _ -> print_expr) e (fun _ -> expr_arglist_print) list1
  | _ -> raise Error

(* environment *)
and print_env (env:Program.env) =
  match env with
  |(s,t,Some v)::list -> Format.printf "(%s,%a,%a)::%a" s (fun _ -> print_type) t (fun _ -> print_value) v (fun _ -> print_env) list
  |(s,t,None)::list -> Format.printf "(%s,%a,None)::%a" s (fun _ -> print_type) t (fun _ -> print_env) list
  | [] -> Format.printf "[]"

(* type environment *)
and print_tenv (tenv:Program.tenv) =
  match tenv with
  |(t1,t2)::list -> Format.printf "(%a,%a)::%a" (fun _ -> print_type) t1 (fun _ -> print_type) t2 (fun _ -> print_tenv) list
  | [] -> Format.printf "[]"

(* type equals *)
and print_tequals (tequals:Program.tequals) =
    match tequals with
    |(t1,t2)::[] -> Format.printf "(%a=%a)\n" (fun _ -> print_type) t1 (fun _ -> print_type) t2
    |(t1,t2)::tequals1 -> Format.printf "\n(%a=%a),%a" (fun _ -> print_type) t1 (fun _ -> print_type) t2 (fun _ -> print_tequals) tequals1
    | [] -> Format.printf "[]"
;;

(* other *)
let rec print_evalResult (result:Program.evalResult) =
  match result with
  |(v,env,tenv) -> Format.printf "value: %a\nenv: %a\ntenv: %a\n" (fun _ -> print_value) v (fun _ -> print_env) env (fun _ -> print_tenv) tenv
;;

(* equalities of data types *)
let eq_opt eq opt1 opt2 = 
  match opt1,opt2 with
  | None,None -> true
  | Some q1,Some q2 -> eq q1 q2
  | _,_ -> false

let eq_pair eq1 eq2 (p1,p2) (q1,q2) = eq1 p1 q1 && eq2 p2 q2
                                    
let eq_list eq pp1 pp2 = List.length pp1 = List.length pp2 && List.for_all2 eq pp1 pp2

let rec eq_expr e1 e2 = e1 = e2
and eq_type (t1:tp) (t2:tp) =
  match t1,t2 with
  | P.Struct strEnv1, P.Struct strEnv2 -> eq_structEnv strEnv1 strEnv2
  | _,_ -> t1 = t2
and eq_value (v1:value) (v2:value) =
  match v1,v2 with
  | P.Cons (v1a,v1b),Cons (v2a,v2b) -> eq_pair eq_value eq_value (v1a,v2a) (v1b,v2b)
  | P.Tuple vv1, P.Tuple vv2 -> eq_list eq_value vv1 vv2
  | _,_ -> v1 = v2
and eq_structEnv strEnv1 strEnv2 =
  match checkEqFun eq_type strEnv1 strEnv2 with
  | true -> true
  | false -> false
and eq_tenv (tenv1: P.tenv) (tenv2: P.tenv) = checkEqFun eq_type tenv1 tenv2
and eq_eenv eenv1 eenv2 = checkEqFun2 eq_type (eq_opt eq_value) eenv1 eenv2

let eq_result (res1: Result.t) (res2: Result.t) =
  let checkValue = eq_opt eq_value res1.R.value res2.R.value in
  let checkTenv = eq_opt eq_tenv res1.R.tenv res2.R.tenv in
  let checkEenv = eq_opt eq_eenv res1.R.eenv res2.R.eenv in
  (if checkValue then () else print_endline "Failed: Value equality check");
  (if checkTenv then () else print_endline "Failed: Tenv equality check");
  (if checkEenv then () else print_endline "Failed: Eenv equality check");
  checkValue && checkTenv && checkEenv 


