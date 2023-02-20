open Syntax
open Tools   
module F = Format
   
                    
let rec pp_op fmt (op:Program.op) =
  match op with
  | Add -> pp_string fmt "+"
  | Sub -> pp_string fmt "-"
  | Sub2 -> pp_string fmt "-"
  | Mul -> pp_string fmt "*"
  | Div -> pp_string fmt "/"
  | Mod -> pp_string fmt "mod"
  | Lt -> pp_string fmt "<"
  | LtEq -> pp_string fmt "<="
  | Gt -> pp_string fmt ">"
  | GtEq -> pp_string fmt ">="
  | CEq -> pp_string fmt "=="
  | And -> pp_string fmt "&&"
  | Or -> pp_string fmt "||"

(* assignment operator *)
and pp_aop fmt (aop:Program.aop) =
  match aop with
  | Add -> pp_string fmt "+="
  | Sub -> pp_string fmt "-="
  | Mul -> pp_string fmt "*="
  | Div -> pp_string fmt "/="
  | Eq -> pp_string fmt "="

(* type *)
and pp_type fmt (t:Program.t) =
  match t with
  | T s -> pp_string fmt s
  | MT s -> pp_string fmt s
  | Int -> pp_string fmt "Int"
  | Unit -> pp_string fmt "Unit"         
  | Double -> pp_string fmt "Double"      
  | Bool -> pp_string fmt "Bool"
  | String -> pp_string fmt "String"
  | List t1 -> F.fprintf fmt "List(%a)" pp_type t1
  | Tuple list -> F.fprintf fmt "Tuple(%a)" (pp_list0 pp_type) list
  | Fun(t1,t2) -> F.fprintf fmt "%a->%a" pp_type t1 pp_type t2
  | Struct list -> F.fprintf fmt "%a" (pp_list0 pp_type_struct1) list
  | Any -> pp_string fmt "Any"
  | Ind -> pp_string fmt "Ind"
  | Operate(op,t1,t2) -> F.fprintf fmt "Operate(%a %a %a)" pp_type t1 pp_op op pp_type t2
  | Return t1 -> F.fprintf fmt "Return(%a)" pp_type t1

and pp_type_struct1 fmt (s,t) = pp_tuple2 pp_string pp_type fmt (s,t)
         
(* value *)
and pp_value fmt (v:Program.v) =
  match v with
  | Int i -> F.fprintf fmt "%d" i
  | Double d -> F.fprintf fmt "%f" d
  | Bool b -> F.fprintf fmt "%B" b
  | String s -> pp_string fmt s
  | Null -> pp_string fmt "()"
  | Nil -> pp_string fmt "[]" 
  | Cons(v1,v2) -> F.fprintf fmt "%a::%a" pp_value v1 pp_value v2
  | Tuple list -> F.fprintf fmt "(%a)" (pp_list "" "," pp_value) list
  | FunClos(env,s,bk) -> F.fprintf fmt "FunClos(%a,%s,%a)" pp_env env s pp_block bk
  | Struct (s,list) -> F.fprintf fmt "Struct(%s,[%a])" s pp_env list

(* and pp_value_struct1 fmt (s,t,v) = pp_tuple3 pp_string pp_type pp_value fmt (s,t,v) *)

(* pattern *)
and pp_pat fmt (p:Program.p) =
  match p with
  | Int i -> F.fprintf fmt "%d" i
  | Double d -> F.fprintf fmt "%f" d
  | Bool b -> F.fprintf fmt "%B" b
  | String s -> pp_string fmt s
  | Var s -> F.fprintf fmt "Var(%s)" s
  | Nil -> pp_string fmt "[]"
  | Wild -> pp_string fmt "_"
  | Cons(p1,p2) -> F.fprintf fmt "%a::%a" pp_pat p1 pp_pat p2
  | Tuple list -> F.fprintf fmt "(%a)" (pp_list0 pp_pat) list

(* expr *)
and pp_expr fmt (e:Program.e) =
  match e with
  | Int i -> F.fprintf fmt "Int(%d)" i
  | Double d -> F.fprintf fmt "Double(%f)" d
  | Bool b -> F.fprintf fmt "Bool(%B)" b
  | String s -> F.fprintf fmt "String(%s)" s
  | Var s -> F.fprintf fmt "Var(%s)" s
  | Null -> F.fprintf fmt "Null"
  | Nil -> F.fprintf fmt "Nil"
  | Cons(e1,e2) -> F.fprintf fmt "Cons(%a,%a)" pp_expr e1 pp_expr e2
  | Tuple list -> F.fprintf fmt "Tuple(%a)"  (pp_list0 pp_expr) list
  | Declrt1(t,s,e) -> F.fprintf fmt "Declrt1(%a,%s,%a)" pp_type t s pp_expr e
  | Declrt2(t,s) -> F.fprintf fmt "Declrt2(%a,%s)" pp_type t s
  | Formu(p,e) -> F.fprintf fmt "Formu(%a,%a)" pp_pat p pp_expr e
  | Formu2(t,e1,e2) -> F.fprintf fmt "Formu2(%a,%a,%a)" pp_type t pp_expr e1 pp_expr e2
  | AOperate(aop,e1,e2) -> F.fprintf fmt "AOperate(%a,%a,%a)" pp_aop aop pp_expr e1 pp_expr e2
  | SubFormu(e,p) -> F.fprintf fmt "SubFormu(%a,%a)" pp_expr e pp_pat p
  | Operate(op,e1,e2) -> F.fprintf fmt "Operate(%a,%a,%a)" pp_op op pp_expr e1 pp_expr e2
  | Sub(e,p) -> F.fprintf fmt "Sub(%a,%a)" pp_expr e pp_pat p
  | Not(e) -> F.fprintf fmt "Not(%a)" pp_expr e
  | If(e1,e2,e3) -> F.fprintf fmt "If(%a,%a,%a)" pp_expr e1 pp_expr e2 pp_expr e3
  | Match(e,list) -> F.fprintf fmt "Match(%a,[%a])" pp_expr e (pp_list0 pp_expr_patlist1) list
                   (*
  | For(list1,ee,e) -> F.fprintf fmt "For([%a],[%a],%a)" (pp_list0 pp_expr_patlist1) list1 (pp_list0 pp_expr) ee pp_expr e
  | For_dict(list1,e1,e2) -> F.fprintf fmt "For_dict([%a],%a,%a)" (pp_list0 pp_expr_patlist1) list1 pp_expr e1 pp_expr e2
                    *)
  | For(list1,ee,bk) -> F.fprintf fmt "For([%a],[%a],%a)" (pp_list0 pp_string) list1 (pp_list0 pp_expr) ee pp_block bk                   
  | For_dict(list1,e1,bk) -> F.fprintf fmt "For_dict([%a],%a,%a)" (pp_list0 pp_string) list1 pp_expr e1 pp_block bk
  | While(e1,bk) -> F.fprintf fmt "While(%a,%a)" pp_expr e1 pp_block bk
  | Dfun(t,s,bk) -> F.fprintf fmt "Dfun(%a,%s,%a)" pp_type t s pp_block bk
  | Fun(e1,e2) -> F.fprintf fmt "Fun(%a,%a)" pp_expr e1 pp_expr e2
  | Return(e) -> F.fprintf fmt "Return(%a)" pp_expr e
  | Dstruct(s,bk) -> F.fprintf fmt "Dstruct(%s,%a)" s pp_block bk
  | UseIns1(e,s) -> F.fprintf fmt "UseIns1(%a,%s)" pp_expr e s
  | UseIns2(e1,e2) -> F.fprintf fmt "UseIns2(%a,%a)" pp_expr e1 pp_expr e2

(* block *)
and pp_block fmt (bk:Program.bk) =
  match bk with
  |Block elist -> F.fprintf fmt "Block([%a])" (pp_list0 pp_expr) elist

and pp_expr_patlist1 fmt (p,bk) = pp_tuple2 pp_pat pp_block fmt (p,bk)

(* environment *)
and pp_env fmt (env:Program.env) = pp_list0 (pp_tuple3 pp_string pp_type (pp_opt "Null" pp_value)) fmt env
         
(* type environment *)
and pp_tenv fmt (tenv:Program.tenv) = pp_list0 (pp_tuple2 pp_type pp_type) fmt tenv

(* type equals *)
and pp_tequals fmt (tequals:Program.tequals) = pp_list "" "\n" (pp_tuple2 pp_type pp_type) fmt tequals

(* other *)
let rec pp_evalResult fmt ((v,env,tenv) :Program.evalResult) =
  F.fprintf fmt "@[value: %a@." pp_value v;
  F.fprintf fmt "@[env: %a@." pp_env env;
  F.fprintf fmt "@[tenv: %a@." pp_tenv tenv

           
