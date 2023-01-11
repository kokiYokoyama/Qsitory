exception Error
exception Error1
exception Error2
exception Error3
exception Error4
exception Error5
exception NoValueError
exception NoSourcetoSubError
exception NoMatchPatternError
exception NotMatchExpressionError
exception OperateTypeError
open Syntax
open Tools
open Pprint
(* Expr_Eval-------------------------------------------------------------- *)

let rec expr_eval (e:Program.e) (env:Program.env) (tenv:Program.tenv) :Program.evalResult  =
  match e with
  |Int i -> (Int i,env,tenv)
  |Double d -> (Double d,env,tenv)
  |Bool b -> (Bool b,env,tenv)
  |String s -> (String s,env,tenv)
  |Var s -> (* print_env env; *) ((find env s),env,tenv)
  |Null -> (Null,env,tenv)
  |Nil -> (Nil,env,tenv)
  |Cons(e1,e2) ->
    begin
      match expr_eval e1 env tenv with
      |(v1,env1,tenv1) ->
        begin
          match expr_eval e2 env1 tenv1 with
          |(v2,env2,tenv2) -> (Cons(v1,v2),env2,tenv2)
        end
    end
  |Tuple list ->
    begin
      match expr_tuple_eval list env tenv with
      |vlist -> ((Tuple vlist),env,tenv)
    end
  |Declrt1(t,s,e) ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) -> (Null,((s,t,Some (v1))::(find_remove env1 s [])),tenv1)
    end
  |Declrt2(t,s) -> (Null,((s,t,None)::(find_remove env s [])),tenv)
  |Formu(p,e) ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) -> (* print_env env1; *)
        begin
          match patternMatch p v1 env1 with
          |Some env2 -> (Null,env2,tenv1)
          |None -> raise Error
        end
    end
  |Formu2(e1,e2) ->
    begin
      match expr_eval e2 env tenv with
      |(v1,env1,tenv1) ->
        begin
          match e1 with
          |UseIns1(e3,fi_n) ->
            begin
              match splitSF e1 [] with
              |(ins_n,fids) -> (Null,(updateFids ins_n fids v1 env1),tenv1)
            end
          |UseIns2(e3,e4) ->
            begin
              match splitSF2 e1 [] env tenv with
              |(ins_n,fids) -> (Null,(updateFids ins_n fids v1 env1),tenv1)
            end
          |_ -> raise Error
        end
    end
  |AOperate(aop,e1,e2) ->
    begin
      match expr_eval e2 env tenv with
      |(v1,env1,tenv1) ->
        begin
          try
            match expr_eval e1 env1 tenv1 with
            |(v2,env2,tenv2) -> (Null,(aOperate e1 v2 v1 aop env2),tenv2)
          with
          |NoValueError -> (Null,(aOperate e1 Null v1 aop env1),tenv1)
        end
    end
  |SubFormu(e,p) ->
    begin
      try
        match expr_eval e env tenv with
        |(v1,env1,tenv1) ->
          begin
            match expr_subFormu_eval e v1 p env with
            |env2 -> (Null,env2,tenv1)
          end
      with
      |NoValueError -> raise NoSourcetoSubError
    end
  |Operate(op,e1,e2) ->
    begin
      match expr_eval e1 env tenv with
      |(v1,env1,tenv1) ->
        begin
          match expr_eval e2 env1 tenv1 with
          |(v2,env2,tenv2) -> ((operate v1 v2 op),env2,tenv2)
        end
    end
  |Sub(e,p) ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) -> ((removeMatch v1 p env1),env1,tenv1)
    end
  |Not e ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) ->
        begin
          match v1 with
          |Bool true -> ((Bool false),env1,tenv1)
          |Bool false -> ((Bool true),env1,tenv1)
          |_ -> raise Error
        end
    end
  |If(e1,e2,e3) ->
    begin
      match expr_eval e1 env tenv with
      |(v1,env1,tenv1) ->
        begin
          match v1 with
          |Bool true -> expr_eval e2 env1 tenv1
          |Bool false -> expr_eval e3 env1 tenv1
          |_ -> raise Error
        end
    end
  |Match(e0,plist0) ->
    (* print_env env; *)
    begin
      match expr_eval e0 env tenv,plist0 with
      |(v1,env1,tenv1),(p,e)::[] ->
        (* print_env env1; *)
        begin
          match patternMatch p v1 env1 with
          |None -> raise NoMatchPatternError
          |Some env2-> expr_eval e env2 tenv1
        end
      |(v1,env1,tenv1),(p,e)::plist1 ->
        begin
          match patternMatch p v1 env1 with
          |None -> expr_eval (Match(e0,plist1)) env1 tenv1    
          |Some env2 -> expr_eval e env2 tenv1
        end
      |_,_->raise NotMatchExpressionError
    end
  |For(paraList,argList,e) ->
    begin
      match elist_to_vlist argList env tenv [] with
      |(vlist,env1,tenv1) ->
        begin
          match paraList,vlist with
          (* 全要素完了 *)
          |[],[] -> expr_eval e env1 tenv1
          |s::paraList1,(Cons(v1,v2))::vlist1 -> (* print_value (Cons(v1,v2)); *)
            begin
              (* 2要素目 *)
              match expr_secondFor_eval paraList1 vlist1 e ((s,(Any:Program.t),Some (v1))::(find_remove env1 s [])) tenv1 with
              |(v2,env2,tenv2) ->
                begin
                  (* 2周目以降 *)
                  match removeConsHd vlist [] with
                  |vlist2 ->
                    begin
                      match check_vlist vlist2 with
                      |true ->
                        begin
                          (* ループ終了 *)
                          match removeEnv env2 paraList with
                          |env3 -> (Null,env3,tenv2)
                        end
                      |false -> expr_roopFor_eval paraList vlist2 e env2 tenv2
                    end
                end
            end
          |s::paraList1,(Nil)::vlist1 -> expr_secondFor_eval paraList1 vlist1 e ((s,Any,None)::(find_remove env s [])) tenv
          |_ -> raise Error
        end
    end
  |For_dict(paraList,dict,e) ->
    begin
      match expr_eval dict env tenv with
      |(v1,env1,tenv1) ->
        begin
          match v1 with
          |Cons(v2,Nil)->
            begin
              match get_dict_item paraList v2 env with
              |env2 -> expr_eval e env2 tenv1
            end
          |Cons(v2,v3) ->
            begin
              match get_dict_item paraList v2 env with
              |env2 ->
                begin
                  match expr_eval e env2 tenv1 with
                  |(v4,env3,tenv2) ->
                    begin
                      match expr_roopFor_dict_eval paraList v3 e env3 tenv2 with
                      |(v5,env4,tenv3) ->
                        begin
                          match removeEnv env4 paraList with
                          |env5 -> (Null,env5,tenv3)
                        end
                    end
                end
            end                       
          |_ -> raise Error
        end
    end
   
  |While(e1,e2) ->
    begin
      match expr_eval e1 env tenv with
      |(v1,env1,tenv1) ->
        begin
          match v1 with
          |Bool true ->
            begin
              match expr_eval e2 env1 tenv1 with
              |(v2,env2,tenv2) -> expr_eval (While(e1,e2)) env2 tenv2
            end
          |Bool false -> expr_eval e2 env1 tenv1
          |_ -> raise Error
        end
    end
  |Dfun(t,s,e) -> (FunClos(env,s,e),env,tenv)  (* dummy *)
  |Fun(e1,e2) ->
    begin
      match expr_eval e1 env tenv with
      |(v1,env1,tenv1) ->
        begin
          match v1 with
          |FunClos(env0,s,e0) ->
            begin
              match expr_eval e2 env1 tenv1 with
              |(v2,env2,tenv2) ->
                begin
                  match expr_eval e0 ((s,Any,(Some v2))::(env0@(find_fun env2 []))) tenv2 with
                  |(v3,env3,tenv3) ->
                    begin
                      try
                        begin
                          match find env3 "rv" with
                          |v4 -> (v4,env,tenv)
                        end
                      with
                      |NoValueError -> (v3,env,tenv)
                    end
                end
            end                    
          |_ -> raise Error
        end
    end
  |Return e ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) -> (Null,(("rv",Any,Some v1)::env1),tenv1)
    end
  |Dstruct(s,e) -> (Null,env,tenv)
  |MakeIns(s) -> (Struct(s,(makeStructEnv s tenv [])),env,tenv)
  |UseIns1(e,s) ->
    begin
      match expr_eval e env tenv with
      |(Struct(s1,structEnv),env1,tenv1) -> ((find structEnv s),env1,tenv1)
      |_ -> raise Error
    end
  |UseIns2(e1,e2) ->
    begin
      match expr_eval e1 env tenv with
      |((String s1),env1,tenv1) ->
        begin
          match expr_eval e2 env1 tenv1 with
          |((String s2),env2,tenv2) -> expr_eval (UseIns1(Var(s1),s2)) env2 tenv2
          |_ -> raise Error
        end
      |_ -> raise Error
    end
  |Block(elist) ->
    begin
      match elist with
      |e::[] ->
        begin
          try
            expr_eval e env tenv
          with
          |NoValueError -> (Null,env,tenv)
        end
      |e::elist1 ->
        begin
          try
            begin
              match expr_eval e env tenv with
              |(v1,env1,tenv1) ->
                begin
                  try
                    begin
                      match find env1 "rv" with
                      |v2 -> (v1,env1,tenv1)
                    end
                  with
                  |NoValueError -> expr_eval (Block(elist1)) env1 tenv1
                end
            end
          with
          |NoValueError -> expr_eval (Block(elist1)) env tenv
        end
      |_ -> raise Error
    end
              
      
   
   
(* eval's function!------------------------------------------------------- *)

and find (env:Program.env) (s:string) :Program.v =
  (* print_env env; *)
  match env with
  |(s1,t,Some (v))::env1 -> if String.equal s s1 then v else find env1 s
  |(s1,t,None)::env1 -> find env1 s 
  |[] -> raise NoValueError

and find_fun (env:Program.env) (fenv:Program.env) :Program.env =
  match env with
  |(s,t,v)::env1 ->
    begin
      match t with
      |Fun(t1,t2) -> find_fun env1 ((s,t,v)::fenv)
      |_ -> find_fun env1 fenv
    end
  |[] -> fenv

and find_remove (env:Program.env) (s:string) (fenv:Program.env) :Program.env =
  match env with
  |(s1,t,v)::env1 -> if String.equal s s1 then find_remove env1 s fenv else find_remove env1 s ((s1,t,v)::fenv)
  |[] -> fenv
              
and expr_tuple_eval (elist:Program.e list) (env:Program.env) (tenv:Program.tenv) :Program.v list =
  begin
    match elist with
    |e::[] ->
      begin
        match expr_eval e env tenv with
        |(v1,env1,tenv1) -> (v1::[])
      end
    |e::elist1 ->
      begin
        match expr_eval e env tenv with
        |(v1,env1,tenv1) ->
          begin
            match expr_tuple_eval elist1 env1 tenv1 with
            |vlist -> (v1::[])@vlist
          end
      end
    |_ -> raise Error
  end

and patternMatch (p:Program.p) (v:Program.v) (env:Program.env) :Program.patternop =
  (* print_value v; *)
  (* print_env env; *)
  match p,v  with
  (* パターンマッチ成功 *)
  |Int i1,Int i2 -> if i1==i2 then Some env else None
  |Double d1,Double d2 -> if d1==d2 then Some env else None
  |Bool b1,Bool b2 -> if b1==b2 then Some env else None
  |String s1,String s2 -> if String.equal s1 s2 then Some env else None
  |Var s,v -> Some ((s,(find_type env s),Some v)::(find_remove env s []))
  |Nil,Nil -> Some env
  |Wild,v -> Some env
  |Cons(p1,p2),Cons(v1,v2) ->
    begin
      match patternMatch p1 v1 env with
      |Some env1 -> patternMatch p2 v2 env1
      |None -> None
    end
  |Tuple plist,Tuple vlist ->
    begin
      match plist,vlist with
      |p1::[],v1::[] -> patternMatch p1 v1 env
      |p1::plist1,v1::vlist1 ->
         begin
           match patternMatch p1 v1 env with
           |Some env1 -> patternMatch (Tuple plist1) (Tuple vlist1) env1
           |None -> raise Error
         end
      |_ -> raise Error
    end
  (* パターンマッチ失敗 *)
  |_,_-> None

and splitSF (e:Program.e) (fids:string list)  =
  match e with 
  |UseIns1(e1,f_n) -> splitSF e1 (f_n::fids)
  |Var ins_n -> (ins_n,fids)
  |_ -> raise Error

and splitSF2 (e:Program.e) (fids:string list) (env:Program.env) (tenv:Program.tenv) =
  match e with
  |UseIns2(e1,e2) ->
    begin
      match expr_eval e2 env tenv with
      |String f_n,env1,tenv1 -> splitSF2 e1 (f_n::fids) env1 tenv1
      |_ -> raise Error
    end
  |_ ->
    begin
      match expr_eval e env tenv with
      |String ins_n,env1,tenv1 -> (ins_n,fids)
      |_ -> raise Error
    end

and updateFids (ins_n:string) (fids:string list) (v:Program.v) (env:Program.env) :Program.env =
  match find env ins_n with
  |Struct(st_n,field) ->
    begin
      match fids with
      |fi_n::[] -> (ins_n,(find_type env ins_n),Some (Struct(st_n,((fi_n,(find_type field fi_n),Some v)::(find_remove field fi_n [] )))))::(find_remove env ins_n [])
      |fi_n::fids1 ->
        begin
          match updateFids fi_n fids1 v field with
          |field1 -> ((ins_n,(find_type env ins_n),Some (Struct(st_n,field1)))::(find_remove env ins_n []))
        end
      |_ -> raise Error
    end
  |_ -> raise Error

and aOperate (e:Program.e) (v1:Program.v) (v2:Program.v) (aop:Program.aop) (env:Program.env) :Program.env =
  match e with
  |Var s ->
    begin
      match v1 with
      |Null -> ((s,(find_type env s),Some v2)::(find_remove env s []))
      |_ -> ((s,(find_type env s),Some (operate v1 v2 (changeaop_to_op aop)))::(find_remove env s []))
    end
  |_ -> raise Error

and changeaop_to_op (aop:Program.aop) :Program.op =
  match aop with
  |Add -> Add
  |Sub -> Sub
  |Mul -> Mul
  |Div -> Div
  |_ -> raise Error
and operate (v1:Program.v) (v2:Program.v) (op:Program.op) :Program.v =
  match op with
  |Add ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Int (i1+i2)
      |Int i,Double d -> Double (Float.add (Int.to_float i) d)
      |Int i,String s -> String ((Int.to_string i)^s)
      |Double d1,Double d2 -> Double (Float.add d1 d2)
      |Double d,Int i -> Double (Float.add d (Int.to_float i))
      |Double d,String s -> String ((Float.to_string d)^s)
      |String s1,String s2 -> String (s1^s2)
      |String s,Int i -> String (s^(Int.to_string i))
      |String s,Double d -> String (s^(Float.to_string d))
      |Cons(v3,v4),v5 -> bindCons ((Cons(v3,v4):Program.v)) v5
      |Nil,v3 -> Cons(v3,Nil)
      |Tuple list1,v3 -> Tuple (v3::list1)
      |_ -> raise Error
    end
  |Sub ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Int (i1-i2)
      |Int i,Double d -> Double (Float.sub (Int.to_float i) d)
      |Double d1,Double d2 -> Double (Float.sub d1 d2)
      |Double d,Int i -> Double (Float.sub d (Int.to_float i))
      |_ -> raise Error
    end
  |Mul ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Int (i1*i2)
      |Int i,Double d -> Double (Float.mul (Int.to_float i) d)
      |Double d1,Double d2 -> Double (Float.mul d1 d2)
      |Double d,Int i -> Double (Float.mul d (Int.to_float i))
      |_ -> raise Error
    end
  |Div ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Int (i1/i2)
      |Int i,Double d -> Double (Float.div (Int.to_float i) d)
      |Double d1,Double d2 -> Double (Float.div d1 d2)
      |Double d,Int i -> Double (Float.div d (Int.to_float i))
      |_ -> raise Error
    end
  |Mod ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Int (i1 mod i2)
      |_ -> raise Error
    end
  |Lt ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Bool (i1<i2)
      |Int i,Double d -> Bool ((Int.to_float i)<d)
      |Double d1,Double d2 -> Bool (d1<d2)
      |Double d,Int i -> Bool (d<(Int.to_float i))
      |_ -> raise Error
    end
  |LtEq ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Bool (i1<=i2)
      |Int i,Double d -> Bool ((Int.to_float i)<=d)
      |Double d1,Double d2 -> Bool (d1<=d2)
      |Double d,Int i -> Bool (d<=(Int.to_float i))
      |_ -> raise Error
    end
  |Gt ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Bool (i1>i2)
      |Int i,Double d -> Bool ((Int.to_float i)>d)
      |Double d1,Double d2 -> Bool (d1>d2)
      |Double d,Int i -> Bool (d>(Int.to_float i))
      |_ -> raise Error
    end
  |GtEq ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Bool (i1>=i2)
      |Int i,Double d -> Bool ((Int.to_float i)>=d)
      |Double d1,Double d2 -> Bool (d1>=d2)
      |Double d,Int i -> Bool (d>=(Int.to_float i))
      |_ -> raise Error
    end
  |CEq ->
    begin
      match v1,v2 with
      |Int i1,Int i2 -> Bool (i1==i2)
      |Int i,Double d -> Bool ((Int.to_float i)==d)
      |Double d1,Double d2 -> Bool (d1==d2)
      |Double d,Int i -> Bool (d==(Int.to_float i))
      |String s1,String s2 -> Bool (String.equal s1 s2)
      |_ -> raise Error
    end
  |And ->
    begin
      match v1,v2 with
      |Bool b1,Bool b2 -> Bool (b1 && b2)
      |_,_ -> raise Error
    end
  |Or ->
    begin
      match v1,v2 with
      |Bool b1,Bool b2 -> Bool (b1 || b2)
      |_,_ -> raise Error
    end
  |_ -> raise Error

and bindCons (v1:Program.v) (v2:Program.v) :Program.v =
  match v1 with
  |Cons(v3,v4) -> Cons(v3,(bindCons v4 v2))
  |Nil ->
    begin
      match v2 with
      |Cons(v3,v4) -> v2
      |_ -> Cons(v2,Nil)
    end
  |_ -> raise Error

and expr_subFormu_eval (e:Program.e) (v:Program.v) (p:Program.p) (env:Program.env) :Program.env =
  match e with
  |Var s -> ((s,(find_type env s),Some (removeMatch v p env))::(find_remove env s []))
  |_ -> raise Error

and removeMatch (v:Program.v) (p:Program.p) (env:Program.env) :Program.v =
  match v,p with
  |Int i1,Int i2 -> if i1==i2 then Bool true else Bool false
  |Double d1,Double d2 -> if d1==d2 then Bool true else Bool false
  |String s1,String s2 -> if String.equal s1 s2 then Bool true else Bool false
  |v,Var s1 -> removeMatch v (ch_value_pat (find env s1)) env
  |Nil,Nil -> Bool true
  |v,Wild -> Bool true
  |Cons(v1,v2),p ->
    begin
      match removeMatch v1 p env with
      |Bool true ->
        begin
          match removeMatch v2 p env with
          |Bool true -> Nil
          |Bool false -> v2
          |v3 -> v3
        end
      |Bool false ->
        begin
          match removeMatch v2 p env with
          |Bool true -> Nil
          |Bool false -> Cons(v1,v2)
          |v3 -> Cons(v1,v3)
        end
      |_ -> raise Error
    end
  |Tuple vlist,Tuple plist ->
    begin
      match vlist,plist with
      |v1::[],p1::[] -> removeMatch v1 p1 env
      |v1::vlist1,p1::plist1 ->
        begin
          match removeMatch v1 p1 env with
          |Bool true -> removeMatch (Tuple vlist1) (Tuple plist1) env
          |Bool false -> Bool false
          |_ -> raise Error
        end
      |_ -> raise Error
    end
  |_,_ -> Bool false

and ch_value_pat (v:Program.v) :Program.p =
  match v with
  |Int i -> Int i
  |Double d -> Double d
  |Bool b -> Bool b
  |String s -> String s
  |Nil -> Nil
  |Cons(v1,v2) -> Cons((ch_value_pat v1),(ch_value_pat v2))
  |Tuple vlist -> Tuple (ch_tuple_vp vlist)
  |_ -> raise Error

and ch_tuple_vp (vlist:Program.v list) :(Program.p list) =
  match vlist with
  |v::[] -> ((ch_value_pat v)::[])
  |v::vlist1 ->
    begin
      match ch_value_pat v with
      |p ->
        begin
          match ch_tuple_vp vlist1 with
          |plist -> (p::plist)
        end
    end
  |_ -> raise Error

and elist_to_vlist (argList:Program.e list) (env:Program.env) (tenv:Program.tenv) (vlist:Program.v list) :(Program.v list * Program.env * Program.tenv) =
  match argList with
  |e::argList1 ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) -> elist_to_vlist argList1 env1 tenv1 (v1::vlist)
    end
  |[] ->(List.rev (vlist),env,tenv)
      
and check_vlist (vlist:Program.v list) :bool =
  match vlist with
  |(Cons(v1,v2))::vlist1 -> false
  |(Nil)::vlist1 -> check_vlist vlist1
  |[] -> true
  |_ -> raise Error
       
and removeEnv (env:Program.env) (paraList:string list) :Program.env =
  match paraList with
  |s::[] -> find_remove env s []
  |s::paraList1 -> removeEnv (find_remove env s []) paraList1
  |_ -> raise Error
  
and removeConsHd (vlist:Program.v list) (fvlist:Program.v list) :(Program.v list) =
  match vlist with
  |(Cons(v1,v2))::vlist1 -> removeConsHd vlist1 (v2::fvlist)
  |(Nil)::vlist1 -> removeConsHd vlist1 ((Nil)::fvlist)
  |[] -> List.rev fvlist
  |_ -> raise Error

and expr_secondFor_eval (paraList:string list) (vlist:Program.v list) (e:Program.e) (env:Program.env) (tenv:Program.tenv) :Program.evalResult =
  match paraList,vlist with
  (* 全要素完了 *)
  |[],[] -> expr_eval e env tenv
  |s::paraList1,(Cons(v1,v2))::vlist1 -> expr_secondFor_eval paraList1 vlist1 e ((s,(find_type env s),Some v1)::(find_remove env s [])) tenv 

  |s::paraList1,(Nil)::vlist1 -> expr_secondFor_eval paraList1 vlist1 e ((s,(find_type env s),None)::(find_remove env s [])) tenv
  |_ -> raise Error

and expr_roopFor_eval (paraList:string list) (vlist:Program.v list) (e:Program.e) (env:Program.env) (tenv:Program.tenv) :Program.evalResult =
  match paraList,vlist with
  (* 全要素完了 *)
  |[],[] -> expr_eval e env tenv
  |s::paraList1,(Cons(v1,v2))::vlist1 ->
    begin
      (* 2要素目 *)
      match expr_secondFor_eval paraList1 vlist1 e ((s,(find_type env s),Some v1)::(find_remove env s [])) tenv with
      |(v2,env2,tenv2) ->
        begin
          (* 2周目以降 *)
          match removeConsHd vlist [] with
          |vlist2 ->
            begin
              match check_vlist vlist2 with
              |true ->
                begin
                  (* ループ終了 *)
                  match removeEnv env2 paraList with
                  |env3 -> (Null,env3,tenv2)
                end
              |false -> expr_roopFor_eval paraList vlist2 e env2 tenv2
            end
        end
    end
  |s::paraList1,(Nil)::vlist1 -> expr_secondFor_eval paraList1 vlist1 e ((s,(find_type env s),None)::(find_remove env s [])) tenv
  |_ -> raise Error

and expr_roopFor_dict_eval (paraList:string list) (v:Program.v) (e:Program.e) (env:Program.env) (tenv:Program.tenv) =
  match v with
  |Cons(v1,Nil)->
    begin
      match get_dict_item paraList v1 env with
      |env1 -> expr_eval e env1 tenv
    end
  |Cons(v1,v2) ->
    begin
      match get_dict_item paraList v1 env with
      |env1 ->
        begin
          match expr_eval e env1 tenv with
          |(v2,env2,tenv1) -> expr_roopFor_dict_eval paraList v2 e env2 tenv1
        end
    end                       
  |_ -> raise Error

and get_dict_item (paraList:string list) (tuple:Program.v) (env:Program.env) :Program.env =
  match paraList,tuple with
  |[],Tuple ([]) ->env
  |s::paraList1,Tuple (v::vlist1) -> get_dict_item paraList1 (Tuple (vlist1)) ((s,(find_type env s),Some v)::(find_remove env s [])) 
  |_ -> raise Error

and makeStructEnv (s:string) (tenv:Program.tenv) (flist:Program.env) :Program.env =
  match List.assoc (MT(s):Program.t) tenv  with
  |Struct(list) -> findMyType tenv list flist
  |_ -> raise Error

and findMyType (tenv:Program.tenv) (list:Program.env) (flist:Program.env) =
  match list with
  |(s,t,v)::list1 ->
    begin
      match t with
      |T(s1) ->
        begin
          match makeStructEnv s tenv flist with
          |flist2 -> findMyType tenv list1 ((s,t,Some (Struct(s1,flist2)))::flist)
        end
      |_ -> findMyType tenv list1 ((s,t,v)::flist)
    end                                            
  |[] -> flist

(* Expr_Tval-------------------------------------------------------------- *)

(* 一つの構文における
 * T0 -> t tn
 * T1 -> t (tn+1)         
 * T2 -> t (tn+2) *)

and t (tn:int) :Program.t = T ("T" ^ string_of_int(tn))

and expr_tval (e:Program.e) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) :Program.tvalResult =
  (* Format.printf "@[%a: (%a)@." pp_expr e pp_type (t n); *)
  match e with
  |Int i -> (env,tenv,(((t n),Int)::tequals),n)
  |Double d -> (env,tenv,(((t n),Double)::tequals),n)
  |Bool b -> (env,tenv,(((t n),Bool)::tequals),n)
  |String s -> (env,tenv,(((t n),String)::tequals),n)
  |Var s -> (env,tenv,(((t n),(find_type env s))::tequals),n)
  |Null -> (env,tenv,(((t n),(t (n+1)))::tequals),n+1)
  |Nil -> (env,tenv,(((t n),(List(t (n+1))))::tequals),n+1)
  |Cons(e1,e2) ->
    begin
      match expr_tval e1 env tenv (((t n),List (t (n+1)))::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) -> expr_tval e2 env1 tenv1 (((t (n1+1)),(t n))::tequals1) (n1+1)
    end
  |Tuple list ->
    begin
      match expr_tuple_tval list env tenv tequals n with
      |(tlist,tequals1,n1) -> (env,tenv,(((t n),(Tuple tlist))::tequals1),n1)
    end
  |Declrt1(t1,s,e) -> expr_tval e ((s,t1,None)::(find_remove env s [])) tenv (((t (n+1)),t1)::((t n),Unit)::tequals) (n+1)
  |Declrt2(t1,s) -> (((s,t1,None)::(find_remove env s [])),tenv,((t (n+1),t1)::((t n),Unit)::tequals),n)
  |Formu(p,e) ->
    begin
      match e with
      |Nil ->
        begin
          match expr_tval e env tenv ((t (n+2),Any)::((t n),Unit)::tequals) (n+1) with
          |(env1,tenv1,tequals1,n1) ->
            begin
              match makeEnvFormu p (n+1) env1 tequals1 with
              |(env2,n2) -> (env2,tenv1,tequals1,n1)
            end
        end
      |_ ->
        begin
          match expr_tval e env tenv (((t n),Unit)::tequals) (n+1) with
          |(env1,tenv1,tequals1,n1) ->
            (* Format.printf "%i" n1; *)
            (* print_tequals tequals1; *)
            begin
              match makeEnvFormu p (n+1) env1 tequals1 with
              |(env2,n2) ->
                (* Format.printf "%i" n2; *)
                (env2,tenv1,tequals1,n1)
            end
        end
    end
  |Formu2(e1,e2) ->
    begin
      match expr_tval e2 env tenv (((t n),Unit)::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match e1 with
          |UseIns1(e3,fi_n) ->
            begin
              match splitSF e1 [] with
              |(ins_n,fids) -> ((updateFids_tval ins_n fids (n+1) env1 tenv1),tenv1,tequals1,n1)
            end
          |UseIns2(e3,e4) ->
            begin
              match splitSF2 e1 [] env tenv with
              |(ins_n,fids) -> ((updateFids_tval ins_n fids (n+1) env1 tenv1),tenv1,tequals1,n1)
            end
          |_ -> raise Error
        end
    end
  |AOperate(aop,e1,e2) -> 
    begin
      match expr_tval e2 env tenv (((t n),Unit)::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) -> 
        begin
          try
            match expr_tval e1 env1 tenv1 tequals1 (n1+1) with
            |(env2,tenv2,tequals2,n2) -> ((aOperateType e1 (n1+1) (n+1) aop env2 tequals2),tenv2,tequals2,n2)
          with
          |NoValueError -> ((aOperateType e1 (n1+1) (n+1) Eq env1 tequals1),tenv1,tequals1,n1)
        end
    end
  |SubFormu(e,p) ->
    begin
      match expr_tval e env tenv (((t n),Unit)::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match pat_tval p env1 tenv1 tequals1 (n1+1) with
          |(env2,tenv2,tequals2,n2) ->
            begin
              match e with
              |Var s -> (((s,(operateType (n+1) (n1+1) (Sub2:Program.op) tequals2),(find_op env2 s))::(find_remove env2 s [])),tenv2,tequals2,n2)
              |_ -> raise Error
            end
        end
    end
  |Operate(op,e1,e2) -> 
    begin
      match expr_tval e1 env tenv tequals (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match expr_tval e2 env1 tenv1 tequals1 (n1+1) with
          |(env2,tenv2,tequals2,n2) -> (env2,tenv2,(((t n),(operateType (n+1) (n1+1) op tequals2))::tequals2),n2)
        end
    end
  |Sub(e,p) ->
    begin
      match expr_tval e env tenv tequals (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match pat_tval p env1 tenv1 tequals1 (n1+1) with
          |(env2,tenv2,tequals2,n2) -> (env2,tenv2,(((t n),(operateType (n+1) (n1+1) (Sub2:Program.op) tequals2))::tequals2),n2)
        end
    end
  |Not e -> expr_tval e env tenv (((t (n+1)),Bool)::((t n),Bool)::tequals) (n+1)
  |If(e1,e2,e3) ->
    begin
      match expr_tval e1 env tenv (((t (n+1)),Bool)::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match expr_tval e2 env1 tenv1 (((t (n1+1)),(t n))::tequals1) (n1+1) with
          |(env2,tenv2,tequals2,n2) -> expr_tval e3 env2 tenv2 (((t (n2+1)),(t n))::tequals2) (n2+1)
        end
    end
  |Match(e,patlist) ->
    begin
      match expr_tval e env tenv tequals (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match patlist with
          |(p,e1)::[] ->
            begin
              match makeEnvMatch p (t (n+1)) env1 tequals1 with
              |env11->
                begin
                  match pat_tval p env11 tenv1 tequals1 (n1+1) with
                  |(env2,tenv2,tequals2,n2) -> expr_tval e1 env2 tenv2 (((t n),(t (n2+1)))::tequals2) (n2+1)
                end
            end
          |(p,e1)::patlist1 ->
            begin
              match makeEnvMatch p (t (n+1)) env1 tequals1 with
              |env11 ->
                begin
                  match pat_tval p env11 tenv1 tequals1 (n1+1) with
                  |(env2,tenv2,tequals2,n2) ->
                    begin
                      match expr_tval e1 env2 tenv2 (((t n),(t (n2+1)))::tequals2) (n2+1) with
                      |(env3,tenv3,tequals3,n3) -> secondMatch_tval patlist1 env3 tenv3 tequals3 n3 (n+1) (n2+1)
                    end
                end
            end
          |_ -> raise Error
        end
    end
  |For(paraList,argList,e) ->
    begin
      match paraList,argList with
      |[],[] -> (env,tenv,tequals,n)
      |s1::paraList1,e1::argList1 ->
        begin
          match expr_tval e1 env tenv (((t (n+1)),List(t (n+2)))::((t n),Unit)::tequals) (n+1) with
          |(env1,tenv1,tequals1,n1) ->   
            begin
              match makeEnvMatch (Cons(Var(s1),Nil)) (t (n+1)) env1 tequals1 with
              |env2 ->
                begin
                  (* 2要素目以降 *)
                  match secondFor_tval paraList1 argList1 env2 tenv1 tequals1 (n1+1) with
                  |(env3,tenv2,tequals2,n2) -> expr_tval e env3 tenv2 tequals2 (n2+1)
                end
            end
        end
      |_ -> raise Error
    end
  |For_dict(paraList,dict,e) ->
    begin
      match paraList,dict with
      |s1::paraList1,Cons(e1,e2) ->
        begin
          match e1 with
          |Tuple elist ->
            begin
              match List.map dict_tval elist with
              |t1::tlist1 ->
                begin
                  match makeEnvMatch (Var(s1)) t1 env tequals with
                  |env1 ->
                    (* 2要素目以降 *)
                    match secondForDict_tval paraList1 tlist1 env1 tequals with
                    |env2 ->
                      begin
                        match expr_tval e env2 tenv (((t n),Unit)::tequals) (n+1) with
                        |(env3,tenv2,tequals2,n2) ->
                          begin
                            match e2 with
                            |Nil ->(env,tenv,tequals2,n2)
                            |_ -> expr_tval (For_dict(paraList,e2,e)) env3 tenv2 tequals2 (n2+1)
                          end
                      end
                end
              |_ -> raise Error
            end
          |_ -> raise Error
        end
      |s1::paraList1,Var(s) ->
        begin
          match expr_tval (Var(s)) env tenv tequals (n+1) with
          |(env1,tenv1,tequals1,n1) ->
            begin
              match find_type_tequals (t (n+1)) tequals1 with
              |List(Tuple(tlist)) ->
                begin
                  match tlist with
                  |t1::tlist1 -> 
                    begin
                      match makeEnvMatch (Var(s1)) t1 env1 tequals1 with
                      |env2 ->
                        (* 2要素目以降 *)
                        begin
                          match secondForDict_tval paraList1 tlist1 env2 tequals with
                          |env3 ->  expr_tval e env3 tenv1 (((t n),Unit)::tequals1) (n1+1)
                        end
                    end
                  |_ -> raise Error
                end
              |_ -> raise Error
            end         
        end
      |_ -> raise Error
    end
  |While(e1,e2) ->
    begin
      match expr_tval e1 env tenv (((t (n+1)),Bool)::((t n),Unit)::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) -> expr_tval e2 env1 tenv1 tequals1 (n1+1)
    end
  |Dfun(tp,s,e) ->
    let env1 = (s,tp,None)::env in
    let tequals1 = [(t(n+4),t(n+2)); (t(n+1),tp); (t(n+3),t(n+1)); (t n,Fun(t(n+1),t(n+2)))] @ tequals in
    expr_tval e env1 tenv tequals1 (n+4)    
  |Fun(e1,e2) ->
    begin
      match expr_tval e2 env tenv tequals (n+1) with
      |(env2,tenv2,tequals2,n2) -> expr_tval e1 env2 tenv2 ((t (n2+1), Fun(t (n+1), t n))::tequals2) (n2+1)
    end
(*    
    begin
      match expr_tval e1 env tenv ((t (n+1),Fun(t (n+2),t n))::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) -> expr_tval e2 env1 tenv1 ((t (n+2),t (n1+1))::tequals1) (n1+1)
    end
 *)
  |Return e ->
    let (env1,tenv1,tequals1,n1) = expr_tval e env tenv (((t n),Unit)::tequals) (n+1) in
    let t1 = find_type_tequals (t (n+1)) tequals1 in
    ((("rv",t1,None)::(find_remove env1 "rv" [])),tenv1,tequals1,n1)

  |Dstruct(s,e) ->
    let structData = makeStructTenv e in
    (env,(((MT s),Struct(structData))::tenv),(((t n),Unit)::tequals),n)
  |MakeIns(s) -> (env,tenv,(((t n),(MT s))::tequals),n)
  |UseIns1(e1,s) ->
    let (env1,tenv1,tequals1,n1) = expr_tval e1 env tenv tequals (n+1) in
    let structEnv = find_structEnv tenv1 tequals1 (n+1) in
    let t1 = find_type structEnv s in
    (env1,tenv1,(((t n),t1)::tequals1),n1)
    (*
    begin
      match expr_tval e1 env tenv tequals (n+1) with
      |(env1,tenv1,tequals1,n1) -> (* print_env env1; *) 
        begin
          match find_structEnv tenv1 tequals1 (n+1) with
          |structEnv -> (* print_env structEnv; *)
            begin
              match find_type structEnv s with
              |t1 -> (env1,tenv1,(((t n),t1)::tequals1),n1)
            end
        end
    end*)
    
  |UseIns2(e1,e2) ->
    begin
      match expr_tval e1 env tenv (((t (n+1)),String)::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match expr_tval e2 env1 tenv1 (((t (n1+1)),String)::tequals1) (n1+1) with
          |(env2,tenv2,tequals2,n2) ->
            begin
              match expr_eval e1 env tenv with
              |(String(s1),env3,tenv3) ->
                begin
                  match expr_eval e2 env3 tenv3 with
                  |(String(s2),env4,tenv4) ->
                    (* Format.printf "%s" (split_dp s1); *)
                    expr_tval (UseIns1(Var(split_dp s1),s2)) env2 tenv2 (((t n),(t n2))::tequals2) n2
                  |_ -> raise Error
                end
              |_ -> raise Error
            end
        end
    end
  |Block(elist) ->
    (*
    Format.printf "@[==========================@.";
    Format.printf "@[%a@." Pprint.pp_env env;
    Format.printf "@[=======@.";
    Format.printf "@[%a@." Pprint.pp_tequals tequals;
    Format.printf "@[=======@.";
    Format.printf "@[%a@." Pprint.pp_tequals tequals1;    
    Format.printf "@[==========================@.";
     *)
    begin
      match elist with
      | [] -> raise Error
      | e::elist1 ->
         let (env1,tenv1,tequals1,n1) = expr_tval e env tenv tequals (n+1) in
         begin
           match elist1 with
           | [] ->
              begin
                try 
                  let t1 = find_type env1 "rv" in
                  let env2 = find_remove env1 "rv" [] in
                  (env2,tenv1,(((t n),t1)::tequals1),n1)
                with
                | NoValueError -> (env1,tenv1,(((t n),t (n+1))::tequals1),n1)
              end
           | _ -> secondBlock_tval elist1 env1 tenv1 tequals1 n1 n
         end
    end
    
    

(* Pat_Tval--------------------------------------------------------------- *)

and pat_tval (p:Program.p) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) :Program.tvalResult =
  match p with
  |Int i -> (env,tenv,(((t n),Int)::tequals),n)
  |Double d -> (env,tenv,(((t n),Double)::tequals),n)
  |Bool b -> (env,tenv,(((t n),Bool)::tequals),n)
  |String s -> (env,tenv,(((t n),String)::tequals),n)
  |Var s -> (env,tenv,(((t n),(find_type env s))::tequals),n)
  |Nil -> (env,tenv,(((t n),(List (t (n+1))))::tequals),n)
  |Wild -> (env,tenv,(((t n),Any)::tequals),n)
  |Cons(p1,p2) ->
    begin
      match pat_tval p1 env tenv (((t n),List (t (n+1)))::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) -> pat_tval p2 env1 tenv1 (((t (n1+1)),(t n))::tequals1) (n1+1)
    end
  |Tuple list ->
    begin
      match pat_tuple_tval list env tenv tequals n with
      |(tlist,tequals1,n1) -> (env,tenv,(((t n),(Tuple tlist))::tequals1),n1)
    end
  
(* tval's function!------------------------------------------------------- *)
   
and find_op (env:Program.env) (s:string) :Program.v option =
  (* print_env env; *)
  match env with
  |(s1,t,v)::env1 -> if String.equal s s1 then v else find_op env1 s
  |[] -> None
      
and remove_list a list flist =
  match list with
  |a1::list1 -> if a1==a then remove_list a list flist else remove_list a list1 (a1::flist)
  |[] -> flist

and equal_type (t1:Program.t) (t2:Program.t) :bool =
  (* Format.printf "@[t1=%a\nt2=%a\n@." pp_type t1 pp_type t2; *)
  match t1,t2 with
  |T s1,T s2 when s1 = s2 -> true
  |Int,Int -> true
  |Double,Double -> true
  |Bool,Bool -> true
  |String,String -> true
  |t,Any -> true
  |Any,t -> true
  |Unit,Unit -> true
  |List t3,List t4 -> equal_type t3 t4
  |Tuple tlist1,Tuple tlist2 -> equal_type_tuple tlist1 tlist2
  |Fun(t1,t2),Fun(t3,t4) -> (equal_type t1 t3) && (equal_type t2 t4)
  |Struct(env1),Struct(env2) -> equal_type_env env1 env2
  |_ -> false
  
and equal_type_tuple (tlist1:Program.t list) (tlist2:Program.t list) :bool =
  match tlist1,tlist2 with
  |t1::[],t2::[] -> equal_type t1 t2
  |t1::tlist3,t2::tlist4 ->
    begin
      match equal_type t1 t2 with
      |true -> equal_type_tuple tlist3 tlist4
      |false -> false
    end
  |_ -> raise Error

and equal_type_env (env1:Program.env) (env2:Program.env) :bool =
  match env1,env2 with
  |(s1,t1,v1)::[],(s2,t2,v2)::[] when (s1=s2) -> equal_type t1 t2
  |(s1,t1,v1)::env3,(s2,t2,v2)::env4 when (s1=s2) ->
    begin
      match equal_type t1 t2 with
      |true -> equal_type_env env3 env4
      |false -> false
    end
  |_,_ -> raise Error

and find_type (env:Program.env) (s:string) :Program.t =
  match env with
  |(s1,t,v)::env1 ->
    if String.equal s s1 then t else find_type env1 s
  |[] -> raise NoValueError

and find_structEnv (tenv:Program.tenv) (tequals:Program.tequals) (n:int) :Program.env =
  match find_type_tequals (t n) tequals with
  |t1 -> (* Format.printf ("%a,%a") (fun _ -> print_type) t1 (fun _ -> print_tequals) tequals; *)
    begin
      match List.assoc t1 tenv with
      |Struct(structEnv) -> structEnv
      |_ -> raise Error
    end

and find_type_tequals (t:Program.t) (tequals:Program.tequals) :Program.t =
  (* print_tequals tequals; *)
  match find_type_tequals2 t tequals with
  |t2 -> (* print_type t2; *)
    begin
      match t2 with
      |List (T s2) -> List (find_type_tequals (find_type_tequals2 (T s2) tequals) tequals)
      |Tuple (tlist) -> Tuple(tuple_ftt tlist tequals)
      |_ -> t2
    end

and find_type_tequals2 (t:Program.t) (tequals:Program.tequals) :Program.t =
  match tequals with
  |(t1,t2)::tequals1 ->
    begin
      match t1,t with
      |T s1,T s2 -> (* Format.printf "(%s,%s)" s1 s2; *)
        begin
          match t2 with
          |T s -> (* print_type (T s); *) find_type_tequals2 t tequals1
          |_ -> if String.equal s1 s2 then t2 else find_type_tequals2 t tequals1
        end
      |T s1,_ -> t
      |_ -> raise Error
    end
  |[] -> t

and tuple_ftt (tlist:Program.t list) (tequals:Program.tequals) :Program.t list =
  List.map (fun t1 -> find_type_tequals t1 tequals) tlist

and expr_tuple_tval (elist:Program.e list) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) :(Program.t list * Program.tequals * int) = (* Format.printf "%i" n; *)
  begin
    match elist with
    |e::[] ->
      begin
        match expr_tval e env tenv tequals (n+1) with
        |(env1,tenv1,tequals1,n1) -> (((t (n+1))::[]),tequals1,n1)
      end
    |e::elist1 ->
      begin
        match expr_tval e env tenv tequals (n+1) with
        |(env1,tenv1,tequals1,n1) -> (* Format.printf "%i" n1; *)
          begin
            match expr_tuple_tval elist1 env1 tenv1 tequals1 n1 with
            |(tlist,tequals2,n2) -> (((t (n+1))::[])@tlist,tequals2,n2)
          end
      end
    |_ -> raise Error
  end

and pat_tuple_tval (plist:Program.p list) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) :(Program.t list * Program.tequals * int) =
  begin
    match plist with
    |p::[] ->
      begin
        match pat_tval p env tenv tequals (n+1) with
        |(env1,tenv1,tequals1,n1) -> (((t n1)::[]),tequals1,n1)
      end
    |p::plist1 ->
      begin
        match pat_tval p env tenv tequals (n+1) with
        |(env1,tenv1,tequals1,n1) ->
          begin
            match pat_tuple_tval plist1 env1 tenv1 tequals1 n1 with
            |(tlist,tequals2,n2) -> (((t n1)::[])@tlist,tequals2,n2)
          end
      end
    |_ -> raise Error
  end

and makeEnvFormu (p:Program.p) (n:int) (env:Program.env) (tequals:Program.tequals) :(Program.env * int) =
  (* Format.printf "%i" n; *)
  match p with
  |Var s -> (((s,(find_type_tequals (t n) tequals),(find_op env s))::(find_remove env s [])),n)
  |Cons(p1,p2) ->
    begin
      match makeEnvFormu p1 (n+1) env tequals with
      |(env1,n1) -> makeEnvFormu p2 (n1+1) env1 tequals
    end
  |Tuple plist ->
    begin
      match plist with
      |p1::[] -> makeEnvFormu p1 (n+1) env tequals 
      |p1::plist1 ->
        begin
          match makeEnvFormu p1 (n+1) env tequals  with
          |(env1,n1) -> makeEnvFormu (Tuple plist1) n1 env1 tequals
        end
      |_ -> raise Error
    end
  |_ -> (env,n)

and makeEnvMatch (p:Program.p) (t:Program.t) (env:Program.env) (tequals:Program.tequals) :Program.env =
  match find_type_tequals t tequals with
  |t1 ->
    begin
      match p,t1 with
      |Cons(p1,p2),List(t2) ->
        begin
          match makeEnvMatch2 p1 t2 env with
          |env1 -> makeEnvMatch2 p2 t1 env1
        end
      |Tuple(plist),Tuple(tlist) ->
        begin
          match plist,tlist with
          |p1::[],t2::[] -> makeEnvMatch2 p1 t2 env
          |p1::plist1,t2::tlist1 ->
            begin
              match makeEnvMatch2 p1 t2 env with
              |env1 -> makeEnvMatch2 (Tuple(plist1)) (Tuple(tlist1)) env1
            end
          |_ -> raise Error
        end
        
      |_ -> makeEnvMatch2 p t1 env
    end

and makeEnvMatch2 (p:Program.p) (t:Program.t) (env:Program.env) :Program.env =
  match p with
  |Var s -> ((s,t,(find_op env s))::(find_remove env s []))
  |Cons(p1,p2) ->
    begin
      match t with
      |List(t2) ->
        begin
          match makeEnvMatch2 p1 t2 env with
          |env1 -> makeEnvMatch2 p2 t env1
        end
      |_ -> raise Error
    end
  |Tuple(plist) ->
    begin
      match t with
      |Tuple(tlist) ->
        begin
          match plist,tlist with
          |p1::[],t2::[] -> makeEnvMatch2 p1 t2 env
          |p1::plist1,t2::tlist1 ->
            begin 
              match makeEnvMatch2 p1 t2 env with
              |env1 -> makeEnvMatch2 (Tuple(plist1)) (Tuple(tlist1)) env1
            end
          |_ -> raise Error
        end
      |_ -> raise Error
    end
  |_ -> env
          
(* and updateFids_tval (ins_n:string) (fids:string list) (n:int) (env:Program.env) :Program.env =
 *   match find env ins_n with
 *   |Struct(st_n,field) ->
 *     begin
 *       match fids with
 *       |fi_n::[] -> (ins_n,(T st_n),Some (Struct(st_n,((fi_n,(t n),None)::(find_remove field fi_n [] )))))::(find_remove env ins_n [])
 *       |fi_n::fids1 ->
 *         begin
 *           match updateFids_tval fi_n fids1 n field with
 *           |field1 -> ((ins_n,(T st_n),Some (Struct(st_n,field1)))::(find_remove env ins_n []))
 *         end
 *       |_ -> raise Error
 *     end
 *   |_ -> raise Error *)

and updateFids_tval (ins_n:string) (fids:string list) (n:int) (env:Program.env) (tenv:Program.tenv) :Program.env =
  match find_type env ins_n with
  |MT s ->
    begin
      match List.assoc ((MT(s)):Program.t) tenv with
      |Struct(structEnv) ->
        begin
          match fids with
          |fi_n::[] -> (ins_n,(MT s),Some (Struct(s,((fi_n,(find_type structEnv fi_n ),(find_op structEnv fi_n))::(find_remove structEnv fi_n [])))))::(find_remove env ins_n [])
          |fi_n::fids1 ->
            begin
              match updateFids_tval fi_n fids1 n structEnv tenv with
              |field1 -> ((ins_n,(MT s),Some (Struct(s,field1)))::(find_remove structEnv ins_n []))
            end
          |_ -> raise Error
        end
      |_ -> raise Error
    end
  |_ ->raise Error
        
and aOperateType (e:Program.e) (n1:int) (n2:int) (aop:Program.aop) (env:Program.env) (tequals:Program.tequals) :Program.env =
  match e with
  |Var s ->
    begin
      match aop with
      |Eq -> (s,(find_type_tequals (t n2) tequals),(find_op env s))::(find_remove env s [])
      |_ ->
        begin
          match operateType n1 n2 (changeaop_to_op aop) tequals with
          |t -> (s,t,(find_op env s))::(find_remove env s [])
        end
    end
  |_ -> raise Error


and operateType (n1:int) (n2:int) (op:Program.op) (tequals:Program.tequals) :Program.t =
  (* print_type (find_type_tequals (t n1) tequals);print_type (find_type_tequals (t n2) tequals); *)
  match op with
  |Add -> (* print_type (find_type_tequals (t n1) tequals);print_type (find_type_tequals (t n2) tequals); *)
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Int,Int -> Int
      |Int,Double -> Double
      |Int,String -> String
      |Double,Double -> Double
      |Double,Int -> Double
      |Double,String -> String
      |String,String -> String
      |String,Int -> String
      |String,Double -> String
      |List t1,List t2 when (equal_type t1 (find_type_tequals t2 tequals)) -> List (find_type_tequals t2 tequals)
      |List t1,t2 ->
        begin
          match t2 with
          |List t3 when (equal_type t1 (List (find_type_tequals t3 tequals))) -> List (List (find_type_tequals t3 tequals))
          |Tuple tlist when (equal_type t1 (Tuple (tuple_ftt tlist tequals))) -> List (Tuple (tuple_ftt tlist tequals))
                               
          |_ when (equal_type t1 (find_type_tequals t2 tequals)) -> List (find_type_tequals t2 tequals)
          |_ -> raise OperateTypeError
        end
      |Tuple tlist,t1 -> Tuple ((t n2)::tlist)
      |_ -> raise OperateTypeError
    end
  |Sub ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> t
      |t,Any -> t
      |Int,Int -> Int
      |Int,Double -> Double
      |Double,Double -> Double
      |Double,Int -> Double
      |_ -> raise OperateTypeError
    end
  |Mul ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> t
      |t,Any -> t
      |Int,Int -> Int
      |Int,Double -> Double
      |Double,Double -> Double
      |Double,Int -> Double
      |_ -> raise OperateTypeError
    end
  |Div ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> t
      |t,Any -> t
      |Int,Int -> Int
      |Int,Double -> Double
      |Double,Double -> Double
      |Double,Int -> Double
      |_ -> raise OperateTypeError
    end
  |Mod ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> t
      |t,Any -> t
      |Int,Int -> Int
      |_ -> raise OperateTypeError
    end
  |Lt -> (* print_type (find_type_tequals (t n1) tequals);print_type (find_type_tequals (t n2) tequals); *) 
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Int,Int -> Bool
      |Int,Double -> Bool
      |Double,Double -> Bool
      |Double,Int -> Bool
      |_ -> raise OperateTypeError
    end
  |LtEq ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Int,Int -> Bool
      |Int,Double -> Bool
      |Double,Double -> Bool
      |Double,Int -> Bool
      |_ -> raise OperateTypeError
    end
  |Gt ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Int,Int -> Bool
      |Int,Double -> Bool
      |Double,Double -> Bool
      |Double,Int -> Bool
      |_ -> raise OperateTypeError
    end
  |GtEq ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Int,Int -> Bool
      |Int,Double -> Bool
      |Double,Double -> Bool
      |Double,Int -> Bool
      |_ -> raise OperateTypeError
    end
  |CEq ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Int,Int -> Bool
      |Int,Double -> Bool
      |Double,Double -> Bool
      |Double,Int -> Bool
      |String,String -> Bool
      |_ -> raise OperateTypeError
    end
  |And ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Bool,Bool -> Bool
      |_ -> raise OperateTypeError
    end
  |Or ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> Bool
      |t,Any -> Bool
      |Bool,Bool -> Bool
      |_ -> raise OperateTypeError
    end
  |Sub2 ->
    begin
      match (find_type_tequals (t n1) tequals),(find_type_tequals (t n2) tequals) with
      |Any,t -> t
      |t,Any -> t
      |String,String -> String
      |String,Int -> String
      |String,Double -> String
      |List t1,List t2 when (equal_type t1 (find_type_tequals t2 tequals)) -> List (find_type_tequals t2 tequals)
      |List t1,t2 ->
        begin
          match t2 with
          |List t3 when (equal_type t1 (List (find_type_tequals t3 tequals))) -> List (List (find_type_tequals t3 tequals))
          |Tuple tlist when (equal_type t1 (Tuple (tuple_ftt tlist tequals))) -> List (Tuple (tuple_ftt tlist tequals))
                               
          |_ when (equal_type t1 (find_type_tequals t2 tequals)) -> List (find_type_tequals t2 tequals)
          |_ -> raise OperateTypeError
        end

      |Tuple tlist,t -> Tuple (remove_list t tlist [])
      |_ -> raise Error
    end

and secondBlock_tval (elist:Program.e list) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) (n0:int) :Program.tvalResult =
  match elist with
  | [] -> raise Error
  | e::[] ->
     let (env1,tenv1,tequals1,n1) = expr_tval e env tenv tequals (n+1) in
     begin
       try
         let t1 = find_type env1 "rv" in
         let env2 = find_remove env1 "rv" [] in
         (env2,tenv1,(((t n0),t1)::tequals1),n1)
       with
       | NoValueError -> (env1,tenv1,(((t n0),t (n+1))::tequals1),n1)
     end
  | e::elist1 ->
     let (env1,tenv1,tequals1,n1) = expr_tval e env tenv tequals (n+1) in
     secondBlock_tval elist1 env1 tenv1 tequals1 n1 n0

and secondMatch_tval (patlist:(Program.p * Program.e) list) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) (np:int) (ne:int) :Program.tvalResult =
  match patlist with
  |(p,e)::[] ->
    begin
      match makeEnvMatch p (t np) env tequals with
      |env01 ->
        begin
          match pat_tval p env01 tenv tequals (n+1) with
          |(env1,tenv1,tequals1,n1) -> expr_tval e env1 tenv1 (((t (n1+1)),(t ne))::tequals1) (n1+1)
        end
    end
  |(p,e)::patlist1 ->
    begin
      match makeEnvMatch p (t np) env tequals with
      |env01 ->
        begin
          match pat_tval p env01 tenv tequals (n+1) with
          |(env1,tenv1,tequals1,n1) ->
            begin
              match expr_tval e env1 tenv1 (((t (n1+1)),(t ne))::tequals1) (n1+1) with
              |(env2,tenv2,tequals2,n2) -> secondMatch_tval patlist1 env2 tenv2 tequals2 n2 np ne
            end
        end
    end
  |_ -> raise Error

and secondFor_tval (paraList:string list) (argList:Program.e list) (env:Program.env) (tenv:Program.tenv) (tequals:Program.tequals) (n:int) :Program.tvalResult =
  match paraList,argList with
  |[],[] -> (env,tenv,tequals,n) 
  |s1::paraList1,e1::argList1 ->
    begin
      match expr_tval e1 env tenv (((t (n+1)),List(t (n+2)))::tequals) (n+1) with
      |(env1,tenv1,tequals1,n1) ->
        begin
          match makeEnvMatch (Cons(Var(s1),Nil)) (t (n+1)) env1 tequals1 with
          |env2 -> secondFor_tval paraList1 argList1 env2 tenv1 tequals1 (n1+1)
        end
    end
  |_ -> raise Error

and dict_tval (e:Program.e) :Program.t =
  match expr_tval e [] [] [] 0 with
  |(env1,tenv1,tequals1,n1) -> find_type_tequals (t 0) tequals1

and secondForDict_tval (paraList:string list) (tlist:Program.t list) (env:Program.env) (tequals:Program.tequals) :Program.env =
  match paraList,tlist with
  |[],[] -> env
  |s1::paraList1,t1::tlist1 ->
    begin
      match makeEnvMatch (Var(s1)) t1 env tequals with
      |env1 -> secondForDict_tval paraList1 tlist1 env1 tequals
    end
  |_ -> raise Error

and makeStructTenv (e:Program.e) :Program.env =
  match expr_eval e [] [] with
  |(v,env,tenv) -> env
;;

(* Unif------------------------------------------------------------------- *)

let rec unif (tequals:Program.tequals) (solutions:Program.tequals) =
  match tequals with
  |[] -> Some solutions

  |(Int,Int)::tequals1 -> unif tequals1 solutions
  |(Double,Double)::tequals1 -> unif tequals1 solutions
  |(Bool,Bool)::tequals1 -> unif tequals1 solutions
  |(String,String)::tequals1 -> unif tequals1 solutions
  |(Unit,Unit)::tequals1 -> unif tequals1 solutions

  |(T s1,T s2)::tequals1 -> unif (changeTequals s1 ((T s2):Program.t) tequals1) ((T s1,T s2)::(changeSolutions s1 ((T s2):Program.t) solutions))
  |(T s1,t2)::tequals1 -> unif (changeTequals s1 t2 tequals1) ((T s1,t2)::(changeSolutions s1 t2 solutions))
  |(t2,T s1)::tequals1 -> unif (changeTequals s1 t2 tequals1) ((T s1,t2)::(changeSolutions s1 t2 solutions))

  |(Fun(t1,t2),Fun(t3,t4))::tequals1 -> unif ((t1,t3)::(t2,t4)::tequals1) solutions                                  
  |(List(t1),List(t2))::tequals1 -> unif ((t1,t2)::tequals1) solutions
  |(Tuple(tlist1),Tuple(tlist2))::tequals1 -> unif (tuple_unif tlist1 tlist2 tequals1) solutions
  |(Struct(env1),Struct(env2))::tequals1 ->
    begin
      match env_unif env1 env2 with
      |true -> unif tequals1 solutions
      |false -> None
    end
  |(A s,_)::tequals1 -> unif tequals1 solutions
  |(_,A s)::tequals1 -> unif tequals1 solutions
  |(Any,t)::tequals1 -> unif tequals1 solutions
  |(t,Any)::tequals1 -> unif tequals1 solutions
  |(t3,t4)::tequals1 -> None

(* unif's function!------------------------------------------------------- *)
      
(* 単一化の際の代入処理
 * t1 代入先
 * t2 代入要素
 * ftequals 代入終了後のtequals *)
and changeType (s: string) (t: Program.t) (t1: Program.t) =
  match t1 with
  | T s1 when s = s1 -> t
  | Fun(t11,t12) -> Fun (changeType s t t11, changeType s t t12)
  | List t11 -> List (changeType s t t11)
  | Tuple tt -> Tuple (List.map (changeType s t) tt)
  | _ -> t1

and changeTequals (s:string) (t:Program.t) (tequals:Program.tequals) :Program.tequals =
  List.map (fun (t1,t2) -> (changeType s t t1,changeType s t t2)) tequals

and changeSolutions (s:string) (t:Program.t) (solutions:Program.tequals) =
  List.map (fun (t1,t2) -> (t1,changeType s t t2)) solutions
  
and tuple_unif (tlist1:Program.t list) (tlist2:Program.t list) (tequals:Program.tequals) :Program.tequals =
  match tlist1,tlist2 with
  |t1::[],t2::[] -> ((t1,t2)::tequals)
  |t1::tlist3,t2::tlist4 -> tuple_unif tlist3 tlist4 ((t1,t2)::tequals)
  |_,_ -> raise Error

and env_unif (env1:Program.env) (env2:Program.env) :bool =
  match env1,env2 with
  |(s1,t1,v1)::[],(s2,t2,v2)::[] when (s1=s2) ->
    begin
      match unif ((t1,t2)::[]) [] with
      |Some solutions -> true
      |None -> false
    end
  |(s1,t1,v1)::env3,(s2,t2,v2)::env4 when (s1=s2) ->
    begin
      match unif ((t1,t2)::[]) [] with
      |Some solutions -> env_unif env3 env4 
      |None -> false
    end
  |_,_ -> raise Error

and tuple_changelist (list:Program.t list) (s1:string) (t2:Program.t) :Program.t list =
  match list with
  |(T s)::[] -> if String.equal s s1 then t2::[] else (T s)::[]
  |t1::[] -> t1::[]
  |(T s)::list1  ->
    begin
      match tuple_changelist list1 s1 t2 with
      |list2 -> if String.equal s s1 then t2::list2 else (T s)::list2
    end
  |t1::list1 ->
    begin
      match tuple_changelist list1 s1 t2 with
      |list2 -> t1::list2
    end
  |_ -> raise Error

let a (tn:int) :Program.t = A ("A" ^ string_of_int(tn))

let rec arrange_solutions (solutions:Program.tequals) (n:int) :(Program.tequals * int) =
  match solutions with
  |(t1,t2)::solutions1 ->
    begin
      match add_type t2 n [] with
      |(t3,n1,fs1) ->
        begin
          match solutions1 with
          |[] -> (((t1,t3)::fs1),n1)
          |_ ->
            begin
              match arrange_solutions solutions1 n1 with
              |(solutions2,n2) -> (((t1,t3)::(solutions2@fs1)),n2)
            end
        end
    end
  |_ -> raise Error

and add_type (t2:Program.t) (n:int) (fs:Program.tequals) :(Program.t * int * Program.tequals) =
  match t2 with
  |T s1 -> ((a n),(n+1),fs)
  |Fun((t3),(t4)) ->
    begin
      match add_type t3 n fs with
      |(t5,n1,fs1) ->
        begin
          match add_type t4 n1 fs with
          |(t6,n2,fs2) -> (Fun(t5,t6),n2,((t4,t6)::(t3,t5)::fs2))
        end
    end
  |_ -> (t2,n,fs)

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
      |Fun(t3,t4) ->
        begin
          match find_type_solutions t3 solutions with
          |t5 ->
            begin
              match find_type_solutions t4 solutions with
              |t6 -> Fun(t5,t6)
            end
         end
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

;;

(* (\* test------------------------------------------------------------------- *\)
 * 
 * (\* d=[("key1",1),("key2",2)]
 *  for k,n in d:
 *  *      z+=k  *\)
 * print_evalResult (expr_eval (For_dict(["k";"n"],Var "d",AOperate(Add,Var "z",Var "k"))) [("z",List Int,Nil);("d",List (Tuple [String;Int]),Cons(Tuple [(String "key1");(Int 1)],Cons(Tuple [(String "key2");(Int 2)],Nil)))] []);; 
 * 
 * (\* z=[]
 *  * l1=[1,2]
 *  * l2=[3,4]        
 *  * for a,b in l1,l2:
 *  *      z+=a+b *\)
 * print_evalResult (expr_eval (For(["a";"b"],[(Var "l1");(Var "l2")],(AOperate(Add,(Var "z"),Operate(Add,(Var "a"),(Var "b")))))) [("z",List Int,Nil);("l1",List Int,Cons((Int 1),Cons((Int 2),Nil)));("l2",List Int,Cons((Int 3),Cons((Int 4),Nil)))] []);; 
 * 
 * 
 * (\* for k,n in [("key1",1),("key2",2)]:
 *  *      z+=k                *\)
 * print_evalResult (expr_eval (For_dict(["k";"n"],Cons((Tuple ([(String "key1");(Int 1)])),Cons((Tuple ([(String "key2");(Int 2)])),Nil)),(AOperate(Add,(Var "z"),(Var "k"))))) [("z",List Int,Nil)] []);; 
 * 
 * (\* z=[]
 *  * for a,b in [1,2],[3,4]:
 *  *    z+=a+b *\)
 * print_evalResult (expr_eval (For(["a";"b"],[(Cons((Int 1),Cons((Int 2),Nil)));(Cons((Int 3),Cons((Int 4),Nil)))],(AOperate(Add,(Var "z"),Operate(Add,(Var "a"),(Var "b")))))) [("z",List Int,Nil)] []);; 
 * 
 * (\* z=[]
 *  * for a,b in [1],[4]:
 *  *    z+=a+b *\)
 * print_evalResult (expr_eval (For(["a";"b"],[(Cons((Int 1),Nil));(Cons((Int 4),Nil))],(AOperate(Add,(Var "z"),Operate(Add,(Var "a"),(Var "b")))))) [("z",List Int,Nil)] []);; 
 * 
 * (\* z=[]
 *  * for a in [1,2,3]:
 *  *    z+=a *\)
 * print_evalResult (expr_eval (For(["a"],[(Cons((Int 1),Cons((Int 2),Cons((Int 3),Nil))))],(AOperate(Add,(Var "z"),(Var "a"))))) [("z",List Int,Nil)] []);; 
 * 
 * (\* 1+2+3 *\)
 * print_evalResult (expr_eval (Operate(Add,(Int 1),Operate(Add,(Int 2),(Int 3)))) [] []);;
 * 
 * (\* z=[]
 *  * for a,b,c in [1,2,3],[4,5,6],[7,8,9]:
 *  *    z+=(a+b+c) *\)
 * print_evalResult (expr_eval (For(["a";"b";"c"],[(Cons((Int 1),Cons((Int 2),Cons((Int 3),Nil))));(Cons((Int 4),Cons((Int 5),Cons((Int 6),Nil))));(Cons((Int 7),Cons((Int 8),Cons((Int 9),Nil))))],(AOperate(Add,(Var "z"),(Operate(Add,(Var "a"),(Operate(Add,(Var "b"),(Var "c"))))))))) [("z",List Int,Nil)] []);; 
 * 
 * (\* match  l with [] -> 0 | x::[] -> 1| x::y::z -> 2 *\)
 * print_evalResult (expr_eval (Match((Var "l"),[(Nil,(Int 0));(Cons((Var "x"),Nil),(Int 1));((Cons((Var "x"),Cons((Var "y"),Cons((Var "z"),Nil)))),(Int 2))])) [("l",List Int,Cons((Int 1),Cons((Int 2),Cons((Int 3),Nil))))] []);;
 * 
 * (\* if not (1<2) then 1 else 0 *\)
 * print_evalResult (expr_eval (If((Not ((Operate(Lt,Var "i",Int 2)))),(Int 1),(Int 0))) [("i",Int,Int 1)] []);;
 * 
 * (\* if (1<2) then 1 else 0 *\)
 * print_evalResult (expr_eval (If((Operate(Lt,Var "i",Int 2)),(Int 1),(Int 0))) [("i",Int,Int 1)] []);;
 * 
 * (\* not (1<2) *\)
 * print_evalResult (expr_eval (Not (Operate(Lt,Var "i",Int 2))) [("i",Int,Int 1)] []);;
 * 
 * (\* [1,2,3] - 2 *\)
 * print_evalResult (expr_eval (Sub(Cons((Int 1),Cons((Int 2),Cons((Int 3),Nil))),Int 2)) [] []);;
 * 
 * (\* x=1+2 *\)
 * print_evalResult (expr_eval (Formu(Var "x",Operate(Add,Var "i",Int 2))) [("i",Int,Int 1)] []);;
 * 
 * print_evalResult (expr_eval (Operate(Add,Var "i",Int 2)) [("i",Int,Int 1)] []);;
 * 
 * (\* 変数が存在してない場合NoSourcetoSubErrorが出る *\)
 * print_evalResult (expr_eval (SubFormu(Var "l",Tuple [Wild;(Int 2)])) [] []);;
 * 
 * (\* [(1,2),(3,4),(4,2)] -= (_,2) *\)
 * print_evalResult (expr_eval (SubFormu(Var "l",Tuple [Wild;(Int 2)])) [("l",List (Tuple [Int;Int]),Cons((Tuple [(Int 1);(Int 2)]),Cons((Tuple [(Int 3);(Int 4)]),Cons((Tuple [(Int 4);(Int 2)]),Nil))))] []);;
 * 
 * (\* [1] -= 1 *\)
 * print_evalResult (expr_eval (SubFormu(Var "l",Int 1)) [("l",List Int,Cons((Int 1),Nil))] []);;
 * 
 * (\* [1,2,3] -= 2 *\)
 * print_evalResult (expr_eval (SubFormu(Var "l",Int 2)) [("l",List Int,Cons((Int 1),Cons((Int 2),Cons((Int 3),Nil))))] []);;
 * 
 * (\* [(1,2),(3,4)] -= (_,2) *\)
 * print_evalResult (expr_eval (SubFormu(Var "l",Tuple [Wild;(Int 2)])) [("l",List (Tuple [Int;Int]),Cons((Tuple [(Int 1);(Int 2)]),Cons((Tuple [(Int 3);(Int 4)]),Nil)))] []);;
 * 
 * 
 * (\* Tuple+Cons *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",Cons((Int 3),Nil))) [("i",(Tuple [Int;Int;(List Int)]),Tuple [(Int 1);(Int 2)])] []);;
 * 
 * (\* Cons+Cons *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",Cons((Int 3),Cons((Int 4),Nil)))) [("i",(List Int),Cons((Int 1),Cons((Int 2),Nil)))] []);;
 * 
 * (\* Cons+Int *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",Cons((Int 3),Nil))) [("i",(List Int),Cons((Int 1),Cons((Int 2),Nil)))] []);;
 * 
 * (\* Int+String *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",String "回")) [("i",Int,Int 1)] []);;
 * 
 * (\* Int+Double *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",Double 2.4)) [("i",Int,Int 1)] []);;
 * 
 * (\* Int+Int *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",Int 2)) [("i",Int,Int 1)] []);;
 * 
 * 
 * (\* 宣言されてない変数の処理 *\)
 * print_evalResult (expr_eval (AOperate(Add,Var "i",Int 2)) [] []);;
 * 
 * (\* user.."wage"..t = 1 *\)
 * print_evalResult (expr_eval (Formu2(UseIns2(UseIns2(Var "user",String "wage"),Var "t"),Int 1)) [("user",String,String "user1");("t",String,String "time");("user1",T "User",(Struct("User",[("name",String,String "A");("wage",T "Hollywage",(Struct("Hollywage",[])))])))] []);;
 * 
 * (\* "user1".."wage".."time" = 1 *\)
 * print_evalResult (expr_eval (Formu2(UseIns2(UseIns2(String "user1",String "wage"),String "time"),Int 1)) [("user1",T "User",(Struct("User",[("name",String,String "A");("wage",T "Hollywage",(Struct("Hollywage",[])))])))] []);;
 * 
 * (\* user1.wage.time.work = 1 *\)
 * print_evalResult (expr_eval (Formu2(UseIns1(UseIns1(UseIns1(Var "user1","wage"),"time"),"work"),Int 1)) [("user1",T "User",(Struct("User",[("name",String,String "A");("wage",T "Hollywage",(Struct("Hollywage",[("time",T "WorkTime",(Struct("WorkTime",[("work",Int,Int 0)])))])))])))] []);;
 * 
 * (\* user1.wage.time = 1 *\)
 * print_evalResult (expr_eval (Formu2(UseIns1(UseIns1(Var "user1","wage"),"time"),Int 1)) [("user1",T "User",(Struct("User",[("name",String,String "A");("wage",T "Hollywage",(Struct("Hollywage",[])))])))] []);;
 * 
 * (\* user1.id = 1 *\)
 * print_evalResult (expr_eval (Formu2(UseIns1(Var "user1","id"),Int 1)) [("user1",T "User",(Struct("User",[("name",String,String "A")])))] []);;
 * 
 * (\* 既存の変数に上書きができているかの確認 *\)
 * print_evalResult (expr_eval (Formu(Tuple[(Var "name");(Var "since");(Var "where")],Tuple([(String "Qsitory");(Int 2022);(String "Japan")]))) [("name",String,String "program")] []);;
 * 
 * print_evalResult (expr_eval (Formu(Tuple[(Wild);(Var "since");(Var "where")],Tuple([(String "Qsitory");(Int 2022);(String "Japan")]))) [] []);;
 * 
 * print_evalResult (expr_eval (Declrt2(String,"name")) [] []);;
 * 
 * print_evalResult (expr_eval (Declrt1(String,"name",String "Qsitory")) [] []);;
 * 
 * print_evalResult (expr_eval (Tuple [(Int 1);(Int 2);(Int 3);(Int 4)]) [] []);;
 * 
 * print_evalResult (expr_eval (Cons((Int 1),(Nil))) [] []);;
 * 
 * print_evalResult (expr_eval (Var "name") [("name",String,String "Qsitory")] []);;
 * 
 * print_evalResult (expr_eval (Int 1) [] []);; *)
