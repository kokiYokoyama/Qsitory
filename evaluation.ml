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
open Syntax
(* Expr_Eval-------------------------------------------------------------- *)

let rec expr_eval (e:Program.e) (env:Program.env) (tenv:Program.tenv) :Program.evalResult  =
  match e with
  |Int i -> (Int i,env,tenv)
  |Double d -> (Double d,env,tenv)
  |Bool b -> (Bool b,env,tenv)
  |String s -> (String s,env,tenv)
  |Var s -> ((find env s),env,tenv)
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
      |(v1,env1,tenv1) -> (Null,((s,t,Some (v1))::env1),tenv1)
    end
  |Declrt2(t,s) -> (Null,((s,t,None)::env),tenv)
  |Formu(p,e) ->
    begin
      match expr_eval e env tenv with
      |(v1,env1,tenv1) ->
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
    begin
      match expr_eval e0 env tenv,plist0 with
      |(v1,env1,tenv1),(p,e)::[] ->
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
          |s::paraList1,(Cons(v1,v2))::vlist1 ->
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
  |Dfun(s,e) -> (FunClos(env,s,e),env,tenv)
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
                  match expr_eval e0 ((s,Any,(Some v2))::(env0@(find_fun env []))) tenv2 with
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

  |Block(elist) ->
    begin
      match elist with
      |e::[] -> expr_eval e env tenv
      |e::elist1 ->
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
      |_ -> raise Error
    end
              
      
   
   
(* eval's function!------------------------------------------------------- *)

and find (env:Program.env) (s:string) :Program.v =
  match env with
  |(s1,t,Some (v))::env1 -> if String.equal s s1 then v else find env1 s
  |[] -> raise NoValueError
  |_ -> raise Error

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
  match p,v  with
  (* パターンマッチ成功 *)
  |Int i1,Int i2 -> if i1==i2 then Some env else None
  |Double d1,Double d2 -> if d1==d2 then Some env else None
  |Bool b1,Bool b2 -> if b1==b2 then Some env else None
  |String s1,String s2 -> if String.equal s1 s2 then Some env else None
  |Var s,v ->
    begin
      match v with
      |FunClos(env0,s0,e0) -> Some ((s,Fun(Any,Any),Some v)::(find_remove env s []))
      |_ -> Some ((s,Any,Some v)::(find_remove env s []))
    end
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
      |fi_n::[] -> (ins_n,(T st_n),Some (Struct(st_n,((fi_n,Any,Some v)::(find_remove field fi_n [] )))))::(find_remove env ins_n [])
      |fi_n::fids1 ->
        begin
          match updateFids fi_n fids1 v field with
          |field1 -> ((ins_n,(T st_n),Some (Struct(st_n,field1)))::(find_remove env ins_n []))
        end
      |_ -> raise Error
    end
  |_ -> raise Error

and aOperate (e:Program.e) (v1:Program.v) (v2:Program.v) (aop:Program.aop) (env:Program.env) :Program.env =
  match e with
  |Var s ->
    begin
      match v1 with
      |Null -> ((s,Any,Some v2)::(find_remove env s []))
      |_ -> ((s,Any,Some (operate v1 v2 (changeaop_to_op aop)))::(find_remove env s []))
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
  |Var s -> ((s,Any,Some (removeMatch v p env))::(find_remove env s []))
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
  |[] ->(vlist,env,tenv)
      
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
  |s::paraList1,(Cons(v1,v2))::vlist1 -> expr_secondFor_eval paraList1 vlist1 e ((s,Any,Some v1)::(find_remove env s [])) tenv 

  |s::paraList1,(Nil)::vlist1 -> expr_secondFor_eval paraList1 vlist1 e ((s,Any,None)::(find_remove env s [])) tenv
  |_ -> raise Error

and expr_roopFor_eval (paraList:string list) (vlist:Program.v list) (e:Program.e) (env:Program.env) (tenv:Program.tenv) :Program.evalResult =
  match paraList,vlist with
  (* 全要素完了 *)
  |[],[] -> expr_eval e env tenv
  |s::paraList1,(Cons(v1,v2))::vlist1 ->
    begin
      (* 2要素目 *)
      match expr_secondFor_eval paraList1 vlist1 e ((s,(Any:Program.t),Some v1)::(find_remove env s [])) tenv with
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
  |s::paraList1,Tuple (v::vlist1) -> get_dict_item paraList1 (Tuple (vlist1)) ((s,Any,Some v)::(find_remove env s [])) 
  |_ -> raise Error

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
