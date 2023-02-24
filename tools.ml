module F = Format

exception ParseError of string

(* Debugging *)
let debugOptions: string list ref = ref []                       

let doIfDebug deb f x = if List.mem deb !debugOptions then f x else ()
                                  
let addDebugOpt opt = debugOptions := opt :: !debugOptions

let doIfNotNone f opt =
  match opt with
  | None -> ()
  | Some a -> f a
                    
(* pretty printing constructor for option types *)   
let pp_opt none pp fmt opt =
  match opt with
  | None -> F.fprintf fmt "%s" none
  | Some u -> F.fprintf fmt "%a" pp u

(* pretty printing constructor for lists *)
let pp_list base sep pp fmt xx =
  match xx with
  | [] -> F.fprintf fmt "%s" base
  | _ -> F.pp_print_list ~pp_sep:(fun _ _ -> F.fprintf fmt sep) pp fmt xx

(* simple pattern of pp_list (base = "", sep = ",") *)
let pp_list0 pp fmt xx = pp_list "" "," pp fmt xx

let pp_list00 pp fmt xx = pp_list "" ", " pp fmt xx

let pp_list0_bracket pp fmt xx = Format.fprintf fmt "[%a]" (pp_list0 pp) xx

let pp_list00_bracket pp fmt xx = Format.fprintf fmt "[%a]" (pp_list00 pp) xx
                       
let pp_tuple2 pp1 pp2 fmt (x,y) = F.fprintf fmt "(%a,%a)" pp1 x pp2 y

let pp_tuple3 pp1 pp2 pp3 fmt (x,y,z) = F.fprintf fmt "(%a,%a,%a)" pp1 x pp2 y pp3 z

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_int fmt n = F.fprintf fmt "%d" n
                    
let print str = Format.printf "@[%s@?" str

let println str = Format.printf "@[%s@." str

(* Lexer tool *)                
let tokenMemo = ref ""
              
let addMemo mes = tokenMemo := if !tokenMemo = "" then mes else F.sprintf "%s %s" !tokenMemo mes

let clearMemo () = tokenMemo := ""
                
(* Other tools *)                
let rec zip ls1 ls2 =
  match ls1,ls2 with
  | x::ls1',y::ls2' -> (x,y)::(zip ls1' ls2')
  | _,_ -> []

let rec list_assoc3 key ls3 =
  match ls3 with
  | [] -> raise Not_found
  | (k,a,b)::ls3 when key = k -> (a,b)
  | _::ls3' -> list_assoc3 key ls3'

let rec list_assoc3_opt key ls3 =
  match ls3 with
  | [] -> None
  | (k,a,b)::ls3 when key = k -> Some (a,b)
  | _::ls3' -> list_assoc3_opt key ls3'

let split_dp (s:string) :string =
  match String.get s 0 with
  | '\"' -> String.sub s 1 ((String.length s)-2)
  | _ -> s

(* checkEqFun eq [(x1,a1);(x2,a2)] [(x1,a1');(x2,a2')] is true <-> eq a1 a1' = true and eq a2 a2' = true *)
let checkEqFun eq f1 f2 =
  let rec check f1 f =
    match f with
    | [] -> true
    | (x,a)::f' ->
       match List.assoc_opt x f1 with
       | None -> false
       | Some b when eq a b -> check f1 f'
       | _ -> false
  in
  check f1 f2 && check f2 f1
;;

(* checkEqFun2 eq [(x,a,b)] [(x,a',b')] is true <-> eq a a' = true and eq b b' = true *)
let checkEqFun2 eq1 eq2 f1 f2 =
  let eq (a,b) (a',b') = eq1 a a' && eq2 b b' in
  let shift (a,b,c) = (a,(b,c)) in
  checkEqFun eq (List.map shift f1) (List.map shift f2)
;;

