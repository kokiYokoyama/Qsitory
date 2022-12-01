module F = Format

exception ParseError of string

(* Debugging *)
let debugOptions: string list ref = ref []                       

let doIfDebug deb f x = if List.mem deb !debugOptions then f x else ()
                                  
let addDebugOpt opt = debugOptions := opt :: !debugOptions

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

let pp_tuple2 pp1 pp2 fmt (x,y) = F.fprintf fmt "(%a,%a)" pp1 x pp2 y

let pp_tuple3 pp1 pp2 pp3 fmt (x,y,z) = F.fprintf fmt "(%a,%a,%a)" pp1 x pp2 y pp3 z

let pp_string fmt s = F.fprintf fmt "%s" s

let pp_int fmt n = F.fprintf fmt "%d" n
                    
let print str = Format.printf "@[%s@?" str

let println str = Format.printf "@[%s@." str
                    
let rec zip ls1 ls2 =
  match ls1,ls2 with
  | x::ls1',y::ls2' -> (x,y)::(zip ls1' ls2')
  | _,_ -> []
