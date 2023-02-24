(*
**  Qsitory
**
*)
open Syntax
open Tools   
module F = Format
module P = Pprint
   

let filename = ref ""

             
let set_filename fname = filename := fname
  
let msgUsage = "USAGE: qsitory [-f <file>]\n"

let speclist = [
    ("-f", Arg.String set_filename, "Input file");
    ("-lex", Arg.Unit (fun _ -> addDebugOpt "LEXING"), "Set lexing debug mode");
    ("-parse", Arg.Unit (fun _ -> addDebugOpt "PARSING"), "Set parsing debug mode");
    ("-test", Arg.Unit (fun _ -> addDebugOpt "TESTMODE"), "Set test mode");
]

let () =
  Arg.parse speclist print_endline msgUsage;
  match !filename = "" with
  | true -> Interactive.interpreter ()
  | false -> Readfile.interpreter !filename
