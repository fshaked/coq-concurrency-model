open Stdlib;;

open Datatypes;;
open ExtrOcamlIntConv;;

(* module Nat = struct
 *   include Nat
 *   let rec to_int = function | O -> 0 | S n -> succ (to_int n)
 *   let rec of_int n = assert(n >= 0); if(n == 0) then O else S (of_int (pred n))
 * end *)

let chars_to_string (cs : char list) : string =
  String.init (List.length cs) (fun i -> List.nth cs  i)
;;

open FlatThread;;
open System;;
open FlatModel;;

let usage_msg = "TODO"
let verbose = ref false
let input_files = ref []
let bound = ref 100
let anon_fun filename =
  input_files := filename :: !input_files
let speclist =
  [("--verbose", Arg.Set verbose, "Output debug information");
   ("-b", Arg.Set_int bound, "TODO")]

let main =
  Arg.parse speclist anon_fun usage_msg;

  begin match FlatModel.run_test test_and (nat_of_int !bound) with
  | Datatypes.Coq_inl _ -> print_endline "*** TODO ***"
  | Datatypes.Coq_inr (_, s) ->
     List.iter (fun cs -> print_endline (chars_to_string cs)) (List.rev s)
  end
;;
