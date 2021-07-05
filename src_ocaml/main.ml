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
open Utils;;

let usage_msg = "TODO"
let verbose = ref false
let input_files = ref []
let bound = ref 100
let anon_fun filename =
  input_files := filename :: !input_files
let speclist =
  [("--verbose", Arg.Set verbose, "Output debug information");
   ("-b", Arg.Set_int bound, "TODO")]

let print_chars_endline cs =
  print_endline (chars_to_string cs)
;;

let main =
  Arg.parse speclist anon_fun usage_msg;

  let ncall = FlatModel.first_not_disabled in

  let dcall = fun msg c ->
    (* print_chars_endline msg; *)
    c () in

  let test = test_ldr in

  begin match FlatModel.run_test ncall dcall test (nat_of_int !bound) with
  | ERReturn (s, _) -> print_chars_endline (FlatModel.show_state s)
  | ERBound -> print_endline "Bound reached!"
  | ERDisabled -> print_endline "'disabled' propagated to the top?"
  | ERError msg -> print_endline "ERRORE:"; print_chars_endline msg
  end
;;
