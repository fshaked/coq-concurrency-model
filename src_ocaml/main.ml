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

type exec_result =
  | Accept of FlatModel.Model.state
  | Reject
  | Error
;;

let rec exec_test it =
  begin match FlatModel.Model.step it with
  | SNondet its ->
     let (eager, not_eager) = List.partition (fun (_, eager) -> eager) its in
     Printf.printf "- Nondet %d (%d eager)\n" (List.length its) (List.length eager);
     begin match eager_nondet eager with
     | Reject -> nondet not_eager
     | x -> x
     end
  | SNext (Some dbg, it) ->
     print_chars_endline dbg;
     exec_test it
  | SNext (None, it) ->
     print_string ".";
     exec_test it
  | SAccept (s, _) -> Accept s
  | SReject ->
     print_endline "- Disabled";
     Reject
  | SError err ->
     Printf.printf "ERROR: %s\n" (chars_to_string err);
     Error
  end
and eager_nondet its =
  begin match its with
  | (it, _)::its ->
     begin match exec_test it with
     | Reject ->
        print_endline "-- Eager disabled^";
        eager_nondet its
     | x -> x
     end
  | _ -> Reject
  end
and nondet its =
  begin match its with
  | (it, _)::its ->
     begin match exec_test it with
     | Accept res -> Accept res
     | Reject ->
        print_endline "-- Nondet disabled";
        nondet its
     | Error -> Error
     end
  | _ -> Reject
  end
;;

let main =
  Arg.parse speclist anon_fun usage_msg;

  (* let test = test_and in *)
  let test = test_ldr in

  begin match exec_test (init_test test) with
  | Accept s -> print_chars_endline (FlatModel.show_state s)
  | _ -> ()
  end
;;
