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

let prefix d =
  let a = d mod 150 in
  Printf.sprintf "%d%s" (d-a) (String.make a '-')
;;

let rec exec_test d it =
  begin match FlatModel.Model.step it with
  | SNondet its ->
     let (eager, not_eager) = List.partition snd
                                (* its in *)
                                (List.rev its) in
     Printf.printf "%s Nondet %d (%d eager)\n" (prefix d) (List.length its) (List.length eager);
     if eager = [] then nondet d not_eager else eager_nondet d eager
     (* begin match eager_nondet d eager with
      * | Reject -> nondet d not_eager
      * | x -> x
      * end *)
  | SNext (Some dbg, it) ->
     Printf.printf "%s %s\n" (prefix d) (chars_to_string dbg);
     exec_test d it
  | SNext (None, it) ->
     (* print_string "."; *)
     exec_test d it
  | SAccept (s, _) -> Accept s
  | SReject ->
     Printf.printf "%s Disabled\n" (prefix d);
     Reject
  | SError err ->
     Printf.printf "ERROR: %s\n" (chars_to_string err);
     Error
  end
and eager_nondet d its =
  begin match its with
  | (it, _)::its ->
     begin match exec_test d it with
     (* | Reject -> eager_nondet d its *)
     | x -> x
     end
  | _ ->
     Printf.printf "%s Eager disabled\n" (prefix d);
     Reject
  end
and nondet d its =
  begin match its with
  | (it, _)::its ->
     begin match exec_test (d+1) it with
     | Accept res -> Accept res
     | Reject -> nondet d its
     | Error -> Error
     end
  | _ ->
     Printf.printf "%s Nondet disabled\n" (prefix d);
     Reject
  end
;;

let main =
  Arg.parse speclist anon_fun usage_msg;

  (* let (test, ts) = (test_and, 1) in *)
  (* let (test, ts) = (test_ldr, 1) in *)
  let (test, ts) = (test_MP, 2) in

  begin match exec_test 1 (init_test test (Big_int.big_int_of_int ts)) with
  | Accept s -> print_chars_endline (FlatModel.show_state s)
  | _ -> ()
  end
;;
