(* ========================================================================= *)
(* Some miscellaneous OCaml system hacking before we get started.            *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };;

(* ------------------------------------------------------------------------- *)
(* Make sure user interrupts generate an exception, not kill the process.    *)
(* ------------------------------------------------------------------------- *)

Sys.catch_break true;;

(* ------------------------------------------------------------------------- *)
(* Set up a quotation expander for the `...` quotes.                         *)
(* This includes the case `;...` to support miz3, even if that isn't loaded. *)
(* ------------------------------------------------------------------------- *)

(* AS:
let quotexpander s =
  if s = "" then failwith "Empty quotation" else
  let c = String.sub s 0 1 in
  if c = ":" then
    "parse_type \""^
    (String.escaped (String.sub s 1 (String.length s - 1)))^"\""
  else if c = ";" then "parse_qproof \""^(String.escaped s)^"\""
  else "parse_term \""^(String.escaped s)^"\"";;

Quotation.add "tot" (Quotation.ExStr (fun x -> quotexpander));;
*)

(* ------------------------------------------------------------------------- *)
(* Modify the lexical analysis of uppercase identifiers.                     *)
(* ------------------------------------------------------------------------- *)

(* AS:
set_jrh_lexer;;*)

(* ------------------------------------------------------------------------- *)
(* Load in the bignum library and set up printing in the toplevel.           *)
(* ------------------------------------------------------------------------- *)

(* AS:
#load "nums.cma";;*)

include Num;;

let print_num n =
  Format.open_hbox();
  Format.print_string(string_of_num n);
  Format.close_box();;

(* AS:
#install_printer print_num;;*)
