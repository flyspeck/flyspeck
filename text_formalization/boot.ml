(* ========================================================================= *)
(* FLYSPECK - BOOK FORMALISATION                                             *)
(*                                                                           *)
(* File to kickstart checkpointed flyspeck using BLCR                        *)
(*                                                                           *)
(* Author: Joe Pleso                                                         *)
(* Date:   2011-04-20                                                        *)
(* ========================================================================= *)


let backup_stdout=Unix.dup Unix.stdout;;
let backup_stderr=Unix.dup Unix.stderr;;

let default_flag_list=[Unix.O_TRUNC;Unix.O_WRONLY;Unix.O_CREAT];;


let hollight_name = "hol_light";;
let hollight_stdout_name= hollight_name ^ ".out";;
let hollight_stdout=Unix.openfile hollight_stdout_name default_flag_list 420;;
let hollight_stderr_name= hollight_name ^ ".err";;
let hollight_stderr=Unix.openfile hollight_stderr_name default_flag_list 420;;
Unix.dup2 hollight_stdout Unix.stdout;;
Unix.dup2 hollight_stderr Unix.stderr;;

#use "hol.ml";;

let flyspeck_name = "flyspeck";;
let flyspeck_stdout_name= flyspeck_name ^ ".out";;
let flyspeck_stdout=Unix.openfile flyspeck_stdout_name default_flag_list 420;;
let flyspeck_stderr_name= flyspeck_name ^ ".err";;
let flyspeck_stderr=Unix.openfile flyspeck_stderr_name default_flag_list 420;;

Unix.dup2 flyspeck_stdout Unix.stdout;;
Unix.dup2 flyspeck_stderr Unix.stderr;;
Unix.close hollight_stdout;;
Unix.close hollight_stderr;;
#use "strictbuild.hl";;
build_silent();;
Unix.dup2 backup_stdout Unix.stdout;;
Unix.dup2 backup_stderr Unix.stderr;;
Unix.close backup_stdout;;
Unix.close backup_stderr;;
Unix.close flyspeck_stdout;;
Unix.close flyspeck_stderr;;

let ocampl_pid()=process_to_string "echo -n $PPID";;
let blcr()=(build_silent o ignore o Sys.command)
  ("cr_checkpoint -f context.ocampl --backup --term " ^ ocampl_pid() ^ " &");;
blcr();;
