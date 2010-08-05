(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Chapter: Linear Programs                                         *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-08-01                                                           *)
(* ========================================================================== *)

(* Linear Programs for the hard cases.  Individual case runs *)

flyspeck_needs "nonlinear/parse_ineq.hl";;
flyspeck_needs "nonlinear/temp_ineq.hl";;
flyspeck_needs "../glpk/tame_archive/lpproc.ml";;
flyspeck_needs "../glpk/tame_archive/hard_lp.ml";;

module Lp_case_analysis = struct

  open Hard_lp;;

Lpproc.archiveraw := "/Users/thomashales/Desktop/workspace/hanoi_workshop_files/tame_archive_svn1830.txt";;

(* moved to hard_lp *)

end;;
