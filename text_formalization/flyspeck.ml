(* File started January 5, 2007.  Thomas C. Hales.

MIT Public License.

This is the code for the Flyspeck project.

*)

(*
Keep the following in mind.

1.  Please use hypotheses to make it possible to add the code anywhere
after the main initialization file.  

2.  Do not make changes that affect the global state of the theorem prover.
That is please don't make any changes that will break theorems proved by others. 

3.  The repository is maintained with the MIT Public License.  The purpose
is to make code available for use and modification by others.  *)

(* I anticipate that many parts will be worked on in parallel.  Some
parts will rely on theorems that have been not been formalized.  To
deal with the hypotheses systematically, let's introduce a list of
hypotheses to each theorem.  We create a tag "hypo" specifically for
hypotheses that will eventually become unqualified theorems.  *)



let hypo = new_recursive_definition list_RECURSION 
  `(hypo [] = T) /\ (hypo (CONS h t) = (h /\ hypo t))`;;

(* Examples/transc.ml contains definitions "cos" and "sin" *)

(* Lemma 1.1 is SIN_CIRCLE *)
(* Lemma 1.2 is SIN_ADD and COS_ADD *)
(* Lemma 1.3 is SIN_NEG and COS_NEG *)
(* Lemma 1.4 is SIN_PI2 *)
(* Lemma 1.5 is GSYM COS_SIN *)






