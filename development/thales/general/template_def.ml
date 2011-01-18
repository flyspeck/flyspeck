(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Author: Thomas C. Hales                                                    *)
(* Date: Feb 7, 2010                                                          *)
(* ========================================================================== *)


(*
Outputs to a file 
a formatted HOL Light identifier, as a module with signature.
The author and date information are added as comments.

The file pathname is derived from the root directory, which can be set by the user,
the lowercase of chapter string must match a subdirectory name precisely,
and the identifier is used to create the file name.
*)


module type Template_hol_type = sig

  type data =
      {
	identifier : string;
	chapter : string;
	author: string;
	date:string;
	code:string;
	comments:string list;
        needlist:string list;
      }

  val output_template_def : data -> unit 

  val output_template_lemma : data -> unit

  val set_root_dir : string-> unit  (* default is "/tmp" *)

end;;

(* 
Example:  The following code creates a template identifier file 
   "/tmp/Trigonometry/azim_def.hl",
populated with the code from def1
*)

(*

open Template_hol;;
let example1() = 
  let def1 = 
    {identifier="azim";
     chapter="Trigonometry";
     author="Thomas C. Hales";
     date="Feb 7, 2010";
     code="<Insert HOL-Light code for theorem here>";
     comments=["This is just a test!"];
     needlist=["Multivariate/flyspeck.ml"];
    } in
 let _ = set_root_dir "/tmp" in
   output_template_def def1;;
example1();;

*)

module Template_hol : Template_hol_type = 
struct

  type data =
      {
	identifier : string;
	chapter : string;
	author: string;
	date:string;
	code:string;
	comments: string list;
	needlist:string list;
      };;

  (* Comments and Line Formatting *)

  let sep= "/";;
  let pad='=';;
  let space=' ';;
  let emptystring="";;

  let unsplit d f = function
    | (x::xs) ->  List.fold_left (fun s t -> s^d^(f t)) (f x) xs
    | [] -> "";;

  let join_lines  = unsplit "\n" (fun x-> x);;
  let width = 80 - 6;;

  let c_enclose s = "(* "^s^String.make (width - String.length s) space^" *)";;
  let pad_line = (String.make width pad);;
  let space_line = String.make width space;;

  type opt = Def | Lemma;;
  let label t = if t=Def then "Definition" else "Lemma";;
  let ext t = if t=Def then "_def" else "";;

  (* Content *)

  let header t dat = 
    let p = Printf.sprintf in
      unsplit "\n" c_enclose [
	pad_line;
	p"FLYSPECK - BOOK FORMALIZATION";
	space_line;
	p"%s: %s" (label t) dat.identifier;
	p"Chapter: %s" dat.chapter;
	p"Author: %s" dat.author;
	p"Date: %s" dat.date;
	pad_line;
      ];;

  let more_comments dat = 
   if (dat.comments =[]) then emptystring else
   "(*\n"^(join_lines dat.comments)^"\n*)\n\n\n";;

  let neededfiles dat = 
       if (dat.needlist =[]) then emptystring else
      (unsplit "\n" (fun s -> "flyspeck_needs \""^s^"\";;") dat.needlist)^"\n\n\n";;

  let body dat = 
    let p = Printf.sprintf in
    let uc = String.capitalize (String.lowercase dat.identifier) in (* HOL Light parsing: cap first char only *)
      join_lines [
	p"module type %s_def_type = sig" uc;
	p"  val %s : thm" dat.identifier;
	"end;;\n\n";
	neededfiles dat;
	p"module %s : %s_def_type = struct\n" uc uc;
 	p" let %s = " dat.identifier;
	dat.code;
	"\nend;;\n";
      ];;

  (* Output *)

  let rootdir =ref "/tmp";;
  let set_root_dir s = (rootdir := s);;

  let filename  t dat = (!rootdir)^sep^(String.lowercase dat.chapter)^sep^dat.identifier^(ext t)^".hl";;

  let save_stringarray filename xs = 
    let oc = open_out filename in
      for i=0 to List.length xs -1
      do
	Pervasives.output_string oc (List.nth xs i ^ "\n");
      done;
      close_out oc;;

  let output_template t dat = save_stringarray (filename t dat) 
      [header t dat;"\n\n\n";more_comments dat;
       body dat];;

  let output_template_def dat = output_template Def dat;;
  let output_template_lemma dat = output_template Lemma dat;;

end;;


