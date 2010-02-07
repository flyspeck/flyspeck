(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Author: Thomas C. Hales                                                    *)
(* Date: Feb 7, 2010                                                          *)
(* ========================================================================== *)


(*
Outputs to a file 
a formatted HOL Light definition, as a module with signature.
The author and date information are added as comments.

The file pathname is derived from the root directory, which can be set by the user,
the lowercase of chapter string must match a subdirectory name precisely,
and the definition is used to create the file name.
*)


module type Template_def_type = sig

  type userdefinition =
      {
	definition : string;
	chapter : string;
	author: string;
	date:string;
	data:string;
	comments:string list;
        needlist:string list;
      }

  val output_template : userdefinition -> unit 

  val set_root_dir : string-> unit  (* default is "/tmp" *)

end;;

(* 
Example:  The following code creates a template definition file 
   "/tmp/Trigonometry/azim_def.hl",
populated with the data from def1
*)

(*

open Template_def;;
let example1() = 
  let def1 = 
    {definition="azim";
     chapter="Trigonometry";
     author="Thomas C. Hales";
     date="Feb 7, 2010";
     data="<Insert HOL-Light code for theorem here>";
     comments=["This is just a test!"];
     needlist=["Multivariate/flyspeck.ml"];
    } in
 let _ = set_root_dir "/tmp" in
   output_template def1;;
example1();;

*)

module Template_def : Template_def_type = 
struct

  type userdefinition =
      {
	definition : string;
	chapter : string;
	author: string;
	date:string;
	data:string;
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

  (* Content *)

  let header ud = 
    let p = Printf.sprintf in
      unsplit "\n" c_enclose [
	pad_line;
	p"FLYSPECK - BOOK FORMALIZATION";
	space_line;
	p"Definition: %s" ud.definition;
	p"Chapter: %s" ud.chapter;
	p"Author: %s" ud.author;
	p"Date: %s" ud.date;
	pad_line;
      ];;

  let more_comments ud = 
   if (ud.comments =[]) then emptystring else
   "(*\n"^(join_lines ud.comments)^"\n*)\n\n\n";;

  let neededfiles ud = 
       if (ud.needlist =[]) then emptystring else
      "\n\n"^(unsplit "\n" (fun s -> "needs (flyspeck ^ \""^s^"\");;") ud.needlist)^"\n\n\n";;

  let body ud = 
    let p = Printf.sprintf in
    let uc = String.capitalize ud.definition in
      join_lines [
	p"module type %s_def_type = sig" uc;
        neededfiles ud;
	p"  val %s : thm" ud.definition;
	"end;;\n\n";
	p"module %s : %s_def_type = struct\n" uc uc;
	p" let %s = " ud.definition;
	ud.data;
	"\nend;;\n";
      ];;

  (* Output *)

  let rootdir =ref "/tmp";;
  let set_root_dir s = (rootdir := s);;

  let def_file  ud = (!rootdir)^sep^(String.lowercase ud.chapter)^sep^ud.definition^"_def.hl";;

  let save_stringarray filename xs = 
    let oc = open_out filename in
      for i=0 to List.length xs -1
      do
	output_string oc (List.nth xs i ^ "\n");
      done;
      close_out oc;;

  let output_template ud = save_stringarray (def_file ud) 
      [header ud;"\n\n\n";more_comments ud;body ud];;



end;;


