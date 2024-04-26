include Format;;

set_max_boxes 100;;


(* ------------------------------------------------------------------------- *)
(* Protection for HTML output                                                *)
(* ------------------------------------------------------------------------- *)
 let output_functions = get_all_formatter_output_functions();;
let make n s=
  let rec make_aux n s str =
    match n with
    | 0 -> str
    | _ -> make_aux (n - 1) s (str ^ s)
  in
  make_aux n s "";;

let new_output_functions (x,y,z,w) = set_all_formatter_output_functions x y  (fun () ->x "<br>" 0 4) (fun n -> x (make n "&#160;")  0 (6 * n));;
 let restore_output_functions (x,y,z,w) = set_all_formatter_output_functions x y z w;;

let pp_print_string' = pp_print_string;;
let print_string' = print_string;;
let rec pp_print_string fmt str = 
match (String.length str) with
| 0 -> ()
|_->
if (Str.string_match (Str.regexp "!") str 0)
then begin
pp_print_as fmt 1 "&#8704;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
if (Str.string_match (Str.regexp "\?") str 0)
then begin
pp_print_as fmt 1 "&#8707;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
if (Str.string_match (Str.regexp "--") str 0)
then begin
pp_print_as fmt 1 "&#8722;";
pp_print_string fmt (String.sub str 2 ((String.length str) - 2))
end
else
if (Str.string_match (Str.regexp "|-") str 0)
then begin
pp_print_as fmt 1 "&#8866;";
pp_print_string fmt (String.sub str 2 ((String.length str) - 2))
end
else
if (Str.string_match (Str.regexp "~") str 0)
then begin
pp_print_as fmt 1 "&#172;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
if (Str.string_match (Str.regexp "<=>") str 0)
then begin
pp_print_as fmt 1 "&#8660;";
pp_print_string fmt (String.sub str 3 ((String.length str) - 3))
end
else
if (Str.string_match (Str.regexp "==>") str 0)
then begin
pp_print_as fmt 1 "&#8658;";
pp_print_string fmt (String.sub str 3 ((String.length str) - 3))
end
else
if (Str.string_match (Str.regexp ">=") str 0)
then begin
pp_print_as fmt 1 "&#8805;";
pp_print_string fmt (String.sub str 2 ((String.length str) - 2))
end
else
if (Str.string_match (Str.regexp "<=") str 0)
then begin
pp_print_as fmt 1 "&#8804;";
pp_print_string fmt (String.sub str 2 ((String.length str) - 2))
end
else
if (Str.string_match (Str.regexp "\\\\/") str 0)
then begin
pp_print_as fmt 1 "&#8744;";
pp_print_string fmt (String.sub str 2 ((String.length str) - 2))
end
else
if (Str.string_match (Str.regexp "/\\\\") str 0)
then begin
pp_print_as fmt 1 "&#8743;";
pp_print_string fmt (String.sub str 2 ((String.length str) - 2))
end
else
if (Str.string_match (Str.regexp "\\\\") str 0)
then begin
pp_print_as fmt 1 "&#955;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
if (Str.string_match (Str.regexp ">") str 0)
then begin
pp_print_as fmt 1 "&#62;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
if (Str.string_match (Str.regexp "<") str 0)
then begin
pp_print_as fmt 1 "&#60;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
if (Str.string_match (Str.regexp " ") str 0)
then begin
pp_print_as fmt 1 "&#160;";
pp_print_string fmt (String.sub str 1 ((String.length str) - 1))
end
else
begin
pp_print_as fmt 1 (String.sub str 0 1);
pp_print_string fmt  (String.sub str 1 ((String.length str) - 1))
end;;
let print_string = pp_print_string std_formatter;;

(* ------------------------------------------------------------------------- *)
(* Determine binary operators that print without surrounding spaces.         *)
(* ------------------------------------------------------------------------- *)

let unspaced_binops = ref [","; ".."; "$"];;

(* ------------------------------------------------------------------------- *)
(* Binary operators to print at start of line when breaking.                 *)
(* ------------------------------------------------------------------------- *)

let prebroken_binops = ref ["==>"];;

(* ------------------------------------------------------------------------- *)
(* Force explicit indications of bound variables in set abstractions.        *)
(* ------------------------------------------------------------------------- *)

(* let print_unambiguous_comprehensions = ref false;; *)

   (* ------------------------------------------------------------------------- *)
   (* Print the universal set UNIV:A->bool as "(:A)".                           *)
   (* ------------------------------------------------------------------------- *)

   let typify_universal_set = ref true;;

   (* ------------------------------------------------------------------------- *)
   (* Flag controlling whether hypotheses print.                                *)
   (* ------------------------------------------------------------------------- *)

   let print_all_thm = ref true;;

   (* ------------------------------------------------------------------------- *)
   (* Flag determining whether interface/overloading is reversed on printing.   *)
   (* ------------------------------------------------------------------------- *)
   let reverse_interface_mapping = ref true;;

   (* ------------------------------------------------------------------------- *)
   (* Uses the_interface to lookup the names of operators                       *)
   (* ------------------------------------------------------------------------- *)
   let reverse_interface (s0,ty0) =
   if not(!reverse_interface_mapping) then s0 else
   try fst(find (fun (s,(s',ty)) -> s' = s0 & can (type_match ty ty0) [])
                (!the_interface))
   with Failure _ -> s0;;

   (* ------------------------------------------------------------------------- *)
   (* Get the name of a constant or variable.                                   *)
   (* ------------------------------------------------------------------------- *)

   let name_of tm =
   match tm with
   Var(x,ty) | Const(x,ty) -> x
  | _ -> "";;

  (* ------------------------------------------------------------------------- *)
  (* Printer for types.                                                        *)
  (* ------------------------------------------------------------------------- *)

  let pp_print_type,pp_print_qtype =
  let soc sep flag ss =
  if ss = [] then "" else
  let s = end_itlist (fun s1 s2 -> s1^sep^s2) ss in
  if flag then "("^s^")" else s in
  let rec sot pr ty =
  try dest_vartype ty with Failure _ ->
  match dest_type ty with
  con,[] -> con
  | "fun",[ty1;ty2] -> soc "->" (pr > 0) [sot 1 ty1; sot 0 ty2]
    | "sum",[ty1;ty2] -> soc "+" (pr > 2) [sot 3 ty1; sot 2 ty2]
    | "prod",[ty1;ty2] -> soc "#" (pr > 4) [sot 5 ty1; sot 4 ty2]
    | "cart",[ty1;ty2] -> soc "^" (pr > 6) [sot 6 ty1; sot 7 ty2]
    | con,args -> (soc "," true (map (sot 0) args))^con in
  (fun fmt ty -> pp_print_string fmt (sot 0 ty)),
  (fun fmt ty -> pp_print_string fmt ("`:" ^ sot 0 ty ^ "`"));;

(* ------------------------------------------------------------------------- *)
(* This returns L and R  if OP = c  in  (tm:= L OP R)                        *)
(* ------------------------------------------------------------------------- *)
let dest_binary' c tm =
try let il,r = dest_comb tm in
let i,l = dest_comb il in
if i = c or
(is_const i & is_const c &
	  reverse_interface(dest_const i) = reverse_interface(dest_const c))
then l,r else fail()
with Failure _ -> failwith "dest_binary";;

(* ------------------------------------------------------------------------- *)
(* string -> bool   Lookup to see if operator of string is right assoc       *)
(* ------------------------------------------------------------------------- *)
let is_right_assoc s =
match snd(get_infix_status s) with
|"right" -> true 
      | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* num -> bool                                                               *)
(* ------------------------------------------------------------------------- *)
let rec power_of_10 n =
if abs_num n </ num 1 then false
else if n =/ num 1 then true
else power_of_10 (n // num 10);;

(* ------------------------------------------------------------------------- *)
(* term -> bool           converts bool term to ocaml bool                   *)
(* ------------------------------------------------------------------------- *)
let bool_of_term t =
match t with
Const("T",_) -> true
| Const("F",_) -> false
    | _ -> failwith "bool_of_term";;

(* ------------------------------------------------------------------------- *)
(* term -> int            converts ASCII term into int equiv                 *)
(* ------------------------------------------------------------------------- *)
let code_of_term t =
let f,tms = strip_comb t in
if not(is_const f & fst(dest_const f) = "ASCII")
or not(length tms = 8) then failwith "code_of_term"
else
itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
(map bool_of_term (rev tms)) 0;;

(* ------------------------------------------------------------------------- *)
(*                       *)
(* ------------------------------------------------------------------------- *)
let rec dest_clause tm =
let pbod = snd(strip_exists(body(body tm))) in
let s,args = strip_comb pbod in
if name_of s = "_UNGUARDED_PATTERN" & length args = 2 then
[rand(rator(hd args));rand(rator(hd(tl args)))]
else if name_of s = "_GUARDED_PATTERN" & length args = 3 then
[rand(rator(hd args)); hd(tl args); rand(rator(hd(tl(tl args))))]
else failwith "dest_clause" ;;

(* ------------------------------------------------------------------------- *)
(*                         *)
(* ------------------------------------------------------------------------- *)
let rec dest_clauses tm =
let s,args = strip_comb tm in
if name_of s = "_SEQPATTERN" & length args = 2 then
dest_clause (hd args)::dest_clauses(hd(tl args))
else [dest_clause tm];;


(* ------------------------------------------------------------------------- *)
(* Allow the installation of user printers. Must fail quickly if N/A.        *)
(* ------------------------------------------------------------------------- *)
let install_user_printer,delete_user_printer,try_user_printer =
let user_printers = ref ([]:(string*(term->unit))list) in
(fun pr -> user_printers := pr::(!user_printers)),
(fun s -> user_printers := snd(remove (fun (s',_) -> s = s')
				      (!user_printers))),
(fun tm -> tryfind (fun (_,pr) -> pr tm) (!user_printers));;





(* ------------------------------------------------------------------------- *)
(* Type to determine how/(what tag) to print                                 *)
(* ------------------------------------------------------------------------- *)
type term_type = Numeral | List | Char_list | Generalized_abstraction |
Empty | Universal | G_spec | Let | Decimal | Match | Function |
	  Insert | Cond | Other;;

(* ------------------------------------------------------------------------- *)
(* term -> term_type                                                         *)
(* ------------------------------------------------------------------------- *)
let rec get_term_type tm = 
if is_numeral tm then Numeral
else if is_list tm then
begin
try if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char" 
then fail()
else Char_list with Failure _ -> List
end
else if is_gabs tm then Generalized_abstraction
else 
begin
let hop,args = strip_comb tm in
let s0 = name_of hop
and ty0 = type_of hop in
let s = reverse_interface (s0,ty0) in
if s = "EMPTY" & is_const tm & args = [] then Empty	  
else if s = "UNIV" & !typify_universal_set & is_const tm & args = [] 
then Universal
else if s = "INSERT" & 
is_const (snd(splitlist (dest_binary "INSERT") tm))  & 
fst(
    dest_const (
		snd(
		    splitlist (
			       dest_binary "INSERT") tm))) = "EMPTY" then Insert
else if (s = "GSPEC") &
fst(dest_const (
		(rator o 
		       fst o dest_comb o 
		       fst o dest_comb o 
		       snd o strip_exists 
		       o body o rand)tm )) = "SETSPEC" then G_spec
else if is_let tm then Let
else if s = "DECIMAL" &
(power_of_10 ((dest_numeral o hd o tl)args)) then Decimal
else if s = "_MATCH" &
length args = 2 then Match
else if s = "_FUNCTION" &
length args = 1 then Function 
else if s = "COND" & length args = 3 then Cond
else Other
end;;


(* ------------------------------------------------------------------------- *)
(* Printer for terms.                                                        *)
(* ------------------------------------------------------------------------- *)
let pp_print_term = 
fun fmt -> 
let rec print_subterm prec tm =
try try_user_printer tm with Failure _ ->
let hop,args = strip_comb tm in
let s0 = name_of hop
and ty0 = type_of hop in
let s = reverse_interface (s0,ty0) in
match get_term_type tm with
| Numeral ->
		  begin
		    open_tag "span class=\"Numeral\"";
		    pp_print_string fmt (string_of_num(dest_numeral tm));
		    close_tag();
		  end;
	      |Char_list ->
begin
open_tag "span class=\"Char_list\"";
pp_print_string fmt (
		     "\"" ^ String.escaped (implode (map (
							  String.make 1 o 
								      Char.chr o 
								      code_of_term ) 
							 (dest_list tm) )) ^ "\"");
close_tag();
end;
|List ->
		 begin
		   open_tag "span class=\"List\"";
		   pp_print_string fmt "[";
		   print_term_sequence "; " 0 (dest_list tm);
		   pp_print_string fmt "]";
		   close_tag();
		 end;
	      |Generalized_abstraction ->
begin
open_tag "span class=\"Generalized_abstraction\"";
print_binder prec tm;
close_tag();
end
|Empty -> 
		 begin
		   open_tag "span class=\"Empty\"";
		   pp_print_string fmt "{}";
		   close_tag();
		 end
	      |Universal -> 
begin
let ty = fst(dest_fun_ty(type_of tm)) in
begin
open_tag "span class=\"Universal\"";
pp_print_string fmt "(:";
pp_print_type fmt ty;
pp_print_string fmt ")";
close_tag();
end
end;
|Insert ->
		 begin
		   open_tag "span class=\"Insert\"";
		   pp_print_string fmt "{";
		   print_term_sequence ", " 14 (
		     fst(
		       splitlist (dest_binary "INSERT") tm));
		   pp_print_string fmt "}";
		   close_tag();
		 end;
	      |G_spec ->
begin

let evs,bod = strip_exists(body(rand tm)) in
let bod1,fabs = dest_comb bod in
let bod2,babs = dest_comb bod1 in
(* let c = rator bod2 in*)

(* (let fvs = frees fabs and bvs = frees babs in
	if not(!print_unambiguous_comprehensions) &
	set_eq evs
	(if (length fvs <= 1 or bvs = []) then fvs
	    else intersect fvs bvs)
	then ()
	else (print_term_sequence "," 14 evs;
				  pp_print_string fmt " | ")); 
   *)
open_tag "span class=\"G_spec\"";
pp_print_string fmt "{";
print_subterm 0 fabs;
pp_print_string fmt " | ";
print_subterm 0 babs;
pp_print_string fmt "}";
close_tag();
end;
|Let -> 
		 begin
		   open_tag "span class=\"Let\"";
		   let eqs,bod = dest_let tm in
		     (if prec = 0 then pp_open_hvbox fmt 0
		      else (pp_open_hvbox fmt 1; pp_print_string fmt "(");
		      pp_print_string fmt "let ";
		      print_subterm 0 (mk_eq(hd eqs));
		      do_list (fun (v,t) -> pp_print_break fmt 1 0;
				 pp_print_string fmt "and ";
				 print_subterm 0 (mk_eq(v,t)))
			(tl eqs);
		      pp_print_string fmt " in";
		      pp_print_break fmt 1 0;
		      print_subterm 0 bod;
		      if prec = 0 then () else pp_print_string fmt ")";
		      pp_close_box fmt ());
		     close_tag();
		 end;
	      |Decimal ->
begin
open_tag "span class=\"Decimal\"";
let n_num = dest_numeral (hd args)
and n_den = dest_numeral (hd(tl args)) in
let s_num = string_of_num(quo_num n_num n_den) in
let s_den = implode(
		    tl(explode(string_of_num
			       (n_den +/ (mod_num n_num n_den))))) in
pp_print_string fmt(
		    "#"^s_num^(if n_den = num 1 then "" else ".")^s_den);
close_tag();
end;
|Match ->
		 begin
		   
		   open_tag "span class=\"Match\"";
		   let cls = dest_clauses(hd(tl args)) in
		     (if prec = 0 then () else pp_print_string fmt "(";
		      pp_open_hvbox fmt 0;
		      pp_print_string fmt "match ";
		      print_subterm 0 (hd args);
		      pp_print_string fmt " with";
		      pp_print_break fmt 1 2;
		      print_clauses cls;
		      pp_close_box fmt ();
		      if prec = 0 then () else pp_print_string fmt ")");
		     close_tag();
		 end
	      |Function ->
begin
open_tag "span class=\"Function\"";
let cls = dest_clauses(hd args) in
(if prec = 0 then () else pp_print_string fmt "(";
    pp_open_hvbox fmt 0;
    pp_print_string fmt "function";
    pp_print_break fmt 1 2;
    print_clauses cls;
    pp_close_box fmt ();
    if prec = 0 then () else pp_print_string fmt ")");
close_tag();
end
|Cond ->
		 begin
		   open_tag "span class=\"Cond\"";
		   
		   (if prec = 0 then () else pp_print_string fmt "(";
		    pp_open_hvbox fmt (-1);
		    pp_print_string fmt "if ";
		    print_subterm 0 (hd args);
		    pp_print_break fmt 0 0;
		    pp_print_string fmt " then ";
		    print_subterm 0 (hd(tl args));
		    pp_print_break fmt 0 0;
		    pp_print_string fmt " else ";
		    print_subterm 0 (hd(tl(tl args)));
		    pp_close_box fmt ();
		    if prec = 0 then () else pp_print_string fmt ")");
		   close_tag();
		 end
	      |_ ->
begin
if is_prefix s & length args = 1 then
(if prec = 1000 then pp_print_string fmt "(" else ();
    pp_print_string fmt s;
    (if isalnum s or
	s = "--" &
	length args = 1 &
	(try let l,r = dest_comb(hd args) in
	     let s0 = name_of l in
	     s0 = "--" or
	     mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
	     with Failure _ -> false) or
	     s = "~" & length args = 1 & is_neg(hd args)
	     then pp_print_string fmt " " else ());
    print_subterm 999 (hd args);
    if prec = 1000 then pp_print_string fmt ")" else ())
else if parses_as_binder s & length args = 1 & is_gabs (hd args) then
print_binder prec tm
else if can get_infix_status s & length args = 2 then
let bargs =
if is_right_assoc s then
let tms,tmt = splitlist (dest_binary' hop) tm in tms@[tmt]
else
let tmt,tms = rev_splitlist (dest_binary' hop) tm in tmt::tms in
let newprec = fst(get_infix_status s) in
(if newprec <= prec then
    (pp_open_hvbox fmt 1; pp_print_string fmt "(")
		   else pp_open_hvbox fmt 0;
		   print_subterm newprec (hd bargs);
		   do_list (fun x -> if mem s (!unspaced_binops) then ()
				else if mem s (!prebroken_binops)
				then pp_print_break fmt 1 0
				else pp_print_string fmt " ";
				pp_print_string fmt s;
				if mem s (!unspaced_binops)
				then pp_print_break fmt 0 0
				else if mem s (!prebroken_binops)
				then pp_print_string fmt " "
				else pp_print_break fmt 1 0;
				print_subterm newprec x) (tl bargs);
				if newprec <= prec then pp_print_string fmt ")" else ();
				pp_close_box fmt ())
    else if (is_const hop or is_var hop) & args = [] then
    let s' = if parses_as_binder s or can get_infix_status s or is_prefix s
    then "("^s^")" else s in
    pp_print_string fmt s'
    else
    let l,r = dest_comb tm in
    (pp_open_hvbox fmt 0;
		   if prec = 1000 then pp_print_string fmt "(" else ();
		   print_subterm 999 l;
		   (if try mem (fst(dest_const l)) ["real_of_num"; "int_of_num"]
		       with Failure _ -> false
		       then () else pp_print_space fmt ());
		   print_subterm 1000 r;
		   if prec = 1000 then pp_print_string fmt ")" else ();
		   pp_close_box fmt ())
    
    end
    
    

    (* Code is safe down here *)
    


    
    and   print_term_sequence sep prec tms =
    if tms = [] then () else
    (print_subterm prec (hd tms);
		   let ttms = tl tms in
		   if ttms = [] then ()
		   else (pp_print_string fmt sep; print_term_sequence sep prec ttms))
					 
					 
					 and   print_clauses cls =
					 match cls with
					 [c] -> print_clause c
					 | c::cs -> (print_clause c;
		      pp_print_break fmt 1 0;
		      pp_print_string fmt "| ";
		      print_clauses cs)
	      
      and   print_binder prec tm =
	let absf = is_gabs tm in
	let s = if absf then "\\" else name_of(rator tm) in
	let rec collectvs tm =
		   if absf then
		     if is_abs tm then
		       let v,t = dest_abs tm in
		       let vs,bod = collectvs t in (false,v)::vs,bod
		     else if is_gabs tm then
		       let v,t = dest_gabs tm in
		       let vs,bod = collectvs t in (true,v)::vs,bod
		     else [],tm
		   else if is_comb tm & name_of(rator tm) = s then
		     if is_abs(rand tm) then
		       let v,t = dest_abs(rand tm) in
		       let vs,bod = collectvs t in (false,v)::vs,bod
		     else if is_gabs(rand tm) then
		       let v,t = dest_gabs(rand tm) in
		       let vs,bod = collectvs t in (true,v)::vs,bod
		     else [],tm
		   else [],tm in
	let vs,bod = collectvs tm in
	  begin
	    open_tag "span class=\"binder\"";
	    (if prec = 0 then pp_open_hvbox fmt 4
	    else (pp_open_hvbox fmt 5; pp_print_string fmt "("));
	   pp_print_string fmt s;
	   (if isalnum s then pp_print_string fmt " " else ());
	   do_list (fun (b,x) ->
		      (if b then pp_print_string fmt "(" else ());
		      print_subterm 0 x;
		      (if b then pp_print_string fmt ")" else ());
		      pp_print_string fmt " ") (butlast vs);
	   (if fst(last vs) then pp_print_string fmt "(" else ());
	   print_subterm 0 (snd(last vs));
	   (if fst(last vs) then pp_print_string fmt ")" else ());
	   pp_print_string fmt ".";
	   (if length vs = 1 then pp_print_string fmt " "
	    else pp_print_space fmt ());
	   print_subterm 0 bod;
	   (if prec = 0 then () else pp_print_string fmt ")");
	   pp_close_box fmt ();
	   close_tag();
	  end;
	    
      and print_clause cl =
	match cl with
	    [p;g;r] -> (print_subterm 1 p;
			pp_print_string fmt " when ";
			print_subterm 1 g;
			pp_print_string fmt " -> ";
			print_subterm 1 r)
		   | [p;r] -> (print_subterm 1 p;
			       pp_print_string fmt " -> ";
			       print_subterm 1 r)
      in print_subterm 0;;
  
(* ------------------------------------------------------------------------- *)
(* Print term with quotes.                                                   *)
(* ------------------------------------------------------------------------- *)

let pp_print_qterm fmt tm =
new_output_functions output_functions;
open_tag "HTML";
open_tag "HEAD";
open_tag "TITLE";
close_tag ();
open_tag "style type=\"text/css\"";
pp_print_as fmt 0 ".real {color:teal; background-color:white; font-weight:bold; text-align:center;} .num {color:fuchsia; background-color:white; font-weight:bold; text-align:center;} .int {color:olive; background-color:white; font-weight:bold; text-align:center;}";
close_tag();
close_tag();
open_tag "BODY";
open_tag "TT";
pp_print_term fmt tm;
close_tag();
close_tag();
close_tag();
restore_output_functions output_functions;;


(* ------------------------------------------------------------------------- *)
(* Printer for theorems.                                                     *)
(* ------------------------------------------------------------------------- *)

let pp_print_thm fmt th =
let asl,tm = dest_thm th in
(if not (asl = []) then
    (if !print_all_thm then
      (pp_print_term fmt (hd asl);
		     do_list (fun x -> pp_print_string fmt ",";
				  pp_print_space fmt ();
				  pp_print_term fmt x)
		     (tl asl))
      else pp_print_string fmt "...";
      pp_print_space fmt ())
    else ();
    pp_open_hbox fmt();

    pp_print_string fmt "|- ";
    pp_print_term fmt tm;
    pp_close_box fmt ());;

let pp_print_thm' = pp_print_thm;;
let pp_print_thm fmt tm = 
new_output_functions output_functions;
open_tag "HTML";
open_tag "HEAD";
open_tag "TITLE";
close_tag();
open_tag "style type=\"text/css\"";
pp_print_as fmt 0 ".real {color:teal; background-color:white; font-weight:bold; text-align:center;} .num {color:fuchsia; background-color:white; font-weight:bold; text-align:center;} .int {color:olive; background-color:white; font-weight:bold; text-align:center;}";
close_tag();
close_tag();
open_tag "BODY";
open_tag "TT";
pp_print_thm fmt tm;
close_tag();
close_tag();
close_tag();
restore_output_functions output_functions;;


(* ------------------------------------------------------------------------- *)
(* Print on standard output.                                                 *)
(* ------------------------------------------------------------------------- *)

let print_type = pp_print_type std_formatter;;
let print_qtype = pp_print_qtype std_formatter;;
let print_term = pp_print_term std_formatter;;
let print_qterm = pp_print_qterm std_formatter;;
let print_thm = pp_print_thm std_formatter;;

(* ------------------------------------------------------------------------- *)
(* Install all the printers.                                                 *)
(* ------------------------------------------------------------------------- *)

#install_printer print_qtype;;
#install_printer print_qterm;;
#install_printer print_thm;;

(* ------------------------------------------------------------------------- *)
(* Conversions to string.                                                    *)
(* ------------------------------------------------------------------------- *)

let print_to_string printer =
let sbuff = ref "" in
let output s m n = sbuff := (!sbuff)^(String.sub s m n) and flush() = () in
let fmt = make_formatter output flush in
ignore(pp_set_max_boxes fmt 100);
fun i -> ignore(printer fmt i);
ignore(pp_print_flush fmt ());
let s = !sbuff in sbuff := ""; s;;

let string_of_type = print_to_string pp_print_type;;
let string_of_term = print_to_string pp_print_term;;
let string_of_thm = print_to_string pp_print_thm;;

(* ------------------------------------------------------------------------- *)
(* Print types                                                               *)
(* ------------------------------------------------------------------------- *)

let print_typed_var tm =
let s,ty = dest_var tm in
begin
open_tag("span class=\""^(string_of_type ty)^"\"");
print_string(s);
close_tag();
end in
install_user_printer("print_typed_var", print_typed_var);;
set_mark_tags true;;

let pp_print_string = pp_print_string';;
let print_string = print_string';;



