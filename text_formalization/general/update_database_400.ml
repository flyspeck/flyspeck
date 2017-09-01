(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Update theorem search                                                      *)
(* Date: 2010-07-16                                                           *)
(*                                                                            *)
(* 2012-09-06: JRH fixed up for OCaml 4.0 and added alphabetic sorting.       *)
(* ========================================================================== *)

(* ========================================================================= *)
(* Create search database from OCaml / modify search database dynamically.   *)
(*                                                                           *)
(* This file assigns to "theorems", which is a list of name-theorem pairs.   *)
(* The core system already has such a database set up. Use this file if you  *)
(* want to update the database beyond the core, so you can search it.        *)
(*                                                                           *)
(* The trickery to get at the OCaml environment is due to Roland Zumkeller.  *)
(* It works by copying some internal data structures and casting into the    *)
(* copy using Obj.magic.                                                     *)
(* ========================================================================= *)


(* module Update_database_310 = struct *)

(* Execute any OCaml expression given as a string. *)

let exec = ignore o Toploop.execute_phrase false Format.std_formatter
  o !Toploop.parse_toplevel_phrase o Lexing.from_string;;

type dummy;;

(* ------------------------------------------------------------------------- *)
(* Basic data structures copied from OCaml. May be version-dependent.        *)
(* ------------------------------------------------------------------------- *)

type label = int;;

(*** from ./typing/ident.ml: ***)

type ident_t = { stamp: int; name: string; mutable flags: int };;

type 'a tbl =
    Empty
  | Node of 'a tbl * 'a data * 'a tbl * int

and 'a data =
  { ident: ident_t;
    data: 'a;
    previous: 'a data option };;

(*** from ./typing/path.ml: ***)

type path_t =
    Pident of ident_t
  | Pdot of path_t * string * int
  | Papply of path_t * path_t;;

(*** from typing/types.ml: ***)

exec (
"type type_expr =
  { mutable desc: type_desc;
    mutable level: int;
    mutable id: int }

and type_desc =
" ^
(if String.sub Sys.ocaml_version 0 1 = "4"
 then "Tvar of string option\n"
 else "Tvar\n") ^
" | Tarrow of label * type_expr * type_expr * commutable
  | Ttuple of type_expr list
  | Tconstr of path_t * type_expr list * abbrev_memo ref
  | Tobject of type_expr * (path_t * type_expr list) option ref
  | Tfield of string * field_kind * type_expr * type_expr
  | Tnil
  | Tlink of type_expr
  | Tsubst of type_expr
  | Tvariant of row_desc
  | Tunivar
  | Tpoly of type_expr * type_expr list

and row_desc =
    { row_fields: (label * row_field) list;
      row_more: type_expr;
      row_bound: type_expr list;
      row_closed: bool;
      row_fixed: bool;
      row_name: (path_t * type_expr list) option }

and row_field =
    Rpresent of type_expr option
  | Reither of bool * type_expr list * bool * row_field option ref
  | Rabsent

and abbrev_memo =
    Mnil
  | Mcons of path_t * type_expr * type_expr * abbrev_memo
  | Mlink of abbrev_memo ref

and field_kind =
    Fvar of field_kind option ref
  | Fpresent
  | Fabsent

and commutable =
    Cok
  | Cunknown
  | Clink of commutable ref;;
");;

type value_description =
  { val_type: type_expr;
    val_kind: dummy };;

type module_type =
    Tmty_ident of path_t
  | Tmty_signature of signature
  | Tmty_functor of ident_t * module_type * module_type

and signature = signature_item list

and signature_item =
    Tsig_value of ident_t * value_description
  | Tsig_type of ident_t * dummy * dummy
  | Tsig_exception of ident_t * dummy
  | Tsig_module of ident_t * module_type * dummy
  | Tsig_modtype of ident_t * dummy
  | Tsig_class of ident_t * dummy * dummy
  | Tsig_cltype of ident_t * dummy * dummy;;

(*** from ./typing/env.ml: ***)

exec (
"type env_t = {\n" ^
 (if String.sub Sys.ocaml_version 0 1 = "4"
  then "values: ((path_t * value_description) * bool ref) tbl;\n"
  else "values: (path_t * value_description) tbl;\n") ^
 (if (let v = String.sub Sys.ocaml_version 0 4 in v = "3.09" || v = "3.10")
  then ""
  else "annotations: dummy;\n") ^
" constrs: dummy;
  labels: dummy;\n" ^
(if String.sub Sys.ocaml_version 0 1 = "4"
 then "constrs_by_path: dummy;\n"
 else "") ^
" types: dummy;\n" ^
(if String.sub Sys.ocaml_version 0 1 = "4"
  then "modules: ((path_t * module_type) * bool ref) tbl;\n"
  else "modules: (path_t * module_type) tbl;\n") ^
" modtypes: dummy;
  components: dummy;
  classes: dummy;
  cltypes: dummy;
  summary: dummy;\n" ^
(if String.sub Sys.ocaml_version 0 1 = "4"
 then "local_constraints: dummy;
       gadt_instances: dummy;
       in_signature: dummy;
       };;\n"
 else "};;\n"));;

(* ------------------------------------------------------------------------- *)
(* End of basic data structures copied from OCaml.                           *)
(* ------------------------------------------------------------------------- *)

(* Iterate over the entries of a table. *)

let rec iterTbl (f : ident_t -> 'a -> unit) = function
  | Empty -> ()
  | Node (t1,d,t2,_) ->
      f d.ident d.data;
      iterTbl f t1;
      iterTbl f t2;;

(* If the given type is simple return its name, otherwise None. *)

let rec get_simple_type = function
  | Tlink { desc = Tconstr (Pident p,[],_) } -> Some p.name
  | Tlink { desc = d } -> get_simple_type d
  | _ -> None;;

(* Evaluate any OCaml expression given as a string. *)

let eval n =
  exec ("let buf__ = ( " ^ n ^ " );;");
  Obj.magic (Toploop.getvalue "buf__");;

(* Register all theorems added since the last update. *)

let thm_hashtable = Hashtbl.create 5000;;

exec (                                          
"let update_database =             
  let lastStamp = ref 0                  
  and currentStamp = ref 0
  and thms = thm_hashtable in

  let ifNew f i x =
    if i.stamp > !lastStamp then
      ((if i.stamp > !currentStamp then currentStamp := i.stamp);
       f i x) in

  let rec regVal pfx = ifNew (fun i vd ->
    let n = pfx ^ i.name in
      if n <> \"buf__\" then
        (if get_simple_type vd.val_type.desc = Some \"thm\"
         then Hashtbl.replace thms n (eval n)
         else Hashtbl.remove thms n))

  and regMod pfx = ifNew (fun i mt ->
       match mt with
         | Tmty_signature sg ->
             let pfx' = pfx ^ i.name ^ \".\" in
             List.iter (function
               | Tsig_value (i',vd) -> regVal pfx' i' vd
               | Tsig_module (i',mt',_) -> regMod pfx' i' mt'
               | _ -> ()) sg
         | _ -> ())

  in fun () ->
    let env = Obj.magic !Toploop.toplevel_env in
" ^
(if String.sub Sys.ocaml_version 0 1 = "4"
 then "iterTbl (fun i ((_,vd),_) -> regVal \"\" i vd) env.values;
       iterTbl (fun i ((_,mt),_) -> regMod \"\" i mt) env.modules;
      "
 else
      "iterTbl (fun i (_,vd) -> regVal \"\" i vd) env.values;
       iterTbl (fun i (_,mt) -> regMod \"\" i mt) env.modules;
      ") ^
"   lastStamp := !currentStamp;
    theorems := Hashtbl.fold (fun s t l -> (s,t)::l) thms [];;
");;

(* ------------------------------------------------------------------------- *)
(* Search (automatically updates)                                            *)
(* ------------------------------------------------------------------------- *)

let omit t = mk_comb(mk_var("<omit this pattern>",W mk_fun_ty (type_of t)),t);;

let exactly t = mk_comb(mk_var("<match aconv>",W mk_fun_ty (type_of t)),t);;

let name s = mk_comb(mk_var("<match theorem name>",W mk_fun_ty aty),
                     mk_var(s,aty));;

let full t = mk_comb(mk_var("<full term>",W mk_fun_ty (type_of t)),t);;

let rewrite t = mk_comb(mk_var("<rewrite>",W mk_fun_ty (type_of t)),t);;

let regexp s = mk_comb(mk_var("<regexp>",W mk_fun_ty aty),
                     mk_var(s,aty));;

let disjunct pr =
  let u = mk_pair pr in
  let ty = type_of u in
  let h = mk_var ("<search_or>",(mk_type("fun",[ty;aty]))) in
    mk_comb (h,u);;


(* very rough measure of the size of a printed term *)
let rec term_length =
  let n = `NUMERAL` in
  let d = `DECIMAL` in
  function
  | Abs(s,x) -> 1 + term_length x
  | Comb(s,x) -> if ((s = n) || (s = d)) then 2
    else ( term_length s + term_length x)
  | _ -> 1;;

let sortlength_thml thml =
  let ltml = map
   (function (s,t) as r -> (term_length (concl t),r)) thml in
  let stml = sort (fun (a,_) (b,_) -> (a < b)) ltml in
    map snd stml;;


(* main search function *)

let search_thml term_matcher =
  let rec immediatesublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> h1 = h2 && immediatesublist t1 t2 in
  let rec sublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> immediatesublist l1 l2 || sublist l1 t2 in

  let rec conjuncts t =
    let t' = snd (strip_forall t) in
      if (is_conj t') then (let (a,b) = dest_conj t' in conjuncts a @ conjuncts b) else [t'] in

  let heads t =
    let c = map (fst o dest_eq) (filter (is_eq) (conjuncts t)) in
    let h = map (fst o strip_comb) c in
    let hc = filter (is_const) h in
      map (fst o dest_const) hc in

  let is_rewrite t (n,th) =
    mem (fst(dest_const t)) (heads(snd( dest_thm th))) in

  let name_matches_regexp s (n,th) =
    let pat = Str.regexp (".*"^s) in
      Str.string_match pat n 0 in

  let exists_subterm_satisfying p (n,th) = can (find_term p) (concl th) in
  let exists_fullterm_satisfying p (n,th) =  p (concl th) in
  let name_contains s (n,th) = sublist (explode s) (explode n) in
  let rec filterpred tm =
    match tm with
      Comb(Var("<omit this pattern>",_),t) -> not o filterpred t
    | Comb(Var("<match theorem name>",_),Var(pat,_)) -> name_contains pat
    | Comb(Var("<regexp>",_),Var(pat,_)) -> name_matches_regexp pat
    | Comb(Var("<search_or>",_),t) ->
        let (pat1,pat2) = dest_pair t in
        (fun (n,th) -> exists_subterm_satisfying (can (term_matcher pat1)) (n,th) ||
           exists_subterm_satisfying (can (term_matcher pat2)) (n,th))
    | Comb(Var("<rewrite>",_),t) -> is_rewrite t
    | Comb(Var("<match aconv>",_),pat) -> exists_subterm_satisfying (aconv pat)
    | Comb(Var("<full term>",_),pat) -> exists_fullterm_satisfying (can (term_matcher pat))
    | pat -> exists_subterm_satisfying (can (term_matcher pat)) in
  fun pats thml -> update_database ();
    if (pats = []) then failwith ("keywords: omit (term), name (string),"^
                                    " disjunct (term,term), "^
      " regexp (string), exactly (term), full (term), rewrite (term constant)") else
        (itlist (filter o filterpred) pats thml);;


let search pat = sort (increasing fst) (search_thml (term_match [])  pat (!theorems));;

(* ------------------------------------------------------------------------- *)
(* Update to bring to current state.                                         *)
(* ------------------------------------------------------------------------- *)

update_database ();;

(* end;; *)
