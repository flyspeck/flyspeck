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

type type_expr =
  { mutable desc: type_desc;
    mutable level: int;
    mutable id: int }

and type_desc =
    Tvar
  | Tarrow of label * type_expr * type_expr * commutable
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
  | Tsig_cltype of ident_t * dummy * dummy


(*** from ./typing/env.ml: ***)

type env_t = {
  values: (path_t * value_description) tbl;
  annotations: dummy;
  constrs: dummy;
  labels: dummy;
  types: dummy;
  modules: (path_t * module_type) tbl;
  modtypes: dummy;
  components: dummy;
  classes: dummy;
  cltypes: dummy;
  summary: dummy
};;


(* ------------------------------------------------------------------------- *)
(* Get the current environment and theorem names in an environment.          *)
(* ------------------------------------------------------------------------- *)

let rec list_of_tbl = function
  | Empty -> []
  | Node (t1, d, t2, _) -> list_of_tbl t1 @ d :: list_of_tbl t2;;

let rec get_simple_type = function
  | Tlink { desc = Tconstr (Pident p,[],_) } -> Some p.name
  | Tlink { desc = d } -> get_simple_type d
  | _ -> None;;

let rec mapSome f = function
  | []    -> []
  | x::xs -> match f x with
      | None   ->      mapSome f xs
      | Some y -> y :: mapSome f xs;;



let get_thm_names () =
  let getThmName (n,vd) =
    match get_simple_type vd.val_type.desc with
      | Some "thm" -> Some n
      | _ -> None
  and env = Obj.magic !Toploop.toplevel_env in
    List.append
      (mapSome (getThmName o (fun d -> (d.ident.name,snd d.data))) (list_of_tbl env.values))
      (List.flatten (mapSome (fun m -> match snd m.data with
           | Tmty_signature sg -> Some (mapSome (function
               | Tsig_value (i,v) -> getThmName (m.ident.name ^ "." ^ i.name, v)
               | _ -> None) sg)
            | _ -> None
         ) (list_of_tbl env.modules)));;

(* ------------------------------------------------------------------------- *)
(* Get the latest theorem names in an incremental fashion.                   *)
(* Return a list as well as "true" iff it's not the same as last time.       *)
(* ------------------------------------------------------------------------- *)

let toplevel_theorem_names =
  let names = ref (get_thm_names ()) in
  fun () ->
    let currentNames = sort (<) (get_thm_names ()) in
    let delta = subtract currentNames !names in
    names := currentNames;
    (currentNames, delta<>[]);;

(* ------------------------------------------------------------------------- *)
(* Put an assignment of a theorem database in the named file.                *)
(* ------------------------------------------------------------------------- *)

let make_database_assignment filename =
  let allnames,_ = toplevel_theorem_names() in
  let names = subtract allnames ["it"] in
  let entries = map (fun n -> "\""^n^"\","^n) names in
  let text = "theorems :=\n[\n"^
             end_itlist (fun a b -> a^";\n"^b) entries^"\n];;\n" in
  file_of_string filename text;;

(* ------------------------------------------------------------------------- *)
(* Update the database (regardless of whether anything has changed lately).  *)
(* ------------------------------------------------------------------------- *)

let update_database () =
  Format.print_string("Updating search database...\n");
  Format.print_flush();
  let allnames,_ = toplevel_theorem_names() in
  let names = subtract allnames ["it"] in                                      
  let entries = map (fun n -> "\""^n^"\","^n) names in             
  let text = "theorems :=\n[\n"^
             end_itlist (fun a b -> a^";\n"^b) entries^"\n];;\n" in
  let filename = Filename.temp_file "database" ".ml" in
  (file_of_string filename text;
   loadt filename;                                                          
   Sys.remove filename);;

(* ------------------------------------------------------------------------- *)
(* Search, with update call only if something has changed since last time.   *)
(* ------------------------------------------------------------------------- *)

let search =
  let rec immediatesublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> h1 = h2 & immediatesublist t1 t2 in
  let rec sublist l1 l2 =
    match (l1,l2) with
      [],_ -> true
    | _,[] -> false
    | (h1::t1,h2::t2) -> immediatesublist l1 l2 or sublist l1 t2 in
  let exists_subterm_satisfying p (n,th) = can (find_term p) (concl th)
  and name_contains s (n,th) = sublist (explode s) (explode n) in
  let rec filterpred tm =
    match tm with
      Comb(Var("<omit this pattern>",_),t) -> not o filterpred t
    | Comb(Var("<match theorem name>",_),Var(pat,_)) -> name_contains pat
    | Comb(Var("<match aconv>",_),pat) -> exists_subterm_satisfying (aconv pat)
    | pat -> exists_subterm_satisfying (can (term_match [] pat)) in
  fun pats -> let allnames,changed = toplevel_theorem_names() in
              (if changed then 
                (update_database())
               else ());
              itlist (filter o filterpred) pats (!theorems);;

(* ------------------------------------------------------------------------- *)
(* Update to bring things back to current state.                             *)
(* ------------------------------------------------------------------------- *)

theorems := [];;

update_database();;
