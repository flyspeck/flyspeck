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

(*** from ./typing/env.ml: ***)

type env_t = {
  values: (path_t * value_description) tbl;
  annotations: dummy;
  constrs: dummy;
  labels: dummy;
  types: dummy;
  modules: dummy;
  modtypes: dummy;
  components: dummy;
  classes: dummy;
  cltypes: dummy;
  summary: dummy
};;

(* ------------------------------------------------------------------------- *)
(* Find difference between environments.                                     *)
(* ------------------------------------------------------------------------- *)

(*** From ./typing/env.ml ***)

let rec find_stamp s = function
    None ->
      raise Not_found
  | Some k ->
      if k.ident.stamp = s then k.data else find_stamp s k.previous;;

let rec find_same id = function
    Empty ->
      raise Not_found
  | Node(l, k, r, _) ->
      let c = compare id.name k.ident.name in
      if c = 0 then
        if id.stamp = k.ident.stamp
        then k.data
        else find_stamp id.stamp k.previous
      else
        find_same id (if c < 0 then l else r);;

let rec keys_aux stack accu = function
    Empty ->
      begin match stack with
        [] -> accu
      | a :: l -> keys_aux l accu a
      end
  | Node(l, k, r, _) ->
      keys_aux (l :: stack) (k.ident :: accu) r;;

let keys tbl = keys_aux [] [] tbl;;

let diff_keys tbl1 tbl2 =
  let keys2 = keys tbl2 in
  List.filter
    (fun id ->
      match find_same id tbl2 with Pident _, _ ->
        (try ignore (find_same id tbl1); false with Not_found -> true)
      | _ -> false)
    keys2;;

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

let rec filter_nones = function
  | []         -> []
  | Some x::xs -> x :: filter_nones xs
  | None::xs   ->      filter_nones xs;;

let get_raw_environment() = (Obj.magic (!Toploop.toplevel_env) :env_t);;

let get_thm_names (ents:(path_t * value_description) data list) =
  itlist (fun d ns ->
            match get_simple_type (snd d.data).val_type.desc with
           | Some "thm" -> d.ident.name::ns
           | _ -> ns)
         ents [];;

let get_thm_names' env = get_thm_names(list_of_tbl env.values);;

(* ------------------------------------------------------------------------- *)
(* Get the latest theorem names in an incremental fashion.                   *)
(* Return a list as well as "true" iff it's not the same as last time.       *)
(* ------------------------------------------------------------------------- *)

let toplevel_theorem_names =
  let latest_raw_environment = ref(get_raw_environment()) in
  let latest_thm_list = 
    (ref(uniq(mergesort(<) (get_thm_names'(!latest_raw_environment))))) in
  fun () ->
    let env = !latest_raw_environment
    and env' = get_raw_environment() in
    let thms = !latest_thm_list in
    if env' == env then thms,false else
    let newids = diff_keys env.values env'.values in
    let newenv = 
      map (fun i -> {ident=i; data=find_same i env'.values; previous=None})
          newids in
    let newthms = uniq(sort (<) (get_thm_names newenv)) in
    let allthms = uniq(merge (<) thms newthms) in
    (latest_raw_environment := env';
     latest_thm_list := allthms;
     allthms,(newthms <> []));;

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
