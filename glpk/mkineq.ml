(* create new inequalities for lp, cfsqp, formal spec *)

open Str;;
open List;;
open Num;;
let sprintf = Printf.sprintf;;

(* from lpproc.ml *)

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_lines  = unsplit "\n" (fun x-> x);;

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;


(* end from lpproc.ml *)

type sgn = GT | GE;;

type constrain = NONE | SMALLTRI | BIGTRI ;;

type vertex = LOW | MEDIUM | HIGH | EXTRA ;;

type edge = SMALL | BIG;;

type decimal = Dec of string | Sqrt2 | Sqrt8;; 

let has_point s = try 
  let _ = String.index s '.' in true
  with failure -> false;;

let add_point s = if has_point s then s else s^".0";;

let dec_of_string s = 
  if s="s2" then Sqrt2
  else if s="s8" then Sqrt8
  else Dec s;;

let d = dec_of_string;;

let ds:string -> decimal list = fun s ->
  let ss = split_sp s in
    map dec_of_string ss;;

let float_of_dec:decimal -> float = function
  | Sqrt2 -> sqrt(2.0) 
  | Sqrt8 -> sqrt(8.0)
  | Dec x -> float_of_string x;;

let holtext_of_dec:decimal -> string = function
  | Sqrt2 -> "s2"
  | Sqrt8 -> "s8"
  | Dec x ->  let y = add_point x in
      if (y.[0]= '-') then " -- #"^(String.sub y 1 (String.length y - 1)) 
      else "#"^y;;


holtext_of_dec (Dec "2.0");;

let holtext_of_declist:decimal list -> string = fun xs ->
  "["^(unsplit ";" holtext_of_dec xs)^"]";;

let holtext_of_sgn:sgn -> string = function
  | GT -> "( > )"
  | GE -> "( >= )";;

let holtext_of_constrain:constrain -> string = function
  | NONE -> "Cnone"
  | BIGTRI -> "Cbigtri"
  | SMALLTRI -> "Csmalltri";;

let split_sp=  Str.split (regexp " +");;



(*
represents on rectangle xmin[6], xmax[6]:

azim[i]*azim i y + rhzim[i]*rhzim i y + tau0 * taumar y + sol0 * sol y 
sgn
c0 + c dot (y-p).

*)

type ineq = {
  mutable id : string;
  mutable constrain: constrain;
  mutable sgn : sgn;
  mutable xmin : decimal list;
  mutable xmax : decimal list;
  mutable c0 : decimal;
  mutable c : decimal list;
  mutable p : decimal list;
  mutable azim : decimal list;
  mutable rhzim : decimal list;
  mutable tau0 : decimal;
  mutable sol0 : decimal;
};;

let hh =  {
  id = "21444";
  constrain = NONE;
  sgn = GT;
  xmin = ds "2 2 2 2 2 2";
  xmax = ds "2.52 2.52 2.52 2.52 2.52 2.52";
  c0 = d "2.34";
  c = ds "2.0 2.1 2.2 2.3 2.4 2.5";
  p = ds "3.0 3.1 3.2 3.3 3.4 3.5";
  azim = ds "1 1 1";
  rhzim = ds "-1.0 -2.0 -3.0";
  tau0 = d "1.0";
  sol0 = d "-4.0";
};;


let holtext_of_ineq:ineq->string = fun h ->
   let p = sprintf in
     join_lines [
       p"let hol_ineq%s = `hol_ineq (\"%s\", " h.id h.id;
       p"  %s," (holtext_of_constrain h.constrain);
       p"  %s," (holtext_of_sgn h.sgn);
       p"  %s," (holtext_of_declist h.xmin); 
       p"  %s," (holtext_of_declist h.xmax);
       p"  %s," (holtext_of_dec h.c0);
       p"  %s," (holtext_of_declist h.c);
       p"  %s," (holtext_of_declist h.p);
       p"  %s," (holtext_of_declist h.azim);
       p"  %s," (holtext_of_declist h.rhzim);
       p"  %s," (holtext_of_dec h.tau0);
       p"  %s)` " (holtext_of_dec h.sol0);
     ];;
holtext_of_ineq hh;;
(* ampl text generation of triangle ineqs
   ocaml numbering 012345
   ampl numbering 123456 *)


let aug i = i+1;;
let nz s = (float_of_dec s <> 0.0);;
let hasnz s = exists nz s;;
let unempty   = filter (fun t -> t <> "");;

let ampl_of_dec:decimal -> string = function
  | Sqrt2 -> "+1.4142135623730951"
  | Sqrt8 -> "+2.8284271247461903"
  | Dec x ->  
      if (x.[0]= '-') then x else "+"^x;;

let comp:decimal->decimal->int = 
  fun a b ->
    if (a=b) then 0 else compare (float_of_dec a) (float_of_dec b);;

let less_equal bs cs = 
  []= filter (fun t -> comp (fst t) (snd t) >0 ) (zip bs cs);;

let domain_covers (lo,high) h = 
  less_equal h.xmin lo && less_equal high h.xmax;;

let domain_covers_itriangle = 
  domain_covers (ds "2 2 2 2 2 2",ds "2.52 2.52 2.52 2.52 2.52 2.52");;

let domain_covers_apiece = 
  domain_covers (ds "2 2 2 2 2.52 2.52",ds "2.52 2.52 2.52 2.52 s8 s8");;

let domain_covers_flat =
  domain_covers (ds "2 2 2 2.52 2 2",ds "2.52 2.52 2.52 s8 2.52 2.52");;

let domain_covers_superflat =
  domain_covers (ds "2 2 2 s8 2 2",ds "2.52 2.52 2.52 3.0 2.52 2.52");;

let domain_covers_bigtri h = 
  domain_covers_itriangle h && (h.constrain = BIGTRI);;

let domain_covers_smalltri h = 
  domain_covers_itriangle h && (h.constrain = SMALLTRI);;

let vertex_range = function
  | LOW -> ds "2 2.18"
  | MEDIUM -> ds "2.18 2.36"
  | HIGH -> ds "2.18 2.52"
  | EXTRA -> ds "2.36 2.52";;

let domain_covers_f f vertex h i = 
  let ymin = nth h.xmin i in
  let ymax = nth h.xmax i in
  let [mm;mx] = f vertex in
    less_equal [ymin] [mm] && less_equal [mx] [ymax];;

let domain_covers_vertex = domain_covers_f vertex_range;;

let edge_range = function
  | SMALL -> ds "2 2.25"
  | BIG -> ds "2.25 2.52";;

let domain_covers_edge = domain_covers_f edge_range;;

let string_of_domain h = "";;

let ampltext_of_ineq:ineq->string = fun h ->
  let p = sprintf in 
  let a = ampl_of_dec in 
  let mkone f s = if nz f then p"  %s * %s " (a f) s else "" in
  let mk_madd j = p"  %s * (y%d[i2,j] - (%s))" 
    (a (nth h.c j)) (j+1) (a (nth h.p j)) in  
    join_lines (unempty[
      "# ";
      p"ineq%s 'ID[%s]' {(i1,i2,i3,j) in EDART : " h.id h.id;
      string_of_domain h;
      "}:";
      mkone h.tau0 "tau[j]";
      mkone h.sol0 "sol[j]";
      mkone (nth h.azim 0) "azim[i1,j]";
      mkone (nth h.azim 1) "azim[i2,j]";
      mkone (nth h.azim 2) "azim[i3,j]";
      mkone (nth h.rhzim 0) "rhzim[i1,j]";
      mkone (nth h.rhzim 1) "rhzim[i2,j]";
      mkone (nth h.rhzim 2) "rhzim[i3,j]";
      " >= ";
      p"  %s" (a h.c0);
      mk_madd 0;mk_madd 1;mk_madd 2;mk_madd 3;mk_madd 4;mk_madd 5
    ]);;
1;;
ampltext_of_ineq hh;;
