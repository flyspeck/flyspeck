(*
Created Nov 26, 2009
THALES
*)

(*
Needs.
k vertices, k edges {i,i+1},
cyclic map on both
Each vertex is 2, 2h0 or free.
Each vertex is flat or not flat.

Each edge is in G or not,
Each edge is 2, 2h0, or free.

Without loss of generality, first vertex is not flat, followed by longest stretch of flats.



*)
open List;;

(* from lpproc.ml *)
let upto = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [] 0;;


(* minimal fan definition *)

type vertex_t = V2 | V2h0 | Vfree;;
type edge_t = E2 | E2h0 | Gset;;


type minimal_fan =  {
  vertex : vertex_t list;
  vertexflats : bool list;
  edge : edge_t list;
};;

let mk_minimal_fan vhts vflts e =
   {
   vertex = vhts;
   vertexflats = vflts;
   edge = e;
   };;


(* generating minimal_fan *)

let vertex_of_int i = if (i=0) then V2 else if (i=1) then V2h0 else Vfree;;
let edge_of_int i = if (i=0) then E2 else if (i=1) then E2h0 else Gset;;
let bool_of_int i = if (i=0) then false else true;;

let base modulus len k =
  let rec baselist modulus len k acc = 
    if len <= 0 then acc else
    if (k=0) then baselist modulus (len-1) 0 (0::acc)
    else 
      baselist modulus (len - 1) (k/modulus) ((k mod modulus) :: acc) in
  baselist modulus len k [];;

let rec pow base exp =
   if exp = 0 then 1 else base*(pow base (exp-1));;

let mk_x len (a,b,c) (r,s,t) =
  let (v,vf,e) = (base a len r, base b len s, base c len t) in
  mk_minimal_fan 
     (map vertex_of_int v)
     (map bool_of_int vf)
     (map edge_of_int e);;


let nary_list base k = map (fun t -> baselist base k t []) (upto (pow base k));;

let rec cross a = function 
   [] -> []
  | b::bs -> (map (fun t -> (t,b)) a) @ cross a bs;;

(* reading data from a record *)

let kv mf = length (mf.vertex);;
let sv mf = List.length (filter ((=) Gset) mf.edge);;
let rv mf = kv mf - sv mf;;

let posmod i m = 
  let j = i mod m in
  if (j<0) then j+ m else j;;
  
let part xs i = nth xs (posmod i (length xs));;

let g mf i = part mf.edge i = Gset;;
let nong mf i = not(g mf i);;
let flat mf i = part mf.vertexflats i;;
let nonflat mf i = not(flat mf i);;
let number mf = upto(length mf.edge);;
let gminimal mf i = not(part mf.edge i = E2h0);;
let vextremal mf i = not(part mf.vertex i = Vfree);;

(* irreducibility *)

(* extreme_edge is built into construction of edge types *)

let card mf = (sv mf <= 3) && (3 <= sv mf + rv mf) && (rv mf + 2 * sv mf <= 6);;

let extreme_edge mf = true;;

let flat_exists mf = 
  let has i = (kv mf <= 4) or
       flat mf i or flat mf (i+1) or flat mf (i+2) or flat mf (i+3) in
  for_all has (number mf);;


let no_triple_flat mf = 
   let triple_flat i = flat mf i && flat mf (i+1) && flat mf (i+2) in
   not (exists triple_flat (number mf));;

let balance mf = 
   let es = mf.edge in
   let has_balance i = (part es i = part es (i+1)) or not(part es i = Gset) or not (part es (i+1) = Gset) in
   for_all has_balance (number mf);;

let g_flat mf = 
   let gg = g mf in
  let nf = nonflat mf in
  let has_gflat i = nf i or nf (i+1) or not(gg (i-1) or gg i or gg(i+1) ) in
   for_all has_gflat (number mf);;

let flat_middle mf =
  let nf = nonflat mf in
  let has i = nf i or nf (i+1) or (part mf.edge i = E2 ) in
   for_all has (number mf);;

let minimal_vertex mf = 
  let has i = (part mf.vertex i = V2) or (gminimal mf i) or (gminimal mf (i+1)) in
  for_all has (number mf);;

let minimal_vertex_flat mf = 
  let has i = (nonflat mf i) or (part mf.vertex i = V2) or (gminimal mf i && gminimal mf (i+1)) in
  for_all has (number mf);;

let flat_extremal mf = 
  let has i = nonflat mf i or nonflat mf (i+1) or vextremal mf i or vextremal mf (i+1) in
  for_all has (number mf);;

let extremal_vertex mf = 
  let has i = flat mf i or flat mf (i+1) or flat mf (i+2) or vextremal mf (i+1) in
  for_all has (number mf);; 

let flat_extremal_vertex mf = 
   let has i = flat mf i or nonflat mf (i+1) or flat mf (i+2) or flat mf (i+3) or vextremal mf (i+1) or vextremal mf (i+2) in
  for_all has (number mf);;

let flat_extremal_vertex_sym mf = 
   let has i = flat mf i or flat mf (i+1) or nonflat mf (i+2) or flat mf (i+3) or vextremal mf (i+1) or vextremal mf (i+2) in
  for_all has (number mf);;

let flat_count mf = 
   length (filter not mf.vertexflats) > 2;;

let irreducible = 
  fold_right (fun r s m -> r m && s m) 
 [card;extreme_edge;flat_exists;no_triple_flat;balance;g_flat;
  flat_middle;minimal_vertex;minimal_vertex_flat;flat_extremal;
  extremal_vertex;flat_extremal_vertex;flat_extremal_vertex_sym;
  flat_count] 
(fun t->true);;


(* symmetry reductions, add to the list of solutions only if it is shift-distinct from other solutions *)

let shift_one (x::xs) = xs @ [x];;

let shift a = { vertex = shift_one a.vertex; vertexflats = shift_one a.vertexflats; edge = shift_one a.edge };;

let rec shiftk k a =  if (k<=0) then a else shift (shiftk (k-1) a);;

let add_if_new a aas = 
   if (exists (fun i -> mem (shiftk i a) aas) (upto (kv a))) then aas else a::aas;;
let add_if_i a aas = if (irreducible a ) then add_if_new a aas else aas;;

let f3 i j = mk_x 3 (3,1,3) (i,0,j);;
let rec mk3_all i j acc = 
   let acc' =  add_if_i (f3 i j) acc in
   if (j +1 < pow 3 3) then mk3_all i (j+1) acc'
     else if (i +1 < pow 3 3) then mk3_all (i+1) 0 acc' else acc';;
let a3 = mk3_all 0 0 [];;
length a3;;

let f4no_flat i j = mk_x 4 (3,1,3) (i,0,j);;
let rec mk4x i j acc = 
   let acc' =  add_if_i (f4no_flat i j) acc in
   if (j +1 < pow 3 4) then mk4x i (j+1) acc'
     else if (i +1 < pow 3 4) then mk4x (i+1) 0 acc' else acc';;
let a4x = mk4x 0 0 [];;
length a4x;;

(* BUG: This should give the same result, but doesn't *)
let f4no_flat i j = mk_x 4 (4,1,4) (i,0,j);;
let rec mk4x i j acc = 
   let acc' =  add_if_i (f4no_flat i j) acc in
   if (j +1 < pow 4 4) then mk4x i (j+1) acc'
     else if (i +1 < pow 4 4) then mk4x (i+1) 0 acc' else acc';;
let a4x = mk4x 0 0 [];;
length a4x;;


let f4one_flat i j = mk_x 4 (4,2,4) (i,1,j);;
let rec mk41 i j acc = 
   let acc' =  add_if_i (f4one_flat i j) acc in
   if (j +1 < pow 4 4) then mk41 i (j+1) acc'
     else if (i +1 < pow 4 4) then mk41 (i+1) 0 acc' else acc';;
let a41 = mk41 0 0 [];;
length a41;;

let f5no_g i j = mk_x 5 (3,2,1) (i,j,0);;
let rec mk5x i j acc = 
   let acc' =  add_if_i (f5no_g i j) acc in
   if (j +1 < pow 3 5) then mk5x i (j+1) acc'
     else if (i +1 < pow 2 5) then mk5x (i+1) 0 acc' else acc';;
let a5x = mk5x 0 0 [];;
length a5x;;

let f5g i j = mk_x 5 (3,2,2) (i,j,1);;
let rec mk5g i j acc = 
   let acc' =  add_if_i (f5g i j) acc in
   if (j +1 < pow 3 5) then mk5g i (j+1) acc'
     else if (i +1 < pow 2 5) then mk5g (i+1) 0 acc' else acc';;
let a5g = mk5g 0 0 [];;
length a5g;;

let f6 i j = mk_x 6 (3,2,1) (i,j,0);;
let rec mk6 i j acc = 
   let acc' =  add_if_i (f6 i j) acc in
   if (j +1 < pow 3 6) then mk6 i (j+1) acc'
     else if (i +1 < pow 2 6) then mk6 (i+1) 0 acc' else acc';;
let a6 = mk6 0 0 [];;
length a6;;

(* degrees of freedom *)

let freedom a = (kv a) - 3 + length (filter ((=) Vfree) a.vertex);;
map freedom a5x;;
