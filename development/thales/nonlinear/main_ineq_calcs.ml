#directory "/Users/thomashales/Desktop/googlecode/flyspeck/glpk";;
#use "sphere.ml";;


  open Sphere_math;;

  let arc = arclength;;

  let rec binary_rec f a b eps = 
    let fa = f a in 
      if abs_float (fa) < eps then a
      else 
	let c = (a +. b) /. 2. in
	let fc = f c in
	  (if (fa *. fc <= 0.0) then binary_rec f a c eps 
	   else binary_rec f c b eps);;

  let binary f a b eps = 
    let _ = (a < b) or failwith "a b inversion" in
    let _ = f a *. f b <= 0.0 or failwith "same sign" in
      binary_rec f a b eps;;

  let length_of_arc theta = 
      binary (fun x -> arc 2. 2. x -. theta) 2.0 4.0 (10.0** -8.0);;

  let tame_table_d r s = 
    if (r + 2 * s <= 3) then 0.0
    else
      let r' = float_of_int r in
      let s' = float_of_int s in
	0.103 *. (2.0 -. s') +. 0.2759 *. (r' +. 2.0 *. s' -. 4.0);;

tame_table_d 3 1;;
tame_table_d 2 2;;
(* "2065952723 A1" 
15.53 is the upper bound on the deforming edge.
Let's check that two adjacent standard edges fit within this bound.
Conclusion, whenever there is a pair of adjacent standard edges, they
are extremal 2 or 2.52; EXCEPT in something that starts out a hexagon
or protracted pent with two adjacent flats.
*)

  let check_206A1_constant = 
    let u = 2.0 *. arc 2. 2. 2.52 in
    let m =  length_of_arc u in
    let m2 = m*.m in
      (m2 < 15.53);;  (* 15.319 *)

  let check_206A1_protracted51 = 
    let u = arc 2. 2. 2.52 +. arc 2. 2. sqrt8 in
    let m = length_of_arc u in
    let m2 = m*.m in
      m2;;
      (m2 < 15.53);;  (* 15.319 *)

  let factoid1 = (* generic fans except for hexagons *)
    let u = arc 2. 2. cstab +. arc 2. 2. 2.52 in 
      u < pi;;  (* u = 3.0668... *)

  let two_flats_arc_min = 2.0 *. arc 2.52 2. 2. +. arc 2. 2. 2.;;



