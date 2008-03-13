


(* Program to compute the constants in Leech's paper on 13 spheres *)
(* See essay on "THIRTEEN SPHERES"  presentation fo the mathematics involved. *)

(* assertions and general utilities *)
let assertions = ref true;;
let also_assert x = assertions := x && !assertions ; x;;

let min_list it = List.fold_right min it (List.nth it 0);;
let max_list it = List.fold_right max it (List.nth it 0);;

(* constants  *)
let pi = 4.0 *. atan(1.0);;
let b = pi /. 3.0;;
let c = 1.42;;  (* Approximates Leech's constant: acos (1.0/. 7.0). *)
let d = 1.7;;   (* New constant used to estimate areas *)

(* spherical law of cosines: gamma in terms of c b a *)
let gammaCBA c b a = 
    acos ((cos c -. cos a *. cos b)/. (sin a *. sin b));;

(* c in terms of gamma a b *)
let cgammaAB gamma a b =
    acos ( cos(gamma) *. sin(a) *. sin(b) +. cos(a) *. cos(b));;

(* Girard's formula *)
let girard a b c = 
    a +. b +. c -. pi;;

(* Area of a spherical triangle in terms of sides *)
let areaSSS a b c = 
    girard (gammaCBA a b c) (gammaCBA b c a) (gammaCBA c a b);;

(* Area of a spherical triangle given two sides a b and circumradius r *)
(* There are generally two triangles when two sides and the circumradius are given.
   This function returns the minimum of the two areas.
   The triangle is discarded (assigning the default area) if the third
   side has length less than cmin. *)

let areaSSC a b r cmin default = 
    let alpha = gammaCBA a r r in
    let beta  = gammaCBA b r r in
    let s = alpha +. beta in
    let	gamma = if (s < pi) then s else 2.0 *. pi -. s in
    let	c = cgammaAB gamma r r in 
    let area = if (cmin <= c) then (areaSSS a b c) else default in
    let gamma2 = abs_float (alpha -. beta) in
    let c2 = cgammaAB gamma2 r r in
    let area2 = if (cmin <=c2) then (areaSSS a b c2) else default in
	min area area2;;

    
(* Area of an equilateral triangle of minimum edge length *)
let delta = areaSSS b b b;;
also_assert(delta -. (3.0 *. acos(1.0/. 3.0) -. pi) < 1.0e-6);;

(* Excess area on a sphere over 22 minimal triangles *)
let eps_computed = 4.0 *. pi -. 22.0 *. delta;;
let eps = 0.4381;; (* round up to get strict inequalities *)
also_assert (eps > eps_computed);;

(* Compute minimum area of a triangle under edge length constraints. *)
let triangle_min a0 a1 b0 b1 c0 c1 = 
    min_list [
	     areaSSS a0 b0 c0;
	     areaSSS a0 b0 c1;
	     areaSSS a0 b1 c0;
	     areaSSS a0 b1 c1;
	     areaSSS a1 b0 c0;
	     areaSSS a1 b0 c1;
	     areaSSS a1 b1 c0;
	     areaSSS a1 b1 c1;
    ];;

(* Calculate the constants in the table of areas in "THIRTEEN SPHERES" *)

let default = delta +. 2.0*.eps;; (* anything bigger than delta + eps *)
let row1 = min (areaSSC c c b  c default ) (areaSSS c c c);;
also_assert ((row1 -. (delta +. eps)) > 0.0 );; 

let row2 = min_list [
	 areaSSS b c d;
	 areaSSS c c d;
	 areaSSC b c b d default;
	 areaSSC c c b d default;
	 areaSSC b d b c default;
	 areaSSC c d b b default;
	 ];;
also_assert ((row2 -. (delta +. eps)) > 0.0);;

let row3 = triangle_min b c c d c d;;
also_assert ((row3 -. (delta +. eps/. 2.0)) > 0.0);;

let row4 = triangle_min b c b c c d;;
also_assert((row4 -. (delta +. eps/. 4.0)) > 0.0);;

let row5 = min_list [
          areaSSC b b b d default;
          areaSSC c b b d default;
          areaSSC c c b d default;
	  areaSSS b b d;
	  areaSSS b c d;
	  areaSSS c c d;
          ];;
also_assert(row5 >= delta);;

let row6 = triangle_min b c b c b c;;
also_assert(abs_float(row6 -. delta) < 1.0e-6);;

(* compute max valence *)
let valence  = let min_angle = min_list [
    (gammaCBA b b b);
    gammaCBA b b c;
     (gammaCBA b c c)] in
   2.0 *. pi /. min_angle;;  (* 5.9753... *)
also_assert (valence < 6.0);;

(* check the angles > pi/2 on a quad with diags > 1.7 *)
let angle_bigquad = min_list [
	(gammaCBA d b b);
	(gammaCBA d c b);
	 (gammaCBA d c c)] ;;
also_assert (angle_bigquad > pi/. 2.0);;


(* eliminate degree 4 vertices that are not on the oblong quad *)

(* Some code to find max angle. *)
(* Run through all endpoints and all right angled triangles. *)

let maxAngle a0 a1 b0 b1 c = 
	 let angle00 = gammaCBA c a0 b0 in
	 let angle01 = gammaCBA c a0 b1 in
	 let angle10 = gammaCBA c a1 b0 in
	 let angle11 = gammaCBA c a1 b1 in
	 let angleRR = if (a0 <= pi/. 2.0) && (pi/. 2.0 <= a1) &&
	     (b0 <= pi/. 2.0) && (pi/. 2.0 <= b1) then c else angle00 in
	 let u x = acos ( cos x *. cos c) in
	 let angleS x m m' = 
	     let u = u x in
	     if (m <= u) && (u <= m') then gammaCBA c x u else angle00 in
	 max_list [angle00;angle01;angle10;angle11;angleRR;
		  (angleS a0 b0 b1);(angleS a1 b0 b1);
		  (angleS b0 a0 a1);(angleS b1 a0 a1)];;

let r x = maxAngle b c b c x -. pi/. 2.0;;
r 1.15;;  (* -0.21292 *)
r 1.251;; (* -0.0859 *)
r 1.42;;  (* 0.13342 *)
gammaCBA 1.15 b b  -. pi/.2.0;;
gammaCBA 1.251 b b -. pi/.2.0;;
gammaCBA 1.42 b b -. pi/.2.0;;  (* same answers! *)

(* final assert to see that all the asserted conditions are met *)
let tell_me_it_works =  !assertions;;

	     
