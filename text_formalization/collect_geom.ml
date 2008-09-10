(* Formal Spec of Blueprint Chapter  on Collection of Problems in Geometry *)

needs "Examples/transc.ml";;
needs "definitions_kepler.ml";;

prioritize_real();;

(* Definition of Cayley – Menger square cm3 *)
let cm3_ups_x = new_definition `!(v1:real^3) (v2:real^3) (v3:real^3).
   cm3_ups_x v1 v2 v3 = 
  (((v2 - v1)$2 * (v3 - v1)$3 ) - ((v2 - v1)$3 * (v3 - v1)$2)) pow 2 +
  (((v2 - v1)$3 * (v3 - v1)$1 ) - ((v2 - v1)$1 * (v3 - v1)$3)) pow 2 +
  (((v2 - v1)$1 * (v3 - v1)$2 ) - ((v2 - v1)$2 * (v3 - v1)$1)) pow 2 `;;


