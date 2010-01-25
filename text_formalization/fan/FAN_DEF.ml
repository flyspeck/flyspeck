
(* definition of fan as ordered pairs *)
(* This is the correct definition to use!! *)

let CASE_FAN_FINITE = new_definition `CASE_FAN_FINITE (V,E):bool  <=> FINITE V /\ ~(V SUBSET {})`;;

let CASE_FAN_ORIGIN = new_definition `CASE_FAN_ORIGIN (V,E) <=> ~((vec 0) IN (V:real^3 -> bool))`;;

let CASE_FAN_INDEPENDENCE = 
  new_definition `CASE_FAN_INDEPENDENCE (V,E) <=> 
  (!e.  e IN E ==> ~collinear ({vec 0} UNION e))`;;
 
let CASE_FAN_INTERSECTION =  
  new_definition`CASE_FAN_INTERSECTION(V,E):bool<=> 
  (!e1 e2. (e1 IN E UNION {{v}| v IN V}) /\ (e2 IN E UNION {{v}| v IN V})
  ==> ((aff_ge {vec 0 } e1) INTER (aff_ge {vec 0} e2) = aff_ge {vec 0} (e1 INTER e2)))`;;


let FANO=new_definition`FANO(V,E) <=> 
  ((UNIONS E) SUBSET V) /\ graph(E) /\ CASE_FAN_FINITE(V,E) /\ CASE_FAN_ORIGIN(V,E)/\
  CASE_FAN_INDEPENDENCE(V,E)/\ CASE_FAN_INTERSECTION(V,E)`;;

let FANO_OF_FAN = prove( `!V E. (FAN(vec 0 , V , E) <=> FANO(V,E))`, 
  REWRITE_TAC[FAN;FANO;CASE_FAN_FINITE;CASE_FAN_ORIGIN;CASE_FAN_INDEPENDENCE;CASE_FAN_INTERSECTION;fan1;fan2;fan6;fan7]);;
