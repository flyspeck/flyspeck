(*Nguyen Tat Thang*)


(*Definition of null set*)

needs "Multivariate/vector.ml";;
needs "definitions_kepler.ml";;
needs "Multivariate/topology.ml";;


let sphere= new_definition`sphere x=(?(v:real^3)(r:real). (r> &0)/\ (x={w:real^3 | norm (w-v)= r}))`;;

let c_cone = new_definition `c_cone (v,w:real^3, r:real)={x:real^3 | (x=v) \/ ((x-v) dot w 
= norm (x-v)* norm w* r)\/ ((x-v) dot w = --norm (x-v)* norm w* r)}`;;

let circular_cone =new_definition `circular_cone (V:real^3-> bool)=
(? (v,w:real^3)(r:real). V= c_cone (v,w,r))`;;

let NULLSET_RULES,NULLSET_INDUCT,NULLSET_CASES =
  new_inductive_definition
    `(!P. ((plane P)\/ (sphere P) \/ (circular_cone P)) ==> NULLSET P) /\
     !(s:real^3->bool) t. (NULLSET s /\ NULLSET t) ==> NULLSET (s UNION t)`;;


let equiv = new_definition `equiv (s,t :real^3->bool)=(? (B:real^3-> bool). NULLSET B | 
((s DIFF t) UNION (t DIFF s)) SUBSET B)`;;


(*Radial*)

let radial = new_definition `radial r x C <=> (C SUBSET ball (x,r)) /\ (?u. (x+u) IN C ==> (!t.(t> &0) /\ (t< r/ norm(u))==>(x+ t % u) IN C))`;;
let eventually_radial = new_definition `eventually_radial x C <=> (?r. (r> &0) /\ radial r x (C INTER ball (x,r)))`;;



(*4.2.11 combining solid angle and volume*)


let phi=new_definition `phi(h:real,t:real,l:real^2)= l$1*t*h*(t+h)/ &6 + l$2`;;

let A=new_definition `A(h:real,t:real,l:real^2)=(&1-h/t)*(phi (h,t,l)-phi (t,t,l))`;;



