let pl =new_definition `pl(a:real^3,b:real)={x:real^3 | a$1*x$1+a$2*x$2+a$3*x$3+b= &0}`;;

let plane =new_definition `plane (P:real^3->bool)=(? (a:real^3) (b:real).P= pl (a,b))`;;

let b = new_definition`b (v:real^3, r:real)={x:real^3 | norm (x-v)= r}`;;

let ball = new_definition `ball (B:real^3->bool)=(?(v:real^3) r. B= b(v,r))`;;

let c_cone = new_definition `c_cone (v,w:real^3, r:real)={x:real^3 | (x=v) \/ ((x-v) dot w = norm (x-v)* norm w* r)\/ ((x-v) dot w = --norm (x-v)* norm w* r)}`;;

let circular_cone =new_definition `circular_cone (V:real^3-> bool)=(? (v,w:real^3)(r:real). V= c_cone (v,w,r))`;;

let NULLSET_RULES,NULLSET_INDUCT,NULLSET_CASES =
  new_inductive_definition
    `(!P. ((plane P)\/ (ball P) \/ (circular_cone P)) ==> NULLSET P) /\
     !(s:real^3->bool) t. (NULLSET s /\ NULLSET t) ==> NULLSET (s UNION t)`;;


let equiv = new_definition `equiv (s,t :real^3->bool)=(? (B:real^3-> bool). NULLSET B | ((s DIFF t) UNION (t DIFF s)) SUBSET B)`;;

