(* ------------------------------------------------------------------ *)
(*   Generate Definition files from the Collection in Elementary Geometry           *)
(* ------------------------------------------------------------------ *)

open Template_def;;

let _ = set_root_dir "/Users/thomashales/Desktop/flyspeck_google/source/text_formalization";;

let cayleyRstr="new_definition `cayleyR x12 x13 x14 x15  x23 x24 x25  x34 x35 x45 = 
  -- (x14*x14*x23*x23) + &2 *x14*x15*x23*x23 - x15*x15*x23*x23 + &2 *x13*x14*x23*x24 - &2 *x13*x15*x23*x24 - &2 *x14*x15*x23*x24 + 
   &2 *x15*x15*x23*x24 - x13*x13*x24*x24 + &2 *x13*x15*x24*x24 - x15*x15*x24*x24 - &2 *x13*x14*x23*x25 + 
   &2 *x14*x14*x23*x25 + &2 *x13*x15*x23*x25 - &2 *x14*x15*x23*x25 + &2 *x13*x13*x24*x25 - &2 *x13*x14*x24*x25 - &2 *x13*x15*x24*x25 + 
   &2 *x14*x15*x24*x25 - x13*x13*x25*x25 + &2 *x13*x14*x25*x25 - x14*x14*x25*x25 + &2 *x12*x14*x23*x34 - &2 *x12*x15*x23*x34 - 
   &2 *x14*x15*x23*x34 + &2 *x15*x15*x23*x34 + &2 *x12*x13*x24*x34 - &2 *x12*x15*x24*x34 - &2 *x13*x15*x24*x34 + &2 *x15*x15*x24*x34 + 
   &4 *x15*x23*x24*x34 - &2 *x12*x13*x25*x34 - &2 *x12*x14*x25*x34 + &4 *x13*x14*x25*x34 + &4 *x12*x15*x25*x34 - &2 *x13*x15*x25*x34 - &2 *x14*x15*x25*x34 - 
   &2 *x14*x23*x25*x34 - &2 *x15*x23*x25*x34 - &2 *x13*x24*x25*x34 - &2 *x15*x24*x25*x34 + &2 *x13*x25*x25*x34 + &2 *x14*x25*x25*x34 - 
   x12*x12*x34*x34 + &2 *x12*x15*x34*x34 - x15*x15*x34*x34 + &2 *x12*x25*x34*x34 + &2 *x15*x25*x34*x34 - 
   x25*x25*x34*x34 - &2 *x12*x14*x23*x35 + &2 *x14*x14*x23*x35 + &2 *x12*x15*x23*x35 - &2 *x14*x15*x23*x35 - &2 *x12*x13*x24*x35 + 
   &4 *x12*x14*x24*x35 - &2 *x13*x14*x24*x35 - &2 *x12*x15*x24*x35 + &4 *x13*x15*x24*x35 - &2 *x14*x15*x24*x35 - &2 *x14*x23*x24*x35 - &2 *x15*x23*x24*x35 + 
   &2 *x13*x24*x24*x35 + &2 *x15*x24*x24*x35 + &2 *x12*x13*x25*x35 - &2 *x12*x14*x25*x35 - &2 *x13*x14*x25*x35 + &2 *x14*x14*x25*x35 + 
   &4 *x14*x23*x25*x35 - &2 *x13*x24*x25*x35 - &2 *x14*x24*x25*x35 + &2 *x12*x12*x34*x35 - &2 *x12*x14*x34*x35 - &2 *x12*x15*x34*x35 + 
   &2 *x14*x15*x34*x35 - &2 *x12*x24*x34*x35 - &2 *x15*x24*x34*x35 - &2 *x12*x25*x34*x35 - &2 *x14*x25*x34*x35 + &2 *x24*x25*x34*x35 - 
   x12*x12*x35*x35 + &2 *x12*x14*x35*x35 - x14*x14*x35*x35 + &2 *x12*x24*x35*x35 + &2 *x14*x24*x35*x35 - 
   x24*x24*x35*x35 + &4 *x12*x13*x23*x45 - &2 *x12*x14*x23*x45 - &2 *x13*x14*x23*x45 - &2 *x12*x15*x23*x45 - &2 *x13*x15*x23*x45 + 
   &4 *x14*x15*x23*x45 + &2 *x14*x23*x23*x45 + &2 *x15*x23*x23*x45 - &2 *x12*x13*x24*x45 + &2 *x13*x13*x24*x45 + &2 *x12*x15*x24*x45 - 
   &2 *x13*x15*x24*x45 - &2 *x13*x23*x24*x45 - &2 *x15*x23*x24*x45 - &2 *x12*x13*x25*x45 + &2 *x13*x13*x25*x45 + &2 *x12*x14*x25*x45 - 
   &2 *x13*x14*x25*x45 - &2 *x13*x23*x25*x45 - &2 *x14*x23*x25*x45 + &4 *x13*x24*x25*x45 + &2 *x12*x12*x34*x45 - &2 *x12*x13*x34*x45 - 
   &2 *x12*x15*x34*x45 + &2 *x13*x15*x34*x45 - &2 *x12*x23*x34*x45 - &2 *x15*x23*x34*x45 - &2 *x12*x25*x34*x45 - &2 *x13*x25*x34*x45 + &2 *x23*x25*x34*x45 + 
   &2 *x12*x12*x35*x45 - &2 *x12*x13*x35*x45 - &2 *x12*x14*x35*x45 + &2 *x13*x14*x35*x45 - &2 *x12*x23*x35*x45 - &2 *x14*x23*x35*x45 - 
   &2 *x12*x24*x35*x45 - &2 *x13*x24*x35*x45 + &2 *x23*x24*x35*x45 + &4 *x12*x34*x35*x45 - x12*x12*x45*x45 + &2 *x12*x13*x45*x45 - 
   x13*x13*x45*x45 + &2 *x12*x23*x45*x45 + &2 *x13*x23*x45*x45 - x23*x23*x45*x45` ";;

let mkd def data comments needlist = 
  let ud = 
    {definition=def;
     chapter="LEG";
     author="Thomas C. Hales";
     date="2010-02-07";
     data=data;
     comments=comments;
     needlist=needlist;
    } in
     output_template ud;;

mkd "cayleyR" cayleyRstr ["This is the 5 vertex Cayley-Menger determinant";"EDSFZOT";"NUHSVLM";
       "See http://www.math.pitt.edu/~thales/papers/Lemmas_Elementary_Geometry.pdf";
   "Properties of cayleyR have been formalized by Nguyen Quang Truong"]
     [];;

mkd "quadratic_root_plus"
   "   new_definition `quadratic_root_plus (a, b, c) = ( -- b + sqrt(b pow 2 - &4 * a * c))/ (&2 * a)`;;"
   ["Lemmas Elementary Geometry  (def:calE), RPFVZDI"] [];;

mkd "muR"
  "new_definition `muR y1 y2 y3 y4 y5 y6 y7 y8 y9 x = cayleyR (y6*y6) (y5*y5) (y1*y1) (y7*y7) (y4*y4) (y2*y2) (y8*y8)  (y3*y3) (y9*y9) x`;;"
  [
   "This is the cayleyR function, expressed in terms of the unsquared variables";
   "indexing: five vertices v1..v5, yij runs from vi to vj,";
   "two tetrahedra, shared face v1,v2,v3.";
   "v4 v5 in opposite half-planes.";
   "enclosed = y45 = sqrt(x45) is the distance from v4 to v5.";
   "[y1,y2,y3,y4,y5,y6,y7,y8,y9]=[y14,y24,y34,y23,y13,y12,y15,y25,y35].";
   "y1..y6 is the usual indexing of a simplex.";
   "y4..y9 is mod 6 congruent to the usual indexing."] ["leg/cayleyR_def.hl"];;

mkd "abc_of_quadratic"
 "new_definition `abc_of_quadratic f = 
  let c = f (&0) in
  let  p = f (&1) in
  let n = f (-- &1) in
  ((p + n)/(&2) - c, (p -n)/(&2), c)` ;;" ["f = \\x. a x^2 + b x + c, extract a b c"] [];;

mkd "enclosed"
 "new_definition `enclosed y1 y2 y3 y4 y5 y6 y7 y8 y9 = sqrt 
  (quadratic_root_plus (abc_of_quadratic (muR y1 y2 y3 y4 y5 y6 y7 y8 y9)))`;;"
  ["The function of 9 variables defined on page 37 of the Kepler Conjecture, DCG vol 36(1), July 2006";
   "It is generally typeset as a calligraphic E"] ["leg/abc_of_quadratic_def.hl";"leg/quadratic_root_plus.hl"];;

