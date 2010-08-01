(* code automatically generated from formal specification *)

module Sphere_math = struct 

let sqrt = Pervasives.sqrt;;
let pi = 4.0 *. atan(1.0);;
let  sqrt2   =  sqrt 2. ;;


let  sqrt8   =  sqrt 8. ;;


let  delta_x x1 x2 x3 x4 x5 x6  = ((x1 *. (x4 *. ((-. x1) +. (x2 +. ((x3 -.  x4) +. (x5 +. x6)))))) +. ((x2 *. (x5 *. ((x1 -.  x2) +. (x3 +. ((x4 -.  x5) +. x6))))) +. (((((x3 *. (x6 *. (x1 +. ((x2 -.  x3) +. (x4 +. (x5 -.  x6)))))) -.  (x2 *. (x3 *. x4))) -.  (x1 *. (x3 *. x5))) -.  (x1 *. (x2 *. x6))) -.  (x4 *. (x5 *. x6)))));;


let  delta_y y1 y2 y3 y4 y5 y6  =  delta_x (y1 *. y1) (y2 *. y2) (y3 *. y3) (y4 *. y4) (y5 *. y5) (y6 *. y6) ;;


let  delta_x4 x1 x2 x3 x4 x5 x6  = ((((-. x2) *. x3) -.  (x1 *. x4)) +. ((x2 *. x5) +. (((x3 *. x6) -.  (x5 *. x6)) +. (x1 *. ((-. x1) +. (x2 +. ((x3 -.  x4) +. (x5 +. x6))))))));;


let  delta_x6 x1 x2 x3 x4 x5 x6  = ((((-. x1) *. x2) -.  (x3 *. x6)) +. ((x1 *. x4) +. (((x2 *. x5) -.  (x4 *. x5)) +. (x3 *. ((-. x3) +. (x1 +. ((x2 -.  x6) +. (x4 +. x5))))))));;


let  ups_x x1 x2 x6  = (((((-. x1) *. x1) -.  (x2 *. x2)) -.  (x6 *. x6)) +. ((2. *. (x1 *. x6)) +. ((2. *. (x1 *. x2)) +. (2. *. (x2 *. x6)))));;


let  eta_x x1 x2 x3  =  sqrt ((x1 *. (x2 *. x3)) /.  ups_x x1 x2 x3 ) ;;


let  eta_y y1 y2 y3  =  eta_x (y1 *. y1) (y2 *. y2) (y3 *. y3) ;;


let  dih_x x1 x2 x3 x4 x5 x6  = (( pi   /. 2.) +. atan2 ((-.  delta_x4 x1 x2 x3 x4 x5 x6 )) ( sqrt (4. *. (x1 *.  delta_x x1 x2 x3 x4 x5 x6 )) )  );;


let  dih_y y1 y2 y3 y4 y5 y6  =  dih_x (y1 *. y1) (y2 *. y2) (y3 *. y3) (y4 *. y4) (y5 *. y5) (y6 *. y6) ;;


let  dih2_y y1 y2 y3 y4 y5 y6  =  dih_y y2 y1 y3 y5 y4 y6 ;;


let  sol_x x1 x2 x3 x4 x5 x6  = ( dih_x x1 x2 x3 x4 x5 x6  +. ( dih_x x2 x3 x1 x5 x6 x4  +. ( dih_x x3 x1 x2 x6 x4 x5  -.   pi  )));;


let  sol_y y1 y2 y3 y4 y5 y6  = ( dih_y y1 y2 y3 y4 y5 y6  +. ( dih_y y2 y3 y1 y5 y6 y4  +. ( dih_y y3 y1 y2 y6 y4 y5  -.   pi  )));;


let  interp x1 y1 x2 y2 x  = (y1 +. ((x -.  x1) *. ((y2 -.  y1) /. (x2 -.  x1))));;


let  ly y  =  interp 2. 1. 2.52 0. y ;;


let  const1   = ( sol_y 2. 2. 2. 2. 2. 2.  /.  pi  );;


let  rho y  = (1. +. ( const1   -.  ( const1   *.  ly y )));;


let  rhazim y1 y2 y3 y4 y5 y6  = ( rho y1  *.  dih_y y1 y2 y3 y4 y5 y6 );;


let  lnazim y1 y2 y3 y4 y5 y6  = ( ly y1  *.  dih_y y1 y2 y3 y4 y5 y6 );;


let  taum y1 y2 y3 y4 y5 y6  = (( sol_y y1 y2 y3 y4 y5 y6  *. (1. +.  const1  )) -.  ( const1   *. ( lnazim y1 y2 y3 y4 y5 y6  +. ( lnazim y2 y3 y1 y5 y6 y4  +.  lnazim y3 y1 y2 y6 y4 y5 ))));;

end;;
