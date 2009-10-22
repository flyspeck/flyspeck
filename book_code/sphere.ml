(* extracted from sphere.hl *)

let sqrt8 = sqrt(8.0);;
let sqrt2 = sqrt(2.0);;
let pi = 4.0*.atan(1.0);;

let delta_x x1 x2 x3 x4 x5 x6 = 
        x1*.x4*.(-.  x1 +.  x2 +.  x3 -. x4 +.  x5 +.  x6) +. 
        x2*.x5*.(x1 -.  x2 +.  x3 +.  x4 -. x5 +.  x6) +. 
        x3*.x6*.(x1 +.  x2 -.  x3 +.  x4 +.  x5 -.  x6)
        -. x2*.x3*.x4 -.  x1*.x3*.x5 -.  x1*.x2*.x6 -. x4*.x5*.x6;;

let delta_y y1 y2 y3 y4 y5 y6 =
    delta_x (y1*.y1) (y2*.y2) (y3*.y3) (y4*.y4) (y5*.y5) (y6*.y6);;

let delta_x4 x1 x2 x3 x4 x5 x6
        =  -.   x2*. x3 -.   x1*. x4 +.  x2*. x5
        +.  x3*. x6 -.   x5*. x6 +.  x1*. (-.   x1 +.   x2 +.   x3 -.   x4 +.   x5 +.   x6);;

let delta_x6 x1 x2 x3 x4 x5 x6
	= -.   x1 *. x2 -.  x3*.x6 +.  x1 *. x4
	+.  x2*. x5 -.  x4*. x5 +.  x3*.(-.   x3 +.  x1 +.  x2 -.  x6 +.  x4 +.  x5);;

let ups_x x1 x2 x6 = 
    -.  x1*.x1 -.  x2*.x2 -.  x6*.x6 
    +.  2.0 *.x1*.x6 +.  2.0 *.x1*.x2 +.  2.0 *.x2*.x6;;

let eta_x x1 x2 x3 =
        (sqrt ((x1*.x2*.x3)/.(ups_x x1 x2 x3)))
        ;;

let eta_y y1 y2 y3 =
                let x1 = y1*.y1 in
                let x2 = y2*.y2 in
                let x3 = y3*.y3 in
                eta_x x1 x2 x3;;

let atn2 (x,y) = atan(y/. x);;

let dih_x x1 x2 x3 x4 x5 x6 =
       let d_x4 = delta_x4 x1 x2 x3 x4 x5 x6 in
       let d = delta_x x1 x2 x3 x4 x5 x6 in
       pi/.  (2.0) +.   atn2( (sqrt ((4.0) *.  x1 *.  d)),-.  d_x4);;

let dih_y y1 y2 y3 y4 y5 y6 =
       let (x1,x2,x3,x4,x5,x6)= (y1*. y1,y2*. y2,y3*. y3,y4*. y4,y5*. y5,y6*. y6) in
       dih_x x1 x2 x3 x4 x5 x6;;

let sol_x  x1 x2 x3 x4 x5 x6 =
        dih_x x1 x2 x3 x4 x5 x6 +. 
        dih_x x2 x3 x1 x5 x6 x4 +.   dih_x x3 x1 x2 x6 x4 x5 -.  pi;;

let sol_y  y1 y2 y3 y4 y5 y6 =
        dih_y y1 y2 y3 y4 y5 y6 +. 
        dih_y y2 y3 y1 y5 y6 y4 +.   dih_y y3 y1 y2 y6 y4 y5 -.  pi;;

let interp x1 y1 x2 y2 x = y1 +.  (x -. x1) *.  (y2-. y1)/. (x2-.x1);;

(*  c1 in lp2009.c *)
let const1 = sol_y (2.0) (2.0) (2.0) (2.0) (2.0) (2.0) /.  pi;;

let ly y = interp (2.0) (1.0) (2.52) (0.0) y;;

let rho y = 1.0 +.  const1 -. const1*.  ly y;;

let rhazim y1 y2 y3 y4 y5 y6 = rho y1 *.  dih_y y1 y2 y3 y4 y5 y6;;

let lnazim y1 y2 y3 y4 y5 y6 = ly y1 *.  dih_y y1 y2 y3 y4 y5 y6;;

let taum y1 y2 y3 y4 y5 y6 = sol_y y1 y2 y3 y4 y5 y6 *.  (1.0 +.  const1) -. const1 *.  (lnazim y1 y2 y3 y4 y5 y6 +.  lnazim y2 y3 y1 y5 y6 y4 +.  lnazim y3 y1 y2 y6 y4 y5);;

