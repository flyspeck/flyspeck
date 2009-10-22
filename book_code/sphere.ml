(* extracted from sphere.hl *)

let sqrt8 = sqrt(8.0);;
let sqrt2 = sqrt(2.0);;

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

