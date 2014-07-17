(* Ill conditioned function *)

open Interval;;

(* Parenthesis are MANDATORY for interval computation (see documentation) *)
let f_I x y = 
  ((y **$. 6.0) *$. 333.75)  
    +$ (x **$. 2.0 *$ (((x **$. 2.0) *$ (y **$. 2.0) *$. 11.0) -$ (y **$. 6.0) 
			 -$  ((y **$. 4.0) *$. 121.0) -$. 2.0)) +$ ((y **$. 8.0) *$. 5.5) 
    +$ (x /$ (y *$. 2.0));;

(* We could write the regular function without so many parenthesis *)
let f x y = 
  ((y ** 6.0) *. 333.75)  
    +. (x ** 2.0 *. (((x ** 2.0) *. (y ** 2.0) *. 11.0) -. (y ** 6.0) 
		       -. ((y ** 4.0) *. 121.0) -. 2.0)) +. ((y ** 8.0) *. 5.5) 
    +. (x /. (y *. 2.0));;

let g u v = 
  Printf.printf "Computing f(%f,%f)\n" u v;
  let a = {low=u;high=u} and b = {low=v;high=v} in
  let x = (f u v) in
  let y = (f_I a b) in
  Printf.printf "f(x,y) = %e\nf(I) = " x;
  printf_I "%e" y;
  print_newline ();
  let err=100.0*.(y.high -. y.low)/. (abs_float x) in
  Printf.printf "error (in percent) = %e\n" err;
  print_newline();;

let _ = 
  g 77617.0 33095.999;
  g 77617.0 33096.001;
  g 77617.0 33096.0;;
