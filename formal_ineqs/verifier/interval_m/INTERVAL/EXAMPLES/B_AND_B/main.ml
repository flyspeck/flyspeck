open Interval

(* Standard Griewank function without rotation matrix, very easy to maximize *)
let dim = 7
let highbound = 600.0
let lowbound  = -. 400.0
let precisionx = 0.01
let precisionfx = 0.0001

let start_inter = 
  Array.init dim (function i -> {low=lowbound;high=highbound})

let griewank_x v = 
  let s1 = ref 0.0 and s2 = ref 1.0 in
  for i= 0 to (Array.length v)-1 do
    s1:= !s1+. v.(i)*. v.(i);
    s2:= !s2*. (cos (v.(i)/. (sqrt (float (i+1)))))
  done;
  let sum = !s1/. 4000.0 -. !s2 +.1. in
  1./.(1.+. sum)
    
let griewank_X v = 
  let s1 = ref  zero_I and s2 = ref one_I in
  for i= 0 to (Array.length v)-1 do
    s1:= !s1 +$ (pow_I_i v.(i) 2);
    s2:= !s2 *$ (cos_I (v.(i) /$.(sqrt (float (i+1)))))
  done;
  let sum = ((!s1 /$. 4000.0)  -$ !s2) +$. 1. in
  1./.$ (sum +$. 1.)

let _ = 
  let (int,fint,p,pv)= 
    B_and_b.branch_and_bound griewank_x griewank_X start_inter precisionx precisionfx in
  print_X int;print_string " = ";
  print_I fint; print_newline ();
  Array.iter (function x -> Printf.printf "%f " x) p;
  Printf.printf " = %f\n" pv;
  flush stdout;;

  
