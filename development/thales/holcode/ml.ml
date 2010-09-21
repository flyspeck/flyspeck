let upto = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [] 0;;

upto 3;;
(* execution of fejes toth *)

#use "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/packing/OXLZLEZ.ml";;
#use "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/tame_archive/lpproc.ml";;

#directory "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;
#use  "glpk_link.ml";;
open Glpk_link;;

let rec fac n = if (n<=1) then 1 else n * fac (n-1);;

fac 5;;
fac 9;;
let fac9 = 3.6288 *. 10.0 ** 5.0;;
let fac333 = 6.0 ** 3.0;;
let rho = 2.0 +. 2.0 *. fac333;;
rho ** 6.0 *. fac333 ** 12.0 /. fac9 ** 3.0;;
rho *. fac9 /. (fac333 *. 3.0);;
fac333;;
560.0 ** 6.0;;
fac333 *. fac333/. fac9;;

let rec loop t = 
    let _ = sin 3.4 in
    loop t ;;

loop 3;;

raise (Failure "3");;
