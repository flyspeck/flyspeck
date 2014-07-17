open Interval;;

let _ = 
  let a = {low=3.0;high=3.0} in
  let b = 1. /.$ a in
  printf_I "%f" a;
  print_newline();
  printf_I "%f" b;
  print_newline ();
  Printf.printf "%e\n" (b.high -. b.low);;

