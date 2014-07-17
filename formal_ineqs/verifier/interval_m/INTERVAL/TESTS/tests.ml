(*
    Copyright 2011 Jean-Marc Alliot / Jean-Baptiste Gotteland

    This file is part of the ocaml interval library.

    The ocaml interval library is free software: 
    you can redistribute it and/or modify it under the terms of 
    the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    The ocaml interval library is distributed in the hope that it will be 
    useful,but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public 
    License along with the ocaml interval library.  
    If not, see <http://www.gnu.org/licenses/>.
*)

open Fpu
open Interval

type test_mode = Exact | In | Mod2pi

type test_infos = {
    mode: test_mode;
    res_I: interval;
    msg: string;
    mutable res_low: float;
    mutable res_high: float;
    mutable args_low: float list;
    mutable args_high: float list;
    mutable inf: bool;
    mutable neg_inf: bool;
  }

let create_test mode f x =
  flush stdout;
  let (res_I, msg) = try (f x, "") with err -> (zero_I, Printexc.to_string err) in
  print_endline (if msg = "" then sprintf_I "%.25e" res_I else msg);
  flush stdout;
  { mode = mode;
    res_I = res_I;
    msg = msg;
    res_low = infinity;
    res_high = neg_infinity;
    args_low = [];
    args_high = [];
    inf = false;
    neg_inf = false; }

let test_I {low = a; high = b} =
  a = a && b = b && a <= b && a <> infinity && b <> neg_infinity

let twopi = 2.*.pi_I.high

let add_result infos args res =
  if res = res then (
    let resm =
      if infos.mode <> Mod2pi || infos.msg <> "" || infos.res_I.low <= res then res
      else (res +. twopi) in
    if resm = infinity then (
      infos.inf <- true;
      infos.args_high <- args)
    else if resm = neg_infinity then (
      infos.neg_inf <- true;
      infos.args_low <- args)
    else (
      if resm < infos.res_low then (
	infos.res_low <- resm; 
	infos.args_low <- args);
      if infos.res_high < resm then (
	infos.res_high <- resm; 
	infos.args_high <- args)))

let print_test infos =
  let error msg =
    if infos.res_low <= infos.res_high then
      Printf.printf "%s %s\nDEFINED\nArgs low: %s\nArgs high: %s\n" msg
	(sprintf_I "%.25e" {low = infos.res_low; high = infos.res_high})
	(String.concat " " (List.map (Printf.sprintf "%.25e") infos.args_low))
	(String.concat " " (List.map (Printf.sprintf "%.25e") infos.args_high))
    else print_endline msg;
    flush stdout;
    ignore (input_line stdin) in
  if infos.neg_inf && (
    infos.res_low = -.max_float || infos.res_low < infos.res_high) then
    infos.res_low <- neg_infinity;
  if infos.inf && (
    infos.res_high = max_float || infos.res_low < infos.res_high) then
    infos.res_high <- infinity;
  if infos.msg = "" then (
    if infos.res_low <= infos.res_high then (
      if not (test_I infos.res_I) then error "Interval not valid.\nShould be"
      else if infos.res_low < infos.res_I.low || 
      infos.res_I.high < infos.res_high then error "Should_contain"
      else if infos.mode = Exact &&
	(infos.res_low <> infos.res_I.low ||
	infos.res_high <> infos.res_I.high) then error "Should be")
    else error "Should fail.")
  else if infos.res_low <= infos.res_high then error "Should be"

let rec iter f = function
  | a::tl as l when a <> infinity ->
      let b_list = if a = neg_infinity then tl else l in
      List.iter (fun b -> f {low = a; high = b}) b_list;
      iter f tl
  | _ -> ()

let iter_in x_I f values =
  List.iter (fun x ->
    if x_I.low <= x && x <= x_I.high then 
      if x = 0. then (
	if x_I.low < 0. then f (-0.);
	if 0. < x_I.high || x_I.low = 0. then f 0.)
      else f x) (x_I.low::x_I.high::values)

let iter_finite f values =
  List.iter (fun x -> if classify_float x <> FP_infinite then f x) values

let check_I mode values bounds (name, f_list, f_I) =
  iter (fun x_I ->
    Printf.printf "%s %s =\n" name (sprintf_I "%.25e" x_I);
    let infos = create_test mode f_I x_I in
    iter_in x_I (fun x ->
      List.iter (fun f -> add_result infos [x] (f x)) f_list) values;
    print_test infos) bounds

let check_I_f mode values bounds (name, f_list, f_I_f) =
  iter (fun x_I -> iter_finite (fun y ->
    Printf.printf "%s %s %e =\n" name (sprintf_I "%e" x_I) y;
    let infos = create_test mode (f_I_f x_I) y in
    iter_in x_I (fun x ->
      if name = "pow" && x = 0. then (
	Printf.printf "%e ^ %e = %e\n" x y (List.hd f_list x y); 
	flush stdout);
      List.iter (fun f -> add_result infos [x; y] (f x y)) f_list) values;
    print_test infos) bounds) bounds

let check_f_I mode values bounds (name, f_list, f_f_I) =
  iter_finite (fun x -> iter (fun y_I ->
    Printf.printf "%s %e %s =\n" name x (sprintf_I "%e" y_I);
    let infos = create_test mode (f_f_I x) y_I in
    iter_in y_I (fun y ->
      List.iter (fun f -> add_result infos [x; y] (f x y)) f_list) values;
    print_test infos) bounds) bounds

let check_I_I mode values bounds (name, f_list, f_I_I) =
  iter (fun x_I -> iter (fun y_I ->
    Printf.printf "%s %s %s =\n" name (sprintf_I "%e" x_I) (sprintf_I "%e" y_I);
    let infos = create_test mode (f_I_I x_I) y_I in
    iter_in x_I  (fun x -> iter_in y_I (fun y ->
      List.iter (fun f -> add_result infos [x; y] (f x y)) f_list)
	values) values;
    print_test infos) bounds) bounds

let check_I_i mode values bounds valuesi (name, f_list, f_I_i) =
  iter (fun x_I -> List.iter (fun n ->
    Printf.printf "%s %s %d =\n" name (sprintf_I "%e" x_I) n;
    let infos = create_test mode (f_I_i x_I) n in
    let ny = float n in
    iter_in x_I (fun x ->
      List.iter (fun f -> add_result infos [x; ny] (f x ny)) f_list) values;
    print_test infos) valuesi) bounds

let rnd_values = Array.init 1000 (fun i -> 1000.-.Random.float 2000.)

let speed_cmp1 loops (name, f) =
  let l = Array.length rnd_values in
  Printf.printf "%10s speed (%d calls):" name loops; flush stdout;
  let top = (Unix.times ()).Unix.tms_utime in
  for n = 1 to loops / l do Array.iteri (fun i x -> ignore (f x)) rnd_values done;
  let dt = (Unix.times ()).Unix.tms_utime -. top in
  Printf.printf "%f\n" dt; flush stdout

let speed_cmp2 loops (name, f) =
  let l = Array.length rnd_values in
  Printf.printf "%10s speed (%d calls):" name loops; flush stdout;
  let top = (Unix.times ()).Unix.tms_utime in
  for n = 1 to loops / l do 
    Array.iteri (fun i x -> ignore (f x x)) rnd_values;
  done;
  let dt = (Unix.times ()).Unix.tms_utime -. top in
  Printf.printf "%f\n" dt; flush stdout

let rnd_values_I = Array.init 1000 (fun i-> 
  let x1 = 1000.-.Random.float 2000. and x2 = Random.float 10. in
  {low=x1;high=x1+.x2})

let speed_cmp1_I loops (name, f) =
  let l = Array.length rnd_values_I in
  Printf.printf "%10s speed (%d calls):" name loops; flush stdout;
  let top = (Unix.times ()).Unix.tms_utime in
  for n = 1 to loops / l do Array.iteri (fun i x -> ignore (f x)) rnd_values_I done;
  let dt = (Unix.times ()).Unix.tms_utime -. top in
  Printf.printf "%f\n" dt; flush stdout

let speed_cmp2_I loops (name, f) =
  let l = Array.length rnd_values_I in
  Printf.printf "%10s speed (%d calls):" name loops; flush stdout;
  let top = (Unix.times ()).Unix.tms_utime in
  for n = 1 to loops / l do Array.iteri (fun i x -> ignore (f x x)) rnd_values_I done;
  let dt = (Unix.times ()).Unix.tms_utime -. top in
  Printf.printf "%f\n" dt; flush stdout


let inv x = 1./.x
let inv_low x = fdiv_low 1. x
let inv_high x = fdiv_high 1. x

let atan_low y = fatan_low 1. y
let atan_high y = fatan_high 1. y

let myatan2 y x = if y = 0.&& x = 0. then nan else atan2 y x
let myatan2_low y x = if y = 0. && x = 0. then nan else fatan_low x y
let myatan2_high y x = if y = 0. && x = 0. then nan else fatan_high x y

let pospow x y =
  if x = 0. then fpow 0. y
  else if x = infinity || y = infinity || y = neg_infinity then fpow x y
  else flog_pow x y

let _ =

  let top = Sys.time () in

  let o3 = 1./.3. and o7 = 1./.7. and e = exp 1. in
  let m1 = 1.-.epsilon_float and p1 = 1.+.epsilon_float in
  let values = [-.max_float; -.10.; -.1.; -.o7; 0.; o7; 1.; 10.; max_float] in
  let valuesi =  [min_int; -1000; -1; 0; 1; 10; 1000; 1073741823] in
  let bounds = [neg_infinity; -.max_float /.2.; -.e; -.p1; -1.; -.m1; -.o3;
		0.; o3; m1; 1.; p1; e; max_float /.2.; infinity] in

  let pio2_I = pi_I /$.2. and da = acos (1.-.epsilon_float) in
  let rec add_mul al ah da i j l0 =
    if i <= j then float i *.al -.da::float i *.ah +.da::add_mul al ah da (i + 1) j l0
    else l0 in
  let pio2s =
    add_mul pio2_I.low pio2_I.high 0. (-1010) (-990) (
    add_mul pio2_I.low pio2_I.high 0. (-10) 10 (
    add_mul pio2_I.low pio2_I.high 0. 990 1010 [])) in
  let angles = 
    neg_infinity::
    add_mul pio2_I.low pio2_I.high da (-1006) (-994) (
    add_mul pio2_I.low pio2_I.high da (-6) 6 (
    add_mul pio2_I.low pio2_I.high da 994 1006 [infinity])) in

  List.iter (check_I_f Exact values bounds)
    [ ("+", [(+.); fadd_low; fadd_high], ( +$.));
      ("-", [(-.); fsub_low; fsub_high], ( -$.));
      ("*", [( *.); fmul_low; fmul_high], ( *$.));
      ("/", [(/.); fdiv_low; fdiv_high], ( /$.));
      ("**", [fpow; fpow_low; fpow_high], ( **$.));];

  List.iter (check_I Exact values bounds)
    [ ("abs",  [abs_float], abs_I);
      ("inv",  [inv; inv_low; inv_high], inv_I);
      ("sqrt", [sqrt; fsqrt_low; fsqrt_high], sqrt_I);
      ("log",  [log; flog_low; flog_high], log_I);
      ("exp",  [ exp; fexp_low; fexp_high], exp_I);
      ("atan", [atan; atan_low; atan_high], atan_I);
      ("asin", [asin; fasin_low; fasin_high], asin_I);
      ("acos", [facos; facos_low; facos_high], acos_I);
      ("cosh", [cosh; fcosh_low; fcosh_high], cosh_I);
      ("sinh", [sinh; fsinh_low; fsinh_high], sinh_I);
      ("tanh", [tanh; ftanh_low; ftanh_high], tanh_I);];

  List.iter (check_I Exact pio2s angles)
    [ ("cos", [cos; fcos_low; fcos_high], cos_I);
      ("sin", [sin; fsin_low; fsin_high], sin_I)];
  check_I In pio2s angles ("tan", [ftan; ftan_low; ftan_high], tan_I);

  check_I_f In values bounds ("mod_I_f", [fmod; mod_float], mod_I_f);
  check_I_i Exact values bounds valuesi
    ("powi", [fpow; fpow_low; fpow_high], pow_I_i);

  List.iter (check_f_I Exact values bounds) 
    [ ("+.$", [(+.); fadd_low; fadd_high], ( +.$));
      ("-.$", [(+.); fadd_low; fadd_high], ( +.$));
      ("*.$", [(+.); fadd_low; fadd_high], ( +.$)); 
      ("/.$", [(/.); fdiv_low; fdiv_high], ( /.$));
      ("**.$", [pospow; flog_pow_low; flog_pow_high], ( **.$)) ];

  List.iter (check_I_I Exact values bounds) 
    [ ("+", [(+.); fadd_low; fadd_high], ( +$));
      ("-", [(-.); fsub_low; fsub_high], ( -$));
      ("*", [( *.); fmul_low; fmul_high], ( *$));
      ("/", [(/.); fdiv_low; fdiv_high], ( /$));
      ("max", [ max; max; max], max_I_I);
      ("min", [ min; min; min], min_I_I)];

  List.iter (check_I_I Exact values bounds)
    [ ("atan2", [myatan2; myatan2_low; myatan2_high], atan2_I_I);
      ("**$", [pospow; flog_pow_low; flog_pow_high], ( **$) ) ];

  check_I_I Mod2pi values bounds 
    ("atan2mod", [myatan2; myatan2_low; myatan2_high], atan2mod_I_I);
  
  Printf.printf "%f seconds.\n" (Sys.time () -. top);
  flush stdout;

  List.iter (speed_cmp1 10000000) [
  ("tan", tan); ("ftan", ftan); ("cos", cos); ("fcos", fcos); ("sin", sin); ("fsin", fsin) ];

  List.iter (speed_cmp1_I 10000000) [
  ("tan_I", tan_I);("cos_I",cos_I);("sin_I",sin_I) ];

  List.iter (speed_cmp2 10000000) [
  ("+.", (+.)); ("fadd", fadd); ("-.", (-.)); ("fsub", fsub);
  ("*.", ( *.)); ("fmul", fmul); ("/.", (/.)); ("fdiv", fdiv);
  ("**", ( ** )); ("pow", fpow); ("mod_float", mod_float); ("fmod", fmod)];

  List.iter (speed_cmp2_I 10000000) [
  ("+$", (+$)); ("-$", (-$)); 
  ("*$", ( *$)); ("/$", (/$))];

    
