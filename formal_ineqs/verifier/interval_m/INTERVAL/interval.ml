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



type interval = {low: float; high: float}

let zero_I = {low=0.;high=0.}
let one_I = {low=1.;high=1.}

let print_I x = Printf.printf "[%f, %f] " x.low x.high

let sprintf_I format i = 
  Printf.sprintf "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let fprintf_I fp format i = 
  Printf.fprintf fp "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let printf_I format i = 
  Printf.fprintf stdout "[%s, %s]" 
    (Printf.sprintf format i.low) (Printf.sprintf format i.high) 

let is_NaN (x : float) = x <> x

let compare_I_f {low = a; high = b} x =
  if b < x then 1 else if a <= x then 0 else -1

let (<$.) = compare_I_f

let size_I x = x.high -. x.low

let abs_I ({low = a; high = b} as x) =
  if 0. <= a then x
  else if b <= 0. then {low = -.b; high = -.a}
  else {low = 0.; high = max (-.a) b}

let sgn_I {low = a; high = b} =
  {low = float (compare a 0.); high = float (compare b 0.)}

let truncate_I x =
  {low = floor x.low; high = ceil x.high}

let union_I_I x y = {low = min x.low y.low; high = max x.high y.high}

let max_I_I x y = {low = max x.low y.low; high = max x.high y.high}

let min_I_I x y = {low = min x.low y.low; high = min x.high y.high}


external (+$) : interval -> interval -> interval = "fadd_I_caml"
external (-$) : interval -> interval -> interval = "fsub_I_caml"

(*
let (+$) {low = a; high = b} {low = c; high = d} =
  {low = fadd_low a c; high = fadd_high b d}
*)

external (+$.) : interval -> float -> interval = "fadd_I_x_caml"

let (+.$) x a = a +$. x
  
(*
let (+$.) {low = a; high = b} x =
  {low = fadd_low a x; high = fadd_high b x}
*)

(*
let (-$) {low = a; high = b} {low = c; high = d} =
  {low = fsub_low a d; high = fsub_high b c}
*)

external (-$.) : interval -> float -> interval = "fsub_I_x_caml"
external (-.$) : float -> interval -> interval = "fsub_x_I_caml"

(*
let (-$.) {low = a; high = b} y =
  {low = fsub_low a y; high = fsub_high b y}
*)

let (~-$) {low = a; high = b} = {low = -.b; high = -.a}

let ( *$) {low = a; high = b} {low = c; high = d} =
  let sa = compare a 0. and sb = compare b 0. in
  let sc = compare c 0. and sd = compare d 0. in
  if (sa = 0 && sb = 0) || (sc = 0 && sd = 0) then {low = 0.; high = 0.}
  else if sb <= 0 then
    if sd <= 0 then {low = fmul_low b d; high = fmul_high a c}
    else if 0 <= sc then {low = fmul_low a d; high = fmul_high b c}
    else {low = fmul_low a d; high = fmul_high a c}
  else if 0 <= sa then
    if sd <= 0 then {low = fmul_low b c; high = fmul_high a d}
    else if 0 <= sc then {low = fmul_low a c; high = fmul_high b d}
    else {low = fmul_low b c; high = fmul_high b d}
  else if 0 <= sc then {low = fmul_low a d; high = fmul_high b d}
  else if sd <= 0 then {low = fmul_low b c; high = fmul_high a c}
  else
    { low = min (fmul_low a d) (fmul_low b c);
      high = max (fmul_high a c) (fmul_high b d) }

let ( *$.) {low = a; high = b} y =
  let sy = compare y 0. in
  if sy = 0 then {low = 0.; high = 0.}
  else if sy < 0 then {low = fmul_low b y; high = fmul_high a y}
  else {low = fmul_low a y; high = fmul_high b y}

let ( *.$) y a = a *$. y

let (/$) {low = a; high = b} {low = c; high = d} =
  let sc = compare c 0. and sd = compare d 0. in
  if sd = 0 then
    if sc = 0 then failwith "/$"
    else if b <= 0. then
      {low = fdiv_low b c; high = if a = 0. then 0. else infinity}
    else if 0. <= a then {low = neg_infinity; high = fdiv_high a c}
    else {low = neg_infinity; high = infinity}
  else if sd < 0 then
    { low = if b <= 0. then fdiv_low b c else fdiv_low b d;
      high = if 0. <= a then fdiv_high a c else fdiv_high a d }
  else if sc = 0 then
    if b <= 0. then
      {low = if a = 0. then 0. else neg_infinity; high = fdiv_high b d}
    else if 0. <= a then {low = fdiv_low a d; high = infinity}
    else {low = neg_infinity; high = infinity}
  else if 0 < sc then
    { low = if a <= 0. then fdiv_low a c else fdiv_low a d;
      high = if b <= 0. then fdiv_high b d else fdiv_high b c }
  else if a = 0. && b = 0. then {low = 0.; high = 0.}
  else {low = neg_infinity; high = infinity}

let (/$.) {low = a; high = b} y =
  let sy = compare y 0. in
  if sy = 0 then failwith "/$."
  else if 0 < sy then {low = fdiv_low a y; high = fdiv_high b y}
  else {low = fdiv_low b y; high = fdiv_high a y}

let (/.$) x {low = a; high = b} =
  let sx = compare x 0. and sa = compare a 0. and sb = compare b 0. in
  if sx = 0 then
    if sa = 0 && sb = 0 then failwith "/.$" else {low = 0.; high = 0.}
  else if 0 < sa || sb < 0 then
    if 0 < sx then {low = fdiv_low x b; high = fdiv_high x a}
    else {low = fdiv_low x a; high = fdiv_high x b}
  else if sa = 0 then
    if sb = 0 then failwith "/.$"
    else if 0 <= sx then {low = fdiv_low x b; high = infinity}
    else {low = neg_infinity; high = fdiv_high x b}
  else if sb = 0 then
    if sx = 0 then {low = 0.; high = 0.}
    else if 0 <= sx then {low = neg_infinity; high = fdiv_high x a}
    else {low = fdiv_low x a; high = infinity}
  else {low = neg_infinity; high = infinity}

let mod_I_f {low = a; high = b} y =
  (* assume that the result of fmod is exact *)
  let sy = compare y 0. in
  let y = if sy = 0 then failwith "mod_I_f" else abs_float y in
  if 0. <= a then
    if fsub_high b a < y then (
      let ma = fmod a y and mb = fmod b y in
      if ma <= mb then {low = ma; high = mb} else {low = 0.; high = y})
    else {low = 0.; high = y}
  else if b <= 0. then
    if fsub_high b a < y then (
      let ma = fmod a y and mb = fmod b y in
      if ma <= mb then {low = ma; high = mb} else {low = -.y; high = 0.})
    else {low = -.y; high = 0.}
  else
    { low = if a <= -.y then -.y else fmod a y;
      high = if y <= b then y else fmod b y }

let inv_I {low = a; high = b} =
  let sa = compare a 0. and sb = compare b 0. in
  if sa = 0 then
    if sb = 0 then failwith "inv_I"
    else {low = fdiv_low 1. b; high = infinity}
  else if 0 < sa || sb < 0 then {low = fdiv_low 1. b; high = fdiv_high 1. a}
  else if sb = 0 then {low = neg_infinity; high = fdiv_high 1. a}
  else {low =  neg_infinity; high = infinity}

let sqrt_I {low = a; high = b} =
  if b < 0. then failwith "sqrt_I"
  else {low = if a < 0. then 0. else fsqrt_low a; high = fsqrt_high b}

let float_i n = {low = ffloat_low n; high = ffloat_high n}

let pow_I_i {low = a; high = b} n =
  let nf = float_i n in
  let pow_l x =
    if x = infinity then 0.
    else flog_pow_low x (if x < 1.0 then nf.high else nf.low) in
  let pow_h x =
    if x = infinity then infinity
    else flog_pow_high x (if x < 1.0 then nf.low else nf.high) in
  let sn = compare n 0 and sa = compare a 0. and sb = compare b 0. in
  if sn = 0 then if a = 0. && b = 0. then failwith "pow_I_i" else one_I
  else if sb < 0 then
    if n mod 2 = 0 then
      if 0 < sn then {low = pow_l (-.b); high = pow_h (-.a)}
      else {low = pow_l (-.a); high = pow_h (-.b)}
    else if 0 < sn then {low = -.pow_h (-.a); high = -.pow_l (-.b)}
    else {low = -.pow_h (-.b); high = -.pow_l (-.a)}
  else if 0 < sa then
    if 0 < sn then {low = pow_l a; high = pow_h b}
    else {low = pow_l b; high = pow_h a}
  else if n mod 2 = 0 then
    if 0 < sn then
      if sa = sb (* = 0. *) then {low = 0.; high = 0.}
      else {low = 0.; high = pow_h (max (-.a) b)}
    else if sa = sb (* = 0. *) then failwith "pow_I_i"
    else {low = pow_l (max (-.a) b); high = infinity}
  else if 0 < sn then
    { low = if sa = 0 then 0. else -.pow_h (-.a);
      high = if sb = 0 then 0. else pow_h b}
  else if sa = 0 then
    if sb = 0 then failwith "pow_I_i" else {low = pow_l b; high = infinity}
  else if sb = 0 then {low = neg_infinity; high = -.pow_l (-.a)}
  else {low = neg_infinity; high = infinity}

let ( **$.) {low = a; high = b} nf =
  let pow_l x = if x = infinity then 0. else flog_pow_low x nf in
  let pow_h x = if x = infinity then infinity else flog_pow_high x nf in
  let sn = compare nf 0. and sa = compare a 0. and sb = compare b 0. in
  if sn = 0 then if a = 0. && b = 0. then failwith "**$." else one_I
  else if sb < 0 then
    if floor nf <> nf then failwith "**$."
    else if fmod nf 2. = 0. then
      if 0 < sn then {low = flog_pow_low (-.b) nf; high = pow_h (-.a)}
      else {low = pow_l (-.a); high = flog_pow_high (-.b) nf}
    else if 0 < sn then {low = -.pow_h (-.a); high = -.flog_pow_low (-.b) nf}
    else {low = -.flog_pow_high (-.b) nf; high = -.pow_l (-.a)}
  else if 0 < sa then
    if 0 < sn then {low = flog_pow_low a nf; high = pow_h b}
    else {low = pow_l b; high = flog_pow_high a nf}
  else if floor nf <> nf then
    if 0 < sn then {low = 0.; high = if sb = 0 then 0. else pow_h b}
    else if sb = 0 then failwith "**$."
    else {low = pow_l b; high = infinity}
  else if fmod nf 2. = 0. then
    if 0 < sn then
      if sa = sb (* = 0. *) then {low = 0.; high = 0.}
      else {low = 0.; high = pow_h (max (-.a) b)}
    else if sa = sb (* = 0. *) then failwith "**$."
    else {low = pow_l (max (-.a) b); high = infinity}
  else if 0 < sn then
    { low = if sa = 0 then 0. else -.pow_h (-.a);
      high = if sb = 0 then 0. else pow_h b}
  else if sa = 0 then
    if sb = 0 then failwith "**$." else {low = pow_l b; high = infinity}
  else if sb = 0 then {low = neg_infinity; high = -.pow_l (-.a)}
  else {low = neg_infinity; high = infinity}

let ( **$) {low = a; high = b} {low = c; high = d} =
  let a = max 0. a in
  if b < 0. then failwith "**$"
  else if b = 0. then
    if d <= 0. then failwith "**$" else {low = 0.; high = 0.}
  else if a = 0. then
    if 0. <= c then
      {low = if d = 0. then 1. else 0.;
       high = fpow_high b (if b < 1. then c else d)}
    else if d <= 0. then
      {low = fpow_low b (if b < 1. then d else c); high = infinity}
    else {low = 0.; high = infinity}
  else if 0. <= c then
    { low = fpow_low a (if a < 1. then d else c);
      high = fpow_high b (if b < 1. then c else d) }
  else if d <= 0. then
    { low = fpow_low b (if b < 1. then d else c);
      high = fpow_high a (if a < 1. then c else d) }
  else if b < 1. then {low = fpow_low a d; high = fpow_high a c}
  else if 1. < a then {low = fpow_low b c; high = fpow_high b d}
  else {low = min (fpow_low a d) (fpow_low b c);
	high = max (fpow_high a c) (fpow_high b d)}

let ( **.$) x {low = a; high = b} =
  if x = 0. && 0. < b then {low = 0.; high = 0.}
  else if x <= 0. then failwith "**.$"
  else if x < 1. then
    if a = neg_infinity then
      if b = infinity then {low = 0.; high = infinity}
      else {low = flog_pow_low x b; high = infinity}
    else if b = infinity then {low = 0.; high = flog_pow_high x a}
    else {low = flog_pow_low x b; high = flog_pow_high x a}
  else if x = 1. then {low = 1.; high = 1.}
  else if a = neg_infinity then 
    if b = infinity then {low = 0.; high = infinity}
    else {low = 0.; high = flog_pow_high x b}
  else if b = infinity then {low = flog_pow_low x a; high = infinity}
  else {low = flog_pow_low x a; high = flog_pow_high x b}

let log_I {low = a; high = b} =
  let sb = compare b 0. in
  if sb <= 0 then failwith "log_I"
  else {low = if a <= 0. then neg_infinity else flog_low a; high = flog_high b}

let exp_I {low = a; high = b} =
  { low = if a = neg_infinity then 0. else fexp_low a;
    high = if b = infinity then infinity else fexp_high b}

let pi_I = {low = fatan_low (-1.) 0.; high = fatan_high (-1.) 0.}
let pi2_I = pi_I *$. 2.0
let pio2_I = {low = fatan_low 0. 1.; high = fatan_high 0. 1.}

let e_I = {low = fexp_low 1.0;high = fexp_high 1.0}

let sgn x =
  let sgn_low = compare x.low 0. and sgn_high = compare x.high 0. in
  if sgn_low <> sgn_high then 0 else sgn_low

let max_63 = ldexp 1. 63

external cos_I: interval -> interval = "fcos_I_caml"
external sin_I: interval -> interval = "fsin_I_caml"

let tan_I {low = a; high = b} =
  if -.max_63 <= a && b <= max_63 && fsub_high b a < pi_I.high then (
    let ta = ftan_low a in
    let tb = ftan_high b in
    if ta <= tb then {low = ta; high = tb}
    else {low = neg_infinity; high = infinity})
  else {low = neg_infinity; high = infinity}

let acos_I {low = a; high = b} =
  if a <= 1. && -1. <= b then
    {low = if b < 1. then facos_low b else 0.;
     high = if -1. < a then facos_high a else pi_I.high}
  else failwith "acos_I"

let asin_I {low = a; high = b} =
  if a <= 1. && -1. <= b then
    { low = if -1. < a then fasin_low a else -.pio2_I.high;
      high = if b < 1. then fasin_high b else pio2_I.high }
  else failwith "asin_I"

let atan_I {low = a; high = b} =
  { low = fatan_low 1. a; high = fatan_high 1. b}

let atan2mod_I_I {low = ya; high = yb} {low = xa; high = xb} =
  let sya = compare ya 0. and syb = compare yb 0. in
  let sxa = compare xa 0. and sxb = compare xb 0. in
  if syb < 0 then
    if sxb <= 0 then {low = fatan_low xa yb; high = fatan_high xb ya}
    else if 0 <= sxa then {low = fatan_low xa ya; high = fatan_high xb yb}
    else {low = fatan_low xa yb; high = fatan_high xb yb}
  else if 0 < sya then
    if sxb <= 0 then {low = fatan_low xb yb; high = fatan_high xa ya}
    else if 0 <= sxa then {low = fatan_low xb ya; high = fatan_high xa yb}
    else {low = fatan_low xb ya; high = fatan_high xa ya}
  else if sya = syb (* = 0. *) then
    if sxa = 0 && sxb = 0 then failwith "atan2mod_I_I"
    else if 0 <= sxa then zero_I
    else if sxb <= 0 then pi_I
    else {low = 0.; high = pi_I.high}
  else if sya = 0 then
    { low = if sxb <= 0 then fatan_low xb yb else 0.;
      high = if 0 <= sxa then fatan_high xa yb else pi_I.high}
  else if syb = 0 then
    { low = if 0 <= sxa then fatan_low xa ya else -.pi_I.high;
      high = if sxb <= 0 then fatan_high xb ya else 0. }
  else if sxb <= 0 then
    {low = fatan_low xb yb; high = fadd_high (fatan_high xb ya) pi2_I.high}
  else if 0 <= sxa then {low = fatan_low xa ya; high = fatan_high xa yb}
  else {low = -.pi_I.high; high = pi_I.high}

let atan2_I_I {low = ya; high = yb} {low = xa; high = xb} =
  let sya = compare ya 0. and syb = compare yb 0. in
  let sxa = compare xa 0. and sxb = compare xb 0. in
  if syb < 0 then
    if sxb <= 0 then {low = fatan_low xa yb; high = fatan_high xb ya}
    else if 0 <= sxa then {low = fatan_low xa ya; high = fatan_high xb yb}
    else {low = fatan_low xa yb; high = fatan_high xb yb}
  else if 0 < sya then
    if sxb <= 0 then {low = fatan_low xb yb; high = fatan_high xa ya}
    else if 0 <= sxa then {low = fatan_low xb ya; high = fatan_high xa yb}
    else {low = fatan_low xb ya; high = fatan_high xa ya}
  else if sya = syb then
    if sxb <= 0 then
      if sxa = 0 then failwith "atan2" else {low = pi_I.low; high = pi_I.high}
    else if 0 <= sxa then {low = 0.; high = 0.}
    else {low = 0.; high = pi_I.high}
  else if sya = 0 then
    { low = if 0 < sxb then 0. else fatan_low xb yb;
      high = if sxa < 0 then pi_I.high else fatan_high xa yb }
  else if syb = 0 then
    { low = if sxa < 0 then -.pi_I.high else fatan_low xa ya;
      high = if 0 < sxb then 0. else fatan_high xb ya }
  else if 0 <= sxa then {low = fatan_low xa ya; high = fatan_high xa yb}
  else {low = -.pi_I.high; high = pi_I.high}

let cosh_I {low = a; high = b} =
  if b < 0. then {low = fcosh_low b; high = fcosh_high a}
  else if a < 0. then {low = 1.; high = fcosh_high (max (-.a) b)}
  else {low = fcosh_low a; high = fcosh_high b}

let sinh_I {low = a; high = b} = {low = fsinh_low a; high = fsinh_high b}

let tanh_I {low = a; high = b} = {low = ftanh_low a; high = ftanh_high b}

let size_mean_X v =
  let add sum {low = a; high = b} = fadd_high sum (fsub_high b a) in
  Array.fold_left add 0. v /.float (Array.length v)

let size_max_X v =
  Array.fold_left (fun m {low = a; high = b} -> max m (fsub_high b a)) 0. v

let size_X = size_max_X
let size2_X = size_mean_X

let size_x v =
  Array.fold_left (fun m vi -> max m (abs_float vi)) 0. v

let print_X v = Array.iter print_I v

let fprintf_X fp format v = Array.iter (fprintf_I fp format) v

let printf_X format v = Array.iter (printf_I format) v

let fprintf_X fp format v = Array.iter (fprintf_I fp format) v

let sprintf_X format v =
  Array.fold_left (fun  s x -> (sprintf_I format x) ^ s) "" v

let pow_I_f = ( **$.)

let pow_I_I = ( **$)
