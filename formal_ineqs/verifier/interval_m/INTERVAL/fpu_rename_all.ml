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
let (+.) = fadd
let (-.) = fsub
let ( *.) = fmul
let (/.) = fdiv
let mod_float = fmod
let sqrt = fsqrt
let log = flog
let exp = fexp
let ( ** ) = fpow
let cos = fcos
let sin = fsin
let tan = ftan
let asin = fasin
let acos = facos
let atan x = fatan 1.0 x
let atan2 x y = fatan y x
let cosh x = fcosh x
let sinh x = fsinh x
let tanh x = ftanh x

