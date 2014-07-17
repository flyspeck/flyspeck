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

(**
Aliases floating point functions to their "constant" counterparts.

As described in the [Fpu] module documentation, there are problems when mixing
some C-lib or ocaml native functions with interval programming on 64 bits machine.

The standard floating point functions results will always lie in the [low; high] 
interval computed by the Fpu module, but they are slightly different on 32 and 64 
bits machines.

Using [Open Fpu_rename_all] at the beginning of your program guarantees that floating 
computation will give the same results on 32 and 64 bits machines. This is not 
mandatory but might help.

NB: while most transcendantal function are almost as fast, and sometimes faster than
their "standard" ocaml counterparts, +. -. *. and /. are much slower (from 50% to 100%
depending on the processor. If you want to rename transcendantal functions but not
+. -. *. and /. then use the [Fpu_rename] module.
*)

val (+.) : float -> float -> float
(** Computes x + y *)

val (-.) : float -> float -> float
(** Computes x - y *)

val (/.) : float -> float -> float
(** Computes x / y *)

val ( *.) : float -> float -> float
(** Computes x * y *)

val mod_float : float -> float -> float
(** Computes x mod y *)

val sqrt : float -> float
(** square root function*)

val log : float -> float
(** log function *)

val exp : float -> float
(** exp function *)

val ( ** ) : float -> float -> float
(** Computes x^y *)

val cos : float -> float
(** Computes cos(x) for x in \[-2^63, 2^63\] *)

val sin : float -> float
(** Computes sin(x) for x in \[-2^63, 2^63\] *)

val tan : float -> float
(** Computes tan(x) for x in \[-2^63, 2^63\] *)

val asin : float -> float
(** arc-sinus function *)

val acos : float -> float
(** arc-cosine function *)

val atan2 : float -> float -> float
(** atan2 function *)

val atan : float -> float
(** arc-tan function *)

val cosh: float -> float
(** cosh function *)

val sinh: float -> float
(** sinh function *)

val tanh: float -> float
(** tanh function *)
