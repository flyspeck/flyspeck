(*
    Copyright 1999 Pascal Brisset / Jean-Marc Alliot

    This file is part of the ocaml pqueue library.

    The ocaml pqueue library is free software: 
    you can redistribute it and/or modify it under the terms of 
    the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    The ocaml pqueue library is distributed in the hope that it will be 
    useful,but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public 
    License along with the ocaml pqueue library.  
    If not, see <http://www.gnu.org/licenses/>.
*)

type ('a, 'b) pqueue
and ('a, 'b) element

val empty : unit -> ('a, 'b) pqueue

val insert : 'a -> 'b -> ('a, 'b) pqueue ->
                (('a, 'b) element)*(('a, 'b) pqueue)

val extract : ('a, 'b) pqueue -> ('a * 'b * ('a, 'b) pqueue)
(* expt Not_found *)

val suppress : ('a, 'b) element -> unit

val unpack : ('a, 'b) element -> 'a * 'b
