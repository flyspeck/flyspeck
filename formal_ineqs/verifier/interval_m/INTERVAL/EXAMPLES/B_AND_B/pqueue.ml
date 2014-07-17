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
type ('a, 'b) pqueue = Node of ('a,'b) pqueuenode
                     | Nil
and ('a, 'b) pqueuenode = {valid : bool ref;
                           key : 'a;
                           value: 'b;
                           left : ('a, 'b) pqueue;
                           right : ('a, 'b) pqueue}
and ('a, 'b) element = ('a, 'b) pqueuenode

let empty = fun () -> Nil

let rec climb = function
  | {left = Nil; right = Nil} -> Nil
  | {left = Nil; right = r} -> r
  | {left = l; right = Nil} -> l
  | {left = (Node l) as ll; right = (Node r) as rr} ->
    if l.key < r.key
    then Node {valid = l.valid; key = l.key; value = l.value; left = climb l;right= rr}
    else Node {valid = r.valid; key = r.key; value = r.value; left = ll;right= climb r}
  
let rec insert flag key value = function
    Nil -> let e = {valid = flag; key = key; value = value;
                    left = Nil; right = Nil}
           in (e , Node e)
  | (Node ({valid=f} as n)) when !f = false ->
     insert flag key value (climb n)
  | (Node ({valid = x; key = k; value = v; left = l; right = r} as n)) ->
      if k < key
      then let (e, new_r) = insert flag key value r
           in (e, Node {valid=x;right=l; left = new_r; key = k; value = v})
      else let (_, new_r) = insert x k v r
           in let e = {valid=flag;right= l; left = new_r;
	               key = key; value = value}
	   in (e, Node e)

let insert key value =
  insert (ref true) key value
	    


let rec extract = function
  Nil -> raise Not_found
| Node ({valid = f} as n) when !f = false -> extract (climb n)
| Node ({key = k; value = v; left = l; right = r} as n) ->
    (k, v, climb n)


let suppress n = n.valid := false
     
      
let unpack = function
  {valid = f} when !f = false -> raise (Failure "unpack")
| {key =k; value= v} ->
  (k,v)
