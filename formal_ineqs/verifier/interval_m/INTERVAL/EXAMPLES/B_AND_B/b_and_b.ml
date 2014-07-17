(*
    Copyright 2004 Jean-Marc Alliot / Nicolas Durand

    This file is part of the ocaml branch-and-bound library.

    The ocaml branch-and-bound library is free software: 
    you can redistribute it and/or modify it under the terms of 
    the GNU Lesser General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    The ocaml branch-and-bound library is distributed in the hope that it will be 
    useful,but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public 
    License along with the ocaml branch-and-bound library.  
    If not, see <http://www.gnu.org/licenses/>.
*)

(* VERY simple example of Branch and Bound using interval computation
for function optimization *)

open Interval;;

let cut_X v = 
  let (k,_,_) = Array.fold_left (fun (k,maxv,i) x-> 
    if (size_I x)>maxv then  (i,(size_I x),i+1) else (k,maxv,i+1)) (-1,-1.0,0) v in
  let int1= Array.copy v and int2= Array.copy v in
  let midp=(v.(k).low +. v.(k).high)/. 2.0 in 
  int1.(k)<-{low=v.(k).low;high=midp};int2.(k)<-{low=midp;high=v.(k).high};
  (int1,int2);;

let estimatormid f_x v =
  let midpoint = Array.map (fun x -> (x.high +. x.low)/. 2.0) v in
  (f_x midpoint,midpoint);;


let branch_and_bound f_x f_X start_inter precisionx precisionfx =
  let queue = ref (Pqueue.empty ()) in
  let (pvi,pi) = estimatormid f_x start_inter and fxi = f_X start_inter in
  let best_v = ref pvi in 
  let best = ref (start_inter,fxi,pi,pvi) in
  let test_inter int =
    let fint = f_X int in
    if !best_v <fint.high then
      let (pv,p)= estimatormid f_x int in 
      let (_,newq)= Pqueue.insert (-.pv) (int,fint) !queue in
      queue:=newq;
      if pv> !best_v then (best_v:= pv;best:=(int,fint,p,pv)) in

  let (_,newq)=(Pqueue.insert (-.pvi) (start_inter,fxi) !queue) in
  queue := newq;
  try (while (true) do 
    let (_,(x,fx),newq)= Pqueue.extract !queue in
    queue:= newq;
    if (fx.high > !best_v) & ((size_I fx) > precisionfx) & ((size_max_X x) > precisionx) then
      let (int1,int2)= (cut_X x) in test_inter int1;test_inter int2;
    done;
    failwith "Should never happen in b_and_b")
  with 
      Not_found -> !best
