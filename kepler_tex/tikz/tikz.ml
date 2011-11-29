(* ========================================================================== *)
(* FLYSPECK - BOOK PREPARATION                                                *)
(*                                                                            *)
(* Chapter: Graphics                                                          *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2011-11-26                                                           *)
(* ========================================================================== *)

(* 
Some procedures to facilitate the generation of tikz graphics.
Output in fig.tex.
*)

let output_filestring tmpfile a = 
  let outs = open_out tmpfile in
  let _ = try (Printf.fprintf outs "%s" a) 
  with _ as t -> (close_out outs; raise t) in
   close_out outs ;;

let unsplit d f = function
  | (x::xs) ->  List.fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_comma  = unsplit "," (fun x-> x);;

let join_lines  = unsplit "\n" (fun x-> x);;

let join_space  = unsplit " " (fun x-> x);;



(* math *)

let cos = Pervasives.cos;;
let sin = Pervasives.sin;;
let sqrt = Pervasives.sqrt;;
let pi = 4.0 *. atan(1.0);;
let nth = List.nth;;

(* arg between 0 and 2pi *)

let arg x y = if (y<0.0) then atan2 y x +. 2.0 *. pi else atan2 y x;;

let degree x = 180.0 *. x /. pi;;


(* vector sum, difference, scalar product, dot product *)

let map3 f (x,y,z) = (f x,f y,f z);;

let map2 f (x,y) = (f x , f y);;

let (+..) (x1,x2) (y1,y2) = (x1+. y1,x2+. y2);;

let (-..)  (x1,x2) (y1,y2) = (x1-. y1,x2-. y2);;

let uminus3 (x1,x2,x3) = (-. x1,-.x2,-.x3);;

let uminus2 (x1,x2) = (-. x1,-.x2);;

let ( %.. ) s (x1,x2) = (s *. x1, s *. x2);; 

let ( *.. ) (x1,x2) (y1,y2) = (x1 *. y1 +. x2 *. y2);;

let (+...) (x1,x2,x3) (y1,y2,y3) = (x1 +. y1, x2 +. y2, x3+. y3);;

let (-...) (x1,x2,x3) (y1,y2,y3) = (x1 -. y1, x2 -. y2, x3-. y3);;

let ( %... ) s (x1,x2,x3) = (s *. x1, s *. x2, s*. x3);; 

let ( *... ) (x1,x2,x3) (y1,y2,y3) = (x1 *. y1 +. x2 *. y2 +. x3 *. y3);;

let cross (x1,x2,x3) (y1,y2,y3) = 
  (x2 *. y3 -. x3 *. y2, x3 *. y1 -. x1 *. y3, x1 *. y2 -. x2 *. y1);;

let det3 x y z = x *... (cross y z);;

let conj (x,y) = (x,-. y);;

let cmul (x1,y1) (x2,y2) = (x1 *. x2 -. y1 *. y2, x1 *. y2 +. x2 *. y1);;

let cinv v = (1.0/. (v *.. v)) %.. (conj v);;

let cdiv u v = cmul u (cinv v);;
   

let delta1 = (1.0,0.0,0.0);;

let delta2 = (0.0,1.0,0.0);;

let delta3 = (0.0,0.0,1.0);;

let proj e1 e2 x = (x *... e1) , (x *... e2);;

let perp p x  =  x -... (((x *... p) /. (p *... p)) $... p) ;; (* ortho to p *)

let transpose ((a11,a12,a13),(a21,a22,a23),(a31,a32,a33)) = 
  ((a11,a21,a31),(a12,a22,a32),(a13,a23,a33));;

let mul3 (e1,e2,e3) x = 
     (e1 *... x,  e2 *... x, e3 *... x);;

let tuple3 [v1;v2;v3] = (v1,v2,v3);;

let list3 (v1,v2,v3) = [v1;v2;v3];;

let tuple2 [v1;v2] = (v1,v2);;

let list2 (v1,v2) = [v1;v2];;

let normalize3 x = (1.0 /. sqrt(x *... x)) %... x;;

let normalize2 x = (1.0 /. sqrt(x *.. x)) %.. x;;

let dist3 x y = 
  let z = x -... y in sqrt (z *... z);;

let dist2 x y = 
  let z = x -.. y in sqrt (z *.. z);;

let rec outer x y = 
  match x with
    | [] -> []
    | a::r -> (map (fun i -> (a,i)) y) @ (outer r y);;

let solve33 (m1,m2,m3) c =    (* solve m.x ==c for x by Cramer *)
  let d = det3 m1 m2 m3 in
  let (t1,t2,t3) = transpose (m1,m2,m3) in
   map3 (fun t -> t/. d) (det3 c t2 t3, det3 t1 c t3, det3 t1 t2 c);;

let extreme_point M = 
  solve33 M (map3 (fun m -> 0.5 *. (m *... m)) M);;

let lex3 (i,j,k) (i',j',k') = (i<i') or ((i=i') &&(j<j')) or ((i=i')&&(j=j')&&(k<k'));;


let frame_of v1 v2 = 
  let e1 = normalize3 (v1) in
  let e2 = normalize3 (perp e1 v2) in
  let e3 = cross e1 e2 in
    (e1,e2,e3);;
  
let random_SO3 () = 
  let v3 () = tuple3 (map (fun _ -> -1.0 +. Random.float 2.0) [0;0;0]) in
    frame_of (v3()) (v3());;


(* TIKZ OUTPUT *)

let ppair (x,y) = Printf.sprintf "(%f,%f)" x y;;

let pcoord s (x,y) = 
  Printf.sprintf "\coordinate (%s) at (%f,%f) " s x y;;

let plet s y = 
  Printf.sprintf "\pgfmathsetmacro\%s{%s}" s y;;



(* specific cases *)

let orig3 = (0.0,0.0,0.0);;

let orig2 = (0.0,0.0);;

let fix_SO3 =  (*  random_SO3 () ;;  *)
  ((-0.623709278332764572, -0.768294961660169751, -0.143908262477248777),
   (-0.592350038826666592, 0.34445174255424732, 0.728336754910384077),
   (-0.510008007411323683, 0.539514456654259789, -0.669937298138706616));;


(* vertices of an icosahedron, vector lengths sqrt3. *)

let icos_vertex =
  let sqrt3 = sqrt(3.0) in
  let v = sqrt3 %... (1.0,0.0,0.0) in
  let d0 = 2.10292 in  (* 20 Solid[2,2,2,d0,d0,d0] = 4 Pi *)
  let theta = 1.10715 in (* arc[2,2,d0] = theta *)
  let ct = cos theta in
  let st = sin theta in 
  let p5 = pi/. 5.0 in
  let vv =    map (mul3 fix_SO3)  
    ( v :: map 
       (fun i->  (sqrt3 %... (ct, st *. cos (i *. p5), st *. sin (i *. p5)))) 
       [2.0;4.0;6.0;8.0;10.0]) in
   (vv @ (map ( uminus3 ) vv));;

let iv  = nth icos_vertex;;

let icos_edge = 
  let v i = nth icos_vertex i in
  let dall = filter (fun (i,j) -> (i<j)) (outer (0--11) (0--11)) in
   filter (fun (i,j) -> dist3 (v i) (v j) < 2.2) dall;;  (* note 2.2 cutoff *)

let icos_face = 
  let micos (i,j) = mem ( i, j ) icos_edge in
  let balance (i,(j,k)) = (i,j,k) in
    map balance (filter (fun (i,(j,k)) -> micos (i,j) && micos (i,k) && micos (j,k)) 
     (outer (0--11) (outer (0--11) (0--11))));;

let dodec_vertex = 
  map (fun (i,j,k) -> extreme_point (iv i,iv j,iv k)) icos_face;;  (* voronoi cell vertices *)

let next_icos_face (a,b,u3)=  (* input flag: [a] subset u2 subset u3 *)
  let v3 = list3 u3  in
  let _ = mem a v3 or failwith "next_dodec_face a" in
  let _ = mem b v3 or failwith "next_dodec_face b" in
  let ifc = map (tuple3) (filter (subset [a;b]) (map list3 icos_face)) in
  let ifc' = subtract ifc [u3] in
  let _ = List.length ifc' = 1 or failwith "next_dodec_face c" in
  let w3 = nth ifc' 0 in
  let cx = subtract (list3 w3) [a;b] in 
  let _ = List.length cx = 1 or failwith "next_dodec_face d" in
  let c = hd cx in
  let w2x = filter (fun (i,j)->(i<j)) [(a,c);(c,a)] in
  let _ = List.length w2x = 1 or failwith "next_dodec_face e" in
  let w2 = nth w2x 0 in
    (a,c,w3);;

let icos_vertex_cycle a = 
  let [i;j;k] = hd (filter (mem a) (map list3 icos_face)) in
  let startp = (a,(if (a=i) then j else i),(i,j,k)) in
  let t = map (fun i -> funpow i next_icos_face startp) [0;1;2;3;4] in
    map (fun (_,_,u) -> u) t;;

let icos_cycles = map icos_vertex_cycle (0--11);;

let ht xxs = 
  let (_,_,z) = end_itlist ( +... ) xxs in
    z;;

let sort_dodec_face = 
  let t = icos_cycles in
  let lookup = zip icos_face dodec_vertex in
  let htc cycle = ht (map (fun i -> assoc i lookup) cycle) in
  let hts = map htc t in
  let z = zip hts t in
  let z' = filter (fun (h,_) -> (h>0.0)) z in
  let t' = map snd (sort (fun (a,_) (b,_) -> a<b) z') in
    t';;

let center_face cycle = 
  let lookup = zip icos_face dodec_vertex in
  let coords = map (fun i -> assoc i lookup) cycle in
    (1.0 /. float_of_int (List.length cycle)) %... (end_itlist (+...) coords);;

let pname (i,j,k) = Printf.sprintf "V%d-%d-%d" i j k;;

let print_cycles = 
  let lookup = zip icos_face (map (proj delta1 delta2) dodec_vertex) in
    map (fun r,(x,y) -> Printf.sprintf "\coordinate (%s) at (%f,%f);" (pname r) x y) lookup;;

let print_dodec_face = 
  let opt = "fill=white" in
  let pdraw = Printf.sprintf "\draw[%s] " opt in
  let cycle m = join_space (map ((Printf.sprintf "(%s)--") o pname) m) in
  let s m = pdraw ^ (cycle m) ^ "cycle;" in 
    map s sort_dodec_face;;

(* let print_dodec = join_lines (print_cycles @ print_dodec_face);; *)



(* printing spherical caps.
   Parameters: 
     R = radius of sphere at the origin
     v =(_,_,_) norm 1 vector pointing to center of cap.
     theta = arclength on unit sphere of cap.

*)



let frame_cap v = 
  let v = normalize3 v in
  let (x,y,z) = v in
  let w = normalize3 (-. y,x,0.0) in
  frame_of v w;;
    
let ellipse_param v R theta = 
  let (v,w,u) = frame_cap v in
  let q = (R *. cos theta) %... v in
  let qbar = proj delta1 delta2 q in
  let p = ((R *. cos theta) %... v) +... ((R *. sin theta) %... u) in
  let pbar = proj delta1 delta2 p in
  let h = dist2 qbar pbar in
  let k = R *. sin theta in
    (qbar,h,k);;

let calc_psi theta v = 
  let (x,y,_) = normalize3 v in
  let cospsi = cos theta /. sqrt( x *. x +. y *. y) in
    if (abs_float cospsi <= 1.0) then acos cospsi else 0.0;;

let calc_alpha R psi qbar =
  let nqbar = normalize2 qbar in 
  let rtrue = cmul (R *. cos psi, R *. sin psi) nqbar in
  let a = normalize2 (rtrue -.. qbar) in
    acos (a *.. nqbar);;

let adjust_alpha h k alpha =  (* compensate for TIKZ BUG in arc specs *)
  let ca = cos alpha in
  let sa = sin alpha in
  let t = 1.0 /. sqrt(ca *. ca /. (h *. h) +. sa *. sa /. (k *. k)) in
    acos (t *. ca /. h);;

let print_ellipse R qbar h k psi = 
  let nqbar = normalize2 qbar in
  let r = (R *. cos psi, R *. sin psi) in
  let (qbx,qby) = qbar in
  let (px,py) = cmul r nqbar in
  let (px',py') = cmul (conj r) nqbar in
  let alpha = adjust_alpha h k (calc_alpha R psi qbar) in
  let endangle = 2.0 *. pi -. alpha in
  let rotateAngle = degree (arg qbx qby) in
  let cstart = degree (arg px' py') in
  let delta = 2.0 *. psi in 
  let s = "\\draw[ball color=gray!10,shading=ball] (0,0) circle (1);\n\\end{scope}" in
    if (psi<0.01) then
       Printf.sprintf
	"\\begin{scope} \\clip (%f,%f) circle[x radius=%f,y radius=%f,rotate=%f];\n%s"
	qbx qby h k rotateAngle s
    else
      Printf.sprintf 
	"\\begin{scope}\\clip (%f,%f) arc[x radius=%f,y radius = %f,start angle=%f,end angle=%f,rotate=%f] arc[radius=1.0,start angle=%f,delta angle=%f];\pgfpathclose;\n%s"
	px py h k  (degree alpha) (degree endangle) rotateAngle
        cstart (degree delta)
	s;;

let print_dodec_ellipse = 
  let vs = map center_face sort_dodec_face in
  let theta = pi /. 6.0 in
  let R = 1.0 in
  let one_ellipse v = 
    let (q,h,k) = ellipse_param v R theta in
    let psi = calc_psi theta v in
     print_ellipse R q h k psi in
    map one_ellipse vs;;

let outstring = ref "";;

let wrap s s' = Printf.sprintf "\\def\\%s{%s}\n\n\n" s s';;

outstring := !outstring ^ 
  wrap "autoZXEVDCA"   (join_lines (print_cycles @ print_dodec_face @ print_dodec_ellipse))
 ;;


output_filestring "/tmp/x.txt" (!outstring);;
  
