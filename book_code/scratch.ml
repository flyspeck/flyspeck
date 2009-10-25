exit 0;;
1;;

#use "lpproc.ml";;
#use "sphere.ml";;


let bb = h16max;;
let bb = c16Bmax;;
bb;;
display_lp bb;;
let tt = get_azim_table dih_y [4;9;3] bb;;
let tt = map (fun t -> (t,get_azim_table dih_y t bb)) (bb.bigtri);;
let tt = map (fun t -> (t,get_azim_table dih_y t bb)) [[2;0;1];[2;3;0];[2;4;3];[2;1;4]];;
let uu i = (display_lp (nth c16b i); get_yn 2);;
uu 100;;

tt;;
bb.bigtri;;
map (fun t -> (nth tt t)) [12;13;14;15;16;17;18;19;20;21];;

let get_dumpvar  s = (* read variables from dumpfile *)
  let com = sprintf "grep '%s' %s | sed 's/^.*= //'  " s dumpfile in
  let (ic,oc) = Unix.open_process(com) in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  inp;;
let float_of_dump s = float_of_string (hd s);;
get_dumpvar "yn.0.*=";;
let get_float s = float_of_dump(get_dumpvar s);;
let get_yn i = get_float (sprintf "yn.%d.*=" i);;
get_yn 2;;
let get_ye i xs bb = get_float (sprintf "ye.%d,%d.*=" i (wheremod (faces bb) xs));;
get_ye 2 [2;4;3] bb;;
let get_azim i xs bb = get_float (sprintf "azim.%d,%d.*=" i (wheremod (faces bb) xs));;
get_azim 2 [2;4;3] bb;;
let get_sol xs bb = get_float (sprintf "sol.%d.*=" (wheremod (faces bb) xs));;
get_sol [12;7;8] bb;;
let get_tau xs bb = get_float (sprintf "tau.%d.*=" (wheremod (faces bb) xs));;
get_tau [12;7;8] bb;;
let get_azim_table f xs bb = 
   let [y1;y2;y3] = map get_yn xs in
   let [y6;y4;y5] = map (fun i -> get_ye i xs bb) xs in
   let [a1;a2;a3] = map (fun i -> get_azim i xs bb) xs in
   let b1 = f y1 y2 y3 y4 y5 y6 in
   let b2 = f y2 y3 y1 y5 y6 y4 in
   let b3 = f y3 y1 y2 y6 y4 y5 in
   (y1,y2,y3,y4,y5,y6,(a1,b1),(a2,b2),(a3,b3));;
get_azim_table dih_y [2;4;3] bb;;
get_azim_table dih_y [2;3;0] bb;;
map (fun t -> (t,get_tau t bb)) bb.bigtri;;
let u  =  (map get_yn (upto 13));;
fold_right (+.)  u 0.0;;
bb.bigtri;;
bb;;

length c16b;;
let rec reverse (x::xs) = if (xs=[]) then [x] else (reverse xs) @ [x];;
let vals =  reverse (sort (compare) (map (fun t -> match t.lpvalue with | None -> 0.0 | Some x -> x) c16b));;


sort;;
