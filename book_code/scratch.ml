exit 0;;
1;;

#use "lpproc.ml";;
#use "sphere.ml";;


h16max;;

switch_edge h16Amax;;
let rr = switch_edge b16Amax;;
let tt = flatten (map switch_edge rr);;
tt;;
let uu = nth tt 0;;
display_ampl uu;;


dih2_y 2.0 2.1 2.2 2.3 2.4 2.5 -. dih_y 2.1 2.2 2.0 2.4 2.5 2.3;;

mem;;
nth;;
std_face_of_size;;

rotateL;;
let ffg = std_face_of_size pent_bb 3;;
let ffg = flatten (map (fun t -> [t; rotateL 1 t; rotateL 2 t]) ffg) ;;
1;;
