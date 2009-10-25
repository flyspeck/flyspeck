exit 0;;
1;;

#use "lpproc.ml";;
#use "sphere.ml";;


h16max;;

switch_edge b16Amax;;
let rr = switch_edge b16Amax;;
let tt = flatten (map switch_edge rr);;
tt;;
let uu = nth tt 0;;
display_ampl uu;;
dih_y 2.0256 2.3640 2.0023 2.0 2.3574 2.2886;;
dih_y 2.0256 2.3640 2.0022 2.0 2.3198 2.2886;;
dih2_y 2.3640 2.0256 2.0023 2.3574 2.0 2.2886;;


let one_epass bbs = 
  let branches = flatten (map switch_edge bbs) in
    Sys.command (sprintf "echo V STACK %d %d" (length bbs) (nextc()));
    filterout_infeas feasible branches;;
one_epass b16a;;
let branches = let bbs = b16a in flatten (map switch_edge bbs) ;;
let uu = (nth branches 0);;
ampl_of_bb stdout uu;;

dih2_y 2.0 2.1 2.2 2.3 2.4 2.5 -. dih_y 2.1 2.2 2.0 2.4 2.5 2.3;;

mem;;
nth;;
std_face_of_size;;

rotateL;;
let ffg = std_face_of_size pent_bb 3;;
let ffg = flatten (map (fun t -> [t; rotateL 1 t; rotateL 2 t]) ffg) ;;
1;;

#a
azim_med_big 'ID[3872614111]' {(i,i2,i3,j) in EDART : (i2,j) in BIGEDGE and (i,j) in HLLTRI and i in MEDIUMHIGHVERTEX}:
  -azim[i,j] >= -1.542
     -0.362519*(y1[i,j]-2.36)
      0.298691*(y2[i,j]-2)
      0.287065*(y3[i,j]-2)
      -0.920785*(y4[i,j]-2.25)
      0.190917*(y5[i,j]-2)
      0.219132*(y6[i,j]-2) ;
   #  {-0.362519, 0.298691, 0.287065, -0.920785, 0.190917, 0.219132};


     -0.362519*(y1[i,j]-2.36)
      0.298691*(y2[i,j]-2)
      0.287065*(y3[i,j]-2)
      -0.920785*(y4[i,j]-2.25)
      0.190917*(y5[i,j]-2)
      0.219132*(y6[i,j]-2) ;
   #  {-0.362519, 0.298691, 0.287065, -0.920785, 0.190917, 0.219132};
