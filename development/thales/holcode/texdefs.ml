(* Correspondence LaTeX definitions and HOL Light *)

let hol_tex_assoc = ref [];; 

let add_def x = (hol_tex := x::!hol_tex);;

(* ML identifier, HOL constant, LaTeX source *)

add_def ("cos",`cos`,"cos");;
add_
