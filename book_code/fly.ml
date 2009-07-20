#use "hol.ml";;

(* My customization *)

load_path :=
     ["/Users/thomashales/Desktop/flyspeck_google/source/inequalities/";
      "/Users/thomashales/Desktop/flyspeck_google/source/text_formalization/"]
        @ (!load_path);;

(* I cannot find an order in which to load the files that allows me
to load vectors, analysis, transc, and convex. *)


needs "build.ml";;
