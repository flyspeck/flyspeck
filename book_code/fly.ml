#use "hol.ml";;

(* My customization *)

load_path :=
     ["/Users/thomashales/Desktop/flyspeck_google/source/inequalities/";
      "/Users/thomashales/Desktop/flyspeck_google/source/text_formalization/"]
        @ (!load_path);;

load_path :=
     ["/Users/thomashales/Desktop/flyspeck_google/flyspeck/inequalities/";
      "/Users/thomashales/Desktop/flyspeck_google/flyspeck/text_formalization/"]
        @ (!load_path);;


needs "build.ml";;
