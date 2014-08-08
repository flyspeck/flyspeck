let hol_version = 193;;
let flyspeck_version = 3560;;
let formal_ineq_version = 3658;; (* formal_ineqs version *)

let start_time = Unix.gettimeofday();;

let _ =
  if Array.length Sys.argv <> 4 then
    let str = Printf.sprintf "Usage: %s data_file first_case last_case" Sys.argv.(0) in
    print_endline str;
    exit 1
  else
    ();;

let data_file = Sys.argv.(1);;

let _ =
  if not (Sys.file_exists data_file) then
    let str = Printf.sprintf "Data file %s does not exist" data_file in
    print_endline str;
    exit 2
  else
    ();;

let first_case = int_of_string Sys.argv.(2);;
let last_case = int_of_string Sys.argv.(3);;
    
let info_print_level = 1;;
