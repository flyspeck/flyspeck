let print_joe tm = 
  let fmt = std_formatter in
  let hop,args = strip_comb tm in
  let s = name_of hop
  and ty = string_of_type (type_of hop) in
  if is_var hop & args = [] then
    (open_tag ty;
	      pp_print_string fmt s;
	      close_tag())
else if is_abs hop & args = [] then
(
 open_tag "abs";
	  pp_print_term fmt tm;
close_tag())
else fail();;

let show_joe,hide_joe = 
  (fun () -> install_user_printer ("Show JOE", print_joe)),
  (fun () -> try delete_user_printer "Show JOE"
       with Failure _ -> failwith ("JOE not loaded"));;
