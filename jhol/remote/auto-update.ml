

let backup_stdout=Unix.dup Unix.stdout;;
let backup_stderr=Unix.dup Unix.stderr;;

let default_flag_list=[Unix.O_TRUNC;Unix.O_WRONLY;Unix.O_CREAT];;

let hollight_stdout_name=String.concat "." ["hol_light";"out"];;
let hollight_stdout=Unix.openfile hollight_stdout_name default_flag_list 420;;
let hollight_stderr_name=String.concat "." ["hol_light";"err"];;
let hollight_stderr=Unix.openfile hollight_stderr_name default_flag_list 420;;
Unix.dup2 hollight_stdout Unix.stdout;;
Unix.dup2 hollight_stderr Unix.stderr;;

#use "hol.ml";;

let flyspeck_rev=Sys.getenv "FLYSPECK_REV";;

let flyspeck_stdout_name=String.concat "." [(flyspeck_rev);"out"];;
let flyspeck_stdout=Unix.openfile flyspeck_stdout_name default_flag_list 420;;
let flyspeck_stderr_name=String.concat "." [(flyspeck_rev);"err"];;
let flyspeck_stderr=Unix.openfile flyspeck_stderr_name default_flag_list 420;;

Unix.dup2 flyspeck_stdout Unix.stdout;;
Unix.dup2 flyspeck_stderr Unix.stderr;;
Unix.close hollight_stdout;;
Unix.close hollight_stderr;;
#use "strictbuild.hl";;
Unix.dup2 backup_stdout Unix.stdout;;
Unix.dup2 backup_stderr Unix.stderr;;
Unix.close backup_stdout;;
Unix.close backup_stderr;;
Unix.close flyspeck_stdout;;
Unix.close flyspeck_stderr;;


let checkpoint_name=String.concat "." [flyspeck_rev;"cr"];;
let ocampl_pid=string_of_int(Unix.getpid());;
Sys.command(String.concat " " ["cr_checkpoint -f";checkpoint_name;"--term";ocampl_pid;"&"]);;