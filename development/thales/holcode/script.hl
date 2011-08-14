(*   *)

let scriptfile = ref "";;


let outlog = ref "/Users/thomashales/Dropbox/thacklog.hl";;
let errlog = ref "/Users/thomashales/Dropbox/thackerrory.hl";;
let sleep = ref (6);;
let emsg = ref "/";;
let msg = ref ".";;
scriptfile;;

let doubleout fl s = 
      let _ =       report s in
      let _ = Parse_ineq.output_filestring fl s in
	();;

doubleout !errlog "err";;
doubleout !outlog "ok";;

let rec loop () = 
  let _ = try ( loadt (!scriptfile)) 
  with _ -> (doubleout (!errlog) (!emsg)) in
  let _ = Unix.sleep(!sleep) in
  let _ = doubleout (!outlog) (!msg) in
    loop();;


loadt (!scriptfile);;
loop();;


Sys.command("date");;

