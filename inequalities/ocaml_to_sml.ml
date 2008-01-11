 
type const = Decimal of int * int
           | Sqr of const
           | Named of string

let var_to_string v = fst (dest_var v)
 
let dest_decimal x =
  try
    let dec,[num;den] = strip_comb x in
      if dec = `DECIMAL` then
        let Num.Int num' = dest_numeral num in
        let Num.Int den' = dest_numeral den in
          Some (Decimal (num',den'))
      else None
  with _ -> None

let dest_const x =
  try
    let c,_ = dest_const x in
      Some (Named c)
  with _ -> None
 
let rec const_to_const x = 
  match dest_decimal x with
      Some c -> c
    | None ->
  match dest_const x with
      Some c -> c
    | None ->
  match dest_square x with
      Some c -> c
    | None -> (print_string "can't find const for term:";
               print_term x;
               raise (Failure "const_to_const"))

and dest_square x = 
  try
    let sqr,c = dest_comb x in
      if sqr = `square` then
        Some (Sqr (const_to_const c))
      else
        None
  with _ -> None

let dest_ineq ineq =
    let vars,body = strip_forall ineq in
    let _,[bounds;rel] = strip_comb body in
    let ineqs = disjuncts rel in
    let dest_trip xyz =
      let x,yz = dest_pair xyz in
      let y,z = dest_pair yz in
        x,y,z in
    let bounds' = map dest_trip (dest_list bounds) in
      (vars,bounds',ineqs)




dest_pair



strip_comb body

let ineq = I_572068135
dest_ineq I_572068135
disj_list
