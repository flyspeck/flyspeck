
module type Ocaml_sml =
sig

  type expr

  type const

  type monom = const * expr

  type lcomb = monom list

  type bounds = {lo : const;
                 hi : const}

  type ineq = {name : string;
               vars : (string * bounds) list;
               rels : lcomb list}
                   
  (* Translate HOL Light term to OCaml datatype *)
  val translate : string * Term.term -> ineq

  val translate_list : (string * Term.term) list -> ineq list

  (* Print Ocaml datatype as an SML datatype *)
  val ineq_to_sml : ineq -> unit

  val ineqs_to_sml : file:string -> ineqs:ineq list -> unit

end

module Ocaml_sml (* : Ocaml_sml *) = 
struct 

  (* -------------------------------------------------------------------------- *)
  (*  Constants                                                                 *)
  (* -------------------------------------------------------------------------- *)

  type const_name = 
    | Dd_31
    | Dd_32
    | Dd_33
    | Dd_41
    | Dd_42
    | Dd_51
    | Zz_32
    | Zz_33
    | Zz_41
    | Zz_42
    | Doct
    | Pi
    | Pt
    | Ss_5
    | Sqrt2
    | Sqrt8
    | Square_2t0
    | Square_4t0
    | Tt_0
    | Tt_5
    | Two_t0
    | Xi'_gamma
    | Xiv

  let const_of_string const = match const with
    | "kepler'D31" -> Dd_31
    | "kepler'D32" -> Dd_32
    | "kepler'D33" -> Dd_33
    | "kepler'D41" -> Dd_41
    | "kepler'D42" -> Dd_42
    | "kepler'D51" -> Dd_51
    | "kepler'Z32" -> Zz_32
    | "kepler'Z33" -> Zz_33
    | "kepler'Z41" -> Zz_41
    | "kepler'Z42" -> Zz_42
    | "kepler'doct" -> Doct
    | "pi" -> Pi
    | "kepler'pt" -> Pt
    | "kepler's5" -> Ss_5
    | "kepler'sqrt2" -> Sqrt2
    | "kepler'sqrt8" -> Sqrt8
    | "kepler'square_2t0" -> Square_2t0
    | "kepler'square_4t0" -> Square_4t0
    | "kepler't0" -> Tt_0
    | "kepler't5" -> Tt_5
    | "kepler'two_t0" -> Two_t0
    | "kepler'xi'_gamma" -> Xi'_gamma
    | "kepler'xiV" -> Xiv
    | _ -> failwith ("not a constant: " ^ const)

  (* -------------------------------------------------------------------------- *)
  (*  Functions                                                                 *)
  (* -------------------------------------------------------------------------- *)

  type func_name = | One
                   | Edge
                   | Edge_sqrt
                   | Acs
                   | Anc
                   | Arclength
                   | Beta
                   | Chi_x
                   | Cos
                   | Cross_diag_x
                   | Crown
                   | Delta_x
                   | Dih_x
                   | Dih2_x
                   | Dih3_x
                   | Dihr
                   | Eta_x
                   | Gamma_x
                   | Kappa
                   | Kx
                   | Mu_flat_x
                   | Mu_flipped_x
                   | Mu_upright_x
                   | Nu_gamma_x
                   | Nu_x
                   | Octa_x
                   | Octavor0_x
                   | Octavor_analytic_x
                   | Overlap_f
                   | Quo_x
                   | Rad2_x
                   | Q_0_x
                   | Sigma1_qrtet_x
                   | Sigma32_qrtet_x
                   | Sigma_qrtet_x
                   | Sigmahat_x
                   | Sol_x
                   | Taua_x
                   | Tauc0_x
                   | Tauvt_x
                   | Tau_0_x
                   | Tau_analytic_x
                   | Tau_sigma_x
                   | Tauhat_x
                   | Tauhatpi_x
                   | Taumu_flat_x
                   | Taunu_x
                   | U_x
                   | V0x
                   | V1x
                   | Vora_x
                   | Vorc0_x
                   | Vorc_x
                   | Vor_0_x
                   | Vor_0_x_flipped
                   | Vor_analytic_x
                   | Vor_analytic_x_flipped
                   | Vort_x

  let func_of_string func = match func with
    | "sqrt" -> Edge_sqrt
    | "acs" -> Acs
    | "cos" -> Cos
    | "kepler'anc" -> Anc
    | "kepler'arclength" -> Arclength
    | "kepler'beta" -> Beta
    | "kepler'chi_x" -> Chi_x
    | "kepler'cross_diag_x" -> Cross_diag_x
    | "kepler'crown" -> Crown
    | "kepler'delta_x" -> Delta_x
    | "kepler'dih2_x" -> Dih2_x
    | "kepler'dih3_x" -> Dih3_x
    | "kepler'dihR" -> Dihr
    | "kepler'dih_x" -> Dih_x
    | "kepler'eta_x" -> Eta_x
    | "kepler'gamma_x" -> Gamma_x
    | "kepler'kappa" -> Kappa
    | "kepler'KX" -> Kx
    | "kepler'mu_flat_x" -> Mu_flat_x
    | "kepler'mu_flipped_x" -> Mu_flipped_x
    | "kepler'mu_upright_x" -> Mu_upright_x
    | "kepler'nu_gamma_x" -> Nu_gamma_x
    | "kepler'nu_x" -> Nu_x
    | "kepler'octa_x" -> Octa_x
    | "kepler'octavor0_x" -> Octavor0_x
    | "kepler'octavor_analytic_x" -> Octavor_analytic_x
    | "kepler'overlap_f" -> Overlap_f
    | "kepler'quo_x" -> Quo_x
    | "kepler'rad2_x" -> Rad2_x
    | "kepler'sigma1_qrtet_x" -> Sigma1_qrtet_x
    | "kepler'sigma32_qrtet_x" -> Sigma32_qrtet_x
    | "kepler'sigma_qrtet_x" -> Sigma_qrtet_x
    | "kepler'sigmahat_x" -> Sigmahat_x
    | "kepler'sol_x" -> Sol_x
    | "kepler'tauA_x" -> Taua_x
    | "kepler'tauC0_x" -> Tauc0_x
    | "kepler'tauVt_x" -> Tauvt_x
    | "kepler'tau_0_x" -> Tau_0_x
    | "kepler'tau_analytic_x" -> Tau_analytic_x
    | "kepler'tau_sigma_x" -> Tau_sigma_x
    | "kepler'tauhat_x" -> Tauhat_x
    | "kepler'tauhatpi_x" -> Tauhatpi_x
    | "kepler'taumu_flat_x" -> Taumu_flat_x
    | "kepler'taunu_x" -> Taunu_x
    | "kepler'u_x" -> U_x
    | "kepler'v0x" -> V0x
    | "kepler'v1x" -> V1x
    | "kepler'vorA_x" -> Vora_x
    | "kepler'vorC0_x" -> Vorc0_x
    | "kepler'vorC_x" -> Vorc_x
    | "kepler'vor_0_x" -> Vor_0_x
    | "kepler'vor_0_x_flipped" -> Vor_0_x_flipped
    | "kepler'vor_analytic_x" -> Vor_analytic_x
    | "kepler'vor_analytic_x_flipped" -> Vor_analytic_x_flipped
    | "kepler'vort_x" -> Vort_x
    | _ -> failwith ("no such const: " ^ func) 

  (* -------------------------------------------------------------------------- *)
  (*  Terms                                                                     *)
  (* -------------------------------------------------------------------------- *)

  type const = | Decimal of int * int
               | Int of int
               | Named of const_name
               | Sqr of const
               | Sqrt of const
               | Copp of const
               | Cplus of const * const
               | Cmul of const * const
               | Cdiv of const * const

  type expr = | Const of const
              | Funcall of func_name * expr list
              | Var of string
              | Opp of expr
              | Mul of expr * expr
              | Div of expr * expr

  type monom = const * expr

  type lcomb = monom list

  type bounds = {lo : const;
                 hi : const}

  type ineq = {name : string;
               vars : (string * bounds) list;
               rels : lcomb list}

  (* -------------------------------------------------------------------------- *)
  (*  Util                                                                      *)
  (* -------------------------------------------------------------------------- *)

  let var_to_string v = fst (dest_var v)
  let dest_add t = try Some (dest_binop `(+.)` t) with _ -> None
  let dest_sub t = try Some (dest_binop `(-.)` t) with _ -> None
  let dest_mul t = try Some (dest_binop `( *. )` t) with _ -> None
  let dest_div t = try Some (dest_binop `( / )` t) with _ -> None

  (* -------------------------------------------------------------------------- *)
  (*  Translation                                                               *)
  (* -------------------------------------------------------------------------- *)

  (* `#1.35` *)
  let translate_decimal t : const option =
    try
      let dec,numden = strip_comb t in
      let num,den = match numden with [num;den] -> num,den | _ -> failwith "" in
      if dec = `DECIMAL` then
        match dest_numeral num,dest_numeral den with
            Num.Int num', Num.Int den' -> Some (Decimal (num',den'))
          | _ -> failwith ""
      else None
    with _ -> None

  (* `&5` *)  
  let translate_int t : const option = 
    try
      let amp,n = dest_comb t in
        if amp = `&.` then 
          match dest_numeral n with
              Num.Int n' -> Some (Int n')
            | _ -> None 
        else None 
    with _ -> None 

  (* `square_2t0` *)
  let translate_named t : const option =
    try
      let c,_ = dest_const t in
        Some (Named (const_of_string c))
    with _ -> None

  let rec translate_const t : const option =  
    match translate_decimal t with
        Some _ as c -> c
      | None ->
    match translate_int t with
        Some _ as c -> c
      | None ->
    match translate_named t with
        Some _ as c -> c
      | None ->
    match translate_sqr t with
        Some _ as c -> c
      | None ->
    match translate_sqrt t with
        Some _ as c -> c
      | None ->
    match translate_copp t with
        Some _ as c -> c
      | None ->
    match translate_cplus t with
        Some _ as c -> c
      | None ->
    match translate_cmul t with
        Some _ as c -> c
      | None ->
    match translate_cdiv t with
        Some _ as c -> c
      | None -> None 

  and translate_unop p con t : const option = 
    try
      let p',c = dest_comb t in
        if p = p' then
        match translate_const c with
            Some c -> Some (con c)
          | None -> None 
        else
          None
    with _ -> None 

  and translate_binop p con t : const option = 
    try
      let l,r = dest_binop p t in
      match translate_const l,translate_const r with
          Some l', Some r' -> Some (con(l',r'))
        | _ -> None 
    with _ -> None 

  and translate_sqr t = translate_unop `square` (fun x -> Sqr x) t
  and translate_sqrt t = translate_unop `sqrt` (fun x -> Sqrt x) t
  and translate_copp t = translate_unop `(--.)` (fun x -> Copp x) t
  and translate_cplus t = translate_binop `(+.)` (fun x,y -> Cplus (x,y)) t
  and translate_cmul t = translate_binop `( *. )` (fun x,y -> Cmul (x,y)) t
  and translate_cdiv t = translate_binop `( / )` (fun x,y -> Cdiv (x,y)) t

  let translate_var t = 
    if is_var t then Some (Var (fst (dest_var t))) else None 

  let rec translate_expr t : expr option = 
    match translate_const t with
        Some c -> Some (Const c)
      | None ->
    match translate_funcall t with
        Some _ as c -> c
      | None ->
    match translate_var t with
        Some _ as c -> c
      | None ->
    match translate_opp t with
        Some _ as c -> c
      | None ->
    match translate_mul t with
        Some _ as c -> c
      | None ->
    match translate_div t with
        Some _ as c -> c
      | None -> failwith "translate_expr"

  and translate_funcall t =
    try
      let f,xs = strip_comb t in
      let func_str,_ = dest_const f in
      let func = func_of_string func_str in
      let xs' = map (fun x -> match translate_expr x with Some e -> e | None -> failwith "") xs in
        Some (Funcall(func,xs'))
    with _ -> None 

  and translate_unop p con t : expr option = 
    try
      let p',c = dest_comb t in
        if p = p' then
        match translate_expr c with
            Some c -> Some (con c)
          | None -> None 
        else
          None
    with _ -> None 

  and translate_binop p con t : expr option = 
    try
      let l,r = dest_binop p t in
      match translate_expr l,translate_expr r with
          Some l', Some r' -> Some (con(l',r'))
        | _ -> None 
    with _ -> None 

  and translate_opp t = translate_unop `(--.)` (fun x -> Opp x) t
  and translate_mul t = translate_binop `( *. )` (fun x,y -> Mul (x,y)) t
  and translate_div t = translate_binop `( / )` (fun x,y -> Div (x,y)) t

  let translate_monom t : monom option = 
    match translate_const t with
        Some x -> Some (x,Funcall(One,[]))
      | None -> 
    match dest_mul t with
        Some (c,e) -> 
          (match translate_const c, translate_expr e with
               Some c', Some e' -> Some (c',e')
             | _ -> match translate_expr t with
                   Some e -> Some (Int 1,e)
                 | None -> None)
      | None ->
          match translate_expr t with
              Some e -> Some (Int 1,e)
            | None -> None;;

  let rec translate_lcomb t = 
    match dest_add t with
        Some (l,r) ->
          (match translate_lcomb l ,translate_lcomb r with
              Some l', Some r' -> Some (l' @ r')
             | _ -> None)
      | None -> 
          match translate_monom t with
              Some m -> Some [m]
            | None -> None

  let translate_rel t =
    try
      let lcomb,zero = dest_binop `(<.)` t in
      let _ = if zero <> `(&0)` then failwith "not zero" else () in
        translate_lcomb lcomb 
    with _ -> failwith "translate_rel"

  let translate_ineq t =
    try
      let _,body = strip_forall t in
      let ineq_tm,bounds_rel = strip_comb body in
      let bounds,rel = match bounds_rel with [bounds;rel] -> bounds,rel | _ -> failwith "" in
      let ineqs = disjuncts rel in
      let map_fn q = match translate_rel q with Some l -> l | None -> failwith "" in
      let ineqs = map map_fn ineqs in
      let dest_trip xyz =
        let x,yz = dest_pair xyz in
        let x = match translate_const x with Some x -> x | None -> failwith "" in
        let y,z = dest_pair yz in
        let y,_ = dest_var y in
        let z = match translate_const z with Some x -> x | None -> failwith "" in     
          y,{lo = x; hi = z} in
      let bounds' = map dest_trip (dest_list bounds) in
        (bounds',ineqs)
    with _ -> failwith "translate_ineq"

  (* 
     put the hales inequalities in a normal form 

     !x_1 ... x_n. ineq [lower_1,x_1,upper_1;
                         ...;
                         lower_n,x_n,upper_n]
                        c_1_1 f_1 + ... + c_1_m f_m < &0 \/
                        ... \/
                        c_k_1 f_k + ... + c_k_m f_m < &0
   *)

  let normalize =
    let thms = [
                 REAL_ARITH `x * (y + z) = x * y + x * z`;
                 REAL_ARITH `(x +. y) * z = z * x + z * y`;
                 REAL_ARITH `x * -- y = -- x * y`;
                 REAL_ARITH `(x -. y) = x + (-- y)`;
                 REAL_ARITH `(x + y) + z = x + y + z`;
                 REAL_ARITH `--. (x * y) = (--. x) * y`;
                 REAL_ARITH `-- #0.0 = &0`;
                 REAL_ARITH `x + (&0) = x`;
                 REAL_ARITH `--. (x + y) = (--. x) + (-- y)`;
                 REAL_ARITH `--. (-- x) = x`;
                 REAL_ARITH `!f:real->real->real->real->real->real->real. (-- (f x1 x2 x3 x4 x5 x6)) = (-- (&1) *. (f x1 x2 x3 x4 x5 x6))`;
                 MESON [] `(a \/ (b \/ c)) = (a \/ b \/ c)`;
                 pi_prime_tau;
                 pi_prime_sigma;
                 LET_DEF;
                 LET_END_DEF;
               ] in
    let once_thms = [
                      REAL_ARITH `!x y z:real. (x < y) = x - y < &0`;
                      REAL_ARITH `!x y z:real. (x > y) = y - x < &0`;
                    ] in
      fun x -> 
        snd (dest_eq (concl (
                              (DEPTH_CONV BETA_CONV THENC
                               ONCE_REWRITE_CONV once_thms THENC
                               REWRITE_CONV thms THENC
                               NUM_REDUCE_CONV) x)))

  let translate (name,q) =
    let dummy = {name = "dummy";
                 vars = [];
                 rels = []} in
    if mem name ignore then
      begin
        print_endline ("ignoring ineq: " ^ name);
        dummy
      end
    else
      let _ = print_endline ("translating ineq: " ^ name) in
      let bounds,rels = translate_ineq (normalize q) in
        {name = name;
         vars = bounds;
         rels = rels}

  let translate_list ineqs = map translate ineqs

  open Format

  let pp_bound (v, {lo=lo;hi=hi}) = 
    

  let ineq_to_sml q = 
    begin
      print_cut();
      open_hbox();
      print_string "{";
      open_vbox 0;
       print_string "name = \"";
       print_string q.name;
       print_string "\",";
       print_cut();
       print_string "kind = general,";       
       print_cut();
       print_string "bounds =";
       print_cut();
       close_box();
      close_box();
    end

  ineq_to_sml q

  let ineqs_to_sml ~file ~ineqs = ()

end

(* 

#use "../../kepler/notes/holl/definitions_kepler.ml";;
#use "Jordan/parse_ext_override_interface.ml";;
unambiguous_interface();;
#use "../../kepler/notes/holl/kep_inequalities.ml";;
#use "../../kepler/notes/holl/ineq_names.ml";;
#use "../../kepler/notes/holl/ocaml_to_sml.ml";;

module Sml = Ocaml_sml
let ocaml_ineqs = Sml.translate_list ineqs


let q = hd ocaml_ineqs





   let t = Sml.normalize J_586706757;;
   Sml.translate_ineq t

open Sml
   #trace Sml.translate_const;;
   #trace Sml.translate_cdiv;;
   #trace Sml.translate_expr;;
   #trace Sml.translate_funcall;;
   #trace Sml.translate_div;;
   #trace Sml.translate_monom;;
   #trace Sml.translate_lcomb;;
   #trace Sml.translate_rel;;
   #trace Sml.translate_ineq;;
   #trace Sml.translate;;

   #untrace_all;;

   let x = I_572068135
   translate_ineq ineq

   translate_ineq I_867513567_13
   let t = `tau_sigma_x x1 x2 x3 x4 x5 x6 -. #0.2529 *. dih_x x1 x2 x3 x4 x5 x6 >.
   --. #0.3442`

 *) 
