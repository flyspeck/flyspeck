open Native_strictbuild

(* pair *)
    val eval_pair_eq_univ : (term -> thm) * (term -> thm) -> term -> term -> thm
    val pair_eq_conv_univ : (term -> thm) * (term -> thm) -> term -> thm
    val eval_pair_eq_num : term -> term -> thm
    val pair_eq_conv_num : term -> thm
    (* HD *)
    val eval_hd : term -> thm
    val hd_conv : term -> thm
      (* EL *)
    val eval_el : term -> term -> thm
    val el_conv : term -> thm
      (* FST, SND *)
    val fst_conv : term -> thm
    val snd_conv : term -> thm
      (* LENGTH *)
    val eval_length : term -> thm
    val length_conv : term -> thm
      (* ZIP *)
    val eval_zip : term -> term -> thm
      (* ALL *)
    val all_conv_univ : (term -> thm) -> term -> thm
      (* ALL2 *)
    val all2_conv_univ : (term -> thm) -> term -> thm
      (* MEM *)
    val eval_mem_univ : (term -> thm) -> term -> term -> thm
    val mem_conv_univ : (term -> thm) -> term -> thm
      (* FILTER *)
    val filter_conv_univ : (term -> thm) -> term -> thm
      (* MAP *)
    val map_conv_univ : (term -> thm) -> term -> thm
      (* ALL theorems *)
    val get_all : thm -> thm list
    val select_all : thm -> int list -> thm list
      (* set_of_list *)
    val eval_set_of_list : term -> thm
    val set_of_list_conv : term -> thm
      (* flatten *)
    val eval_flatten : term -> thm
    val flatten_conv : term -> thm
      (* uniq *)
    val eval_uniq_univ : (term -> thm) -> term -> thm
    val uniq_conv_univ : (term -> thm) -> term -> thm
      (* undup *)
    val eval_undup_univ : (term -> thm) -> term -> thm
    val undup_conv_univ : (term -> thm) -> term -> thm
      (* cat *)
    val eval_cat : term -> term -> thm
    val cat_conv : term -> thm
      (* BUTLAST, LAST *)
    val eval_butlast_last : term -> thm * thm
      (* take, drop *)
    val eval_take : term -> term -> thm
    val eval_drop : term -> term -> thm
    val eval_take_drop : term -> term -> thm * thm
      (* rot *)
    val eval_rot : term -> term -> thm
    val eval_rot1 : term -> thm
    val eval_rotr1 : term -> thm
      (* index *)
    val eval_index_univ : (term -> thm) -> term -> term -> thm
    val index_conv_univ : (term -> thm) -> term -> thm