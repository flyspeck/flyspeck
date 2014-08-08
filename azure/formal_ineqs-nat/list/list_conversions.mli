open Hol_core
open Num
    val eval_hd : term -> thm
    val hd_conv : term -> thm
    val eval_el : term -> term -> thm
    val el_conv : term -> thm
    val fst_conv : term -> thm
    val snd_conv : term -> thm
    val eval_length : term -> thm
    val length_conv : term -> thm
    val eval_zip : term -> term -> thm
    val all_conv_univ : (term -> thm) -> term -> thm
    val all2_conv_univ : (term -> thm) -> term -> thm
    val eval_mem_univ : (term -> thm) -> term -> term -> thm
    val mem_conv_univ : (term -> thm) -> term -> thm
    val filter_conv_univ : (term -> thm) -> term -> thm
    val map_conv_univ : (term -> thm) -> term -> thm
    val get_all : thm -> thm list
    val select_all : thm -> int list -> thm list
    val set_of_list_conv : term -> thm
