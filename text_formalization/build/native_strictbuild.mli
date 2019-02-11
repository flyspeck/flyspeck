include module type of Hol_core
include module type of Prove_by_refinement

val dest_goal : goal -> (string * thm) list * term
val goal_asms : goal -> (string * thm) list
val goal_concl : goal -> term
val mk_goal : (string * thm) list * term -> goal

val CHEAT_TAC : tactic
val new_axiom : term -> thm
val mk_thm : term list * term -> thm

val flyspeck_needs : string -> unit

val load_begin : unit -> unit
val load_end : string -> unit