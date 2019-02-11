include module type of Hol_core

val dest_goal : goal -> (string * thm) list * term
val goal_asms : goal -> (string * thm) list
val goal_concl : goal -> term
val mk_goal : (string * thm) list * term -> goal

val CHEAT_TAC : tactic
val new_axiom : term -> thm
val mk_thm : term list * term -> thm

val EXISTS_TAC : term -> tactic
val prove : term * tactic -> thm
val prove_by_refinement : term * tactic list -> thm

val flyspeck_needs : string -> unit

val load_begin : ?debug:bool -> unit -> unit
val load_end : string -> unit