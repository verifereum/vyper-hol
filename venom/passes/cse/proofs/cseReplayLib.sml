(* Exact opcode dispatch for executions of distinct instructions.
   Reuse the shared constructor index; never search conditional clauses. *)
structure cseReplayLib :> sig
  val STEP_INST_BASE_CONV : Thm.thm -> Conv.conv
  val selected_base_tac : Abbrev.tactic
end = struct
open HolKernel boolLib bossLib

fun STEP_INST_BASE_CONV opcode_eq =
  PART_MATCH lhs
    (MATCH_MP (stepInstBaseLib.opcode_clause (rhs (concl opcode_eq))) opcode_eq)

fun selected_base_tac (asl, goal) = let
  fun clause tm =
    SOME (STEP_INST_BASE_CONV (ASSUME tm)) handle HOL_ERR _ => NONE
  val convs = List.mapPartial clause asl
  val _ = if null convs then raise mk_HOL_ERR "cseReplayLib" "selected_base_tac" "no opcode equalities" else ()
  val conv = DEPTH_CONV (FIRST_CONV convs)
in
  (RULE_ASSUM_TAC (CONV_RULE conv) >> CONV_TAC conv) (asl, goal)
end
end
