(* Reusable ML-level tactics for valid_state_rel proofs.
   Loaded by both execEquivParamHelpers and execEquivParamProofs. *)

structure execEquivParamLib :> sig
  val vsr_reconstruct_R_ok : Thm.thm
  val vsr_reconstruct_R_term : Thm.thm
  val vsr_R_ok_R_term_thm : Thm.thm
  val vsr_irule : Thm.thm -> Abbrev.tactic
  val vsr_reconstruct_R_ok_tac : Term.term Lib.frag list -> Term.term Lib.frag list -> Abbrev.tactic
  val vsr_reconstruct_R_term_tac : Term.term Lib.frag list -> Term.term Lib.frag list -> Abbrev.tactic
  val vsr_terminal_tac : unit -> Abbrev.tactic
  val vsr_field_update_proof : unit -> Abbrev.tactic
  val vsr_field_update_R_term_proof : unit -> Abbrev.tactic
end =
struct

open HolKernel boolLib bossLib
open execEquivParamDefsTheory venomStateTheory

(* Extract reconstruction conditions from valid_state_rel at ML level *)
val vsr_conjs = SPEC_ALL valid_state_rel_def |> EQ_IMP_RULE |> fst
                |> UNDISCH |> CONJUNCTS
val vsr_reconstruct_R_ok = List.nth(vsr_conjs, 9) |> DISCH_ALL |> GEN_ALL
val vsr_reconstruct_R_term = List.nth(vsr_conjs, 10) |> DISCH_ALL |> GEN_ALL
val vsr_R_ok_R_term_thm = List.nth(vsr_conjs, 6) |> DISCH_ALL |> GEN_ALL

(* Extract field-equality facts for use in tactics.  These are forward
   derivations from valid_state_rel_def rather than load-time tactic proofs,
   so loading this library does not require a current theory. *)
val vsr_R_ok_fields_thm = List.nth(vsr_conjs, 0) |> DISCH_ALL |> GEN_ALL
val vsr_R_term_fields_thm = List.nth(vsr_conjs, 1) |> DISCH_ALL |> GEN_ALL

(* irule that handles the ∃R_term / ∃R_ok from valid_state_rel *)
fun vsr_irule thm =
  first_assum (fn asm =>
    if can (match_term ``valid_state_rel R_ok R_term``) (concl asm)
    then let val spec = SPEC_ALL thm
             val split = CONV_RULE (REWR_CONV (GSYM AND_IMP_INTRO)) spec
                         handle HOL_ERR _ => spec
             val matched = MATCH_MP split asm
         in irule matched end
    else NO_TAC)

fun vsr_reconstruct_R_ok_tac s1q s2q =
  drule_then irule vsr_reconstruct_R_ok >>
  imp_res_tac vsr_R_ok_fields_thm >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  qexistsl_tac [s1q, s2q] >> simp[]

fun vsr_reconstruct_R_term_tac s1q s2q =
  drule_then irule vsr_reconstruct_R_term >>
  imp_res_tac vsr_R_term_fields_thm >>
  simp[write_memory_with_expansion_def, LET_THM] >>
  qexistsl_tac [s1q, s2q] >> simp[]

(* Terminal reconstruction: R_ok s1 s2 ⟹ R_term (f s1) (f s2)
   Used for RETURN, REVERT, ASSERT, SELFDESTRUCT, INVALID, COPY opcodes
   after CASE_TAC reduces the goal to a terminal state. *)
fun vsr_terminal_tac () =
  imp_res_tac vsr_R_ok_R_term_thm >>
  vsr_reconstruct_R_term_tac `s1` `s2`

fun vsr_field_update_proof () =
  rpt strip_tac >> vsr_reconstruct_R_ok_tac `s1` `s2`

fun vsr_field_update_R_term_proof () =
  rpt strip_tac >> vsr_reconstruct_R_term_tac `s1` `s2`

end
