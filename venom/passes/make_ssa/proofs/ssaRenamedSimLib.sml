(*
 * SSA Renamed Simulation Library
 *
 * Provides:
 *   step_base_reduces : thm list
 *     Per-opcode CONDITIONAL reduction theorems for step_inst_base.
 *     Each theorem has the form:
 *       inst.inst_opcode = OPC ==> step_inst_base inst s = ...
 *     where the RHS is the specific exec_* call for that opcode.
 *
 *   STEP_BASE_REDUCE_TAC : tactic
 *     Rewrites step_inst_base when inst_opcode is known in the
 *     assumptions (e.g. after Cases_on `inst.inst_opcode`).
 *)
structure ssaRenamedSimLib :> sig
  val step_base_reduces : Thm.thm list
  val STEP_BASE_REDUCE_TAC : Abbrev.tactic
end = struct

open HolKernel boolLib bossLib
open venomInstTheory venomExecSemanticsTheory
open stepInstBaseLib

val step_base_reduces =
  map (SPEC_ALL o simp_opcode_clause) (TypeBase.constructors_of ``:opcode``)

(* Tactic: rewrite step_inst_base using assumptions for the opcode.
   After Cases_on `inst.inst_opcode`, each goal has inst.inst_opcode = OPC
   as an assumption. ASM_REWRITE_TAC fires the conditional rewrites. *)
val STEP_BASE_REDUCE_TAC =
  ONCE_ASM_REWRITE_TAC step_base_reduces

end
