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

(* Generate per-opcode CONDITIONAL reduction of step_inst_base.
   Result: inst.inst_opcode = OPC ==> step_inst_base inst s = exec_xxx ... *)
fun mk_cond_step_base_thm opc_tm =
  let
    val inst_var = mk_var("inst", ``:instruction``)
    val s_var = mk_var("s", ``:venom_state``)
    (* Build: inst.inst_opcode = OPC ==> (inst with inst_opcode updated_by (\_.OPC)) = inst *)
    val opc_eq = mk_eq(mk_comb(``instruction_inst_opcode``, inst_var), opc_tm)
    val update_eq = mk_eq(
      mk_comb(mk_comb(``instruction_inst_opcode_fupd``,
                       mk_abs(mk_var("_", ``:opcode``), opc_tm)), inst_var),
      inst_var)
    val identity = prove(mk_imp(opc_eq, update_eq),
                         rw[instruction_component_equality])
    (* Build unconditional: step_inst_base (inst with inst_opcode := OPC) s = ... *)
    val inst_tm = mk_comb(
      mk_comb(``instruction_inst_opcode_fupd``,
              mk_abs(mk_var("_", ``:opcode``), opc_tm)),
      inst_var)
    val lhs = list_mk_comb(``step_inst_base``, [inst_tm, s_var])
    val unconditional = SIMP_CONV (srw_ss()) [step_inst_base_def] lhs
    (* Compose: replace (inst with inst_opcode := OPC) with inst under hypothesis *)
    val conditional = REWRITE_RULE [UNDISCH identity] unconditional
  in DISCH_ALL conditional end

val opc_constructors = TypeBase.constructors_of ``:opcode``
val step_base_reduces = map mk_cond_step_base_thm opc_constructors

(* Tactic: rewrite step_inst_base using assumptions for the opcode.
   After Cases_on `inst.inst_opcode`, each goal has inst.inst_opcode = OPC
   as an assumption. ASM_REWRITE_TAC fires the conditional rewrites. *)
val STEP_BASE_REDUCE_TAC =
  ONCE_ASM_REWRITE_TAC step_base_reduces

end
