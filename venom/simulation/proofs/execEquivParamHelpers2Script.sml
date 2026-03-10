(*
 * Parameterized Execution Equivalence — Step Inst Helpers (Part 2)
 *
 * Remaining opcodes: selfdestruct, invalid, ext_call, delegatecall, create, alloca.
 * Depends on execEquivParamBase for core helpers.
 *)

Theory execEquivParamHelpers2
Ancestors
  execEquivParamBase
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
Libs
  finite_mapTheory listTheory rich_listTheory

open execEquivParamLib

(* ML tactics (same as Helpers1) *)

fun vsr_eval_ops_tac () =
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> vsr_irule vsr_eval_operand >> simp[] >> metis_tac[])

fun vsr_eval_rewrite_tac () =
  imp_res_tac vsr_R_ok_fields >> vsr_eval_ops_tac () >> simp[step_inst_base_def]

(* ==========================================================================
   step_inst_base helpers — Part 2
   ========================================================================== *)

Theorem vsr_step_inst_selfdestruct:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = SELFDESTRUCT /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def, halt_state_def]) >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_invalid:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = INVALID ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_inst_base_def, lift_result_def, halt_state_def, set_returndata_def] >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_ext_call:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [CALL;STATICCALL] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_exec_ext_call >> simp[]
QED

Theorem vsr_step_inst_delegatecall:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = DELEGATECALL /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_exec_delegatecall >> simp[]
QED

Theorem vsr_step_inst_create:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [CREATE;CREATE2] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_exec_create >> simp[]
QED

Theorem vsr_step_inst_alloca:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ALLOCA;PALLOCA;CALLOCA] ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_exec_alloca >> simp[]
QED

val _ = export_theory()
