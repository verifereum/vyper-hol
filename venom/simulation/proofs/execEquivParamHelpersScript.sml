(*
 * Parameterized Execution Equivalence — Step Inst Helpers
 *
 * Per-opcode step_inst_base preservation proofs.
 * Depends on execEquivParamBase for core helpers.
 *)

Theory execEquivParamHelpers
Ancestors
  execEquivParamBase
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
Libs
  finite_mapTheory listTheory rich_listTheory

open execEquivParamLib

(* ==========================================================================
   ML tactics (use Base theorems which are now in scope)
   ========================================================================== *)

fun vsr_eval_ops_tac () =
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> vsr_irule vsr_eval_operand >> simp[] >> metis_tac[])

fun vsr_eval_rewrite_tac () =
  imp_res_tac vsr_R_ok_fields >> vsr_eval_ops_tac () >> simp[step_inst_base_def]

(* ==========================================================================
   step_inst_base-level helpers
   ========================================================================== *)

Theorem vsr_step_inst_pure2:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ADD;SUB;MUL;Div;SDIV;Mod;SMOD;Exp;
      AND;OR;XOR;SHL;SHR;SAR;SIGNEXTEND;BYTE;EQ;LT;GT;SLT;SGT] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_pure2 >> simp[]
QED

Theorem vsr_step_inst_pure1:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [NOT;ISZERO] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_pure1 >> simp[]
QED

Theorem vsr_step_inst_pure3:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ADDMOD;MULMOD] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_pure3 >> simp[]
QED

Theorem vsr_step_inst_read0:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode
      [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;
       COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;
       BLOBBASEFEE;SELFBALANCE;CALLDATASIZE;RETURNDATASIZE;MSIZE;
       CODESIZE] ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_read0 >> simp[] >>
  imp_res_tac vsr_R_ok_fields >> simp[]
QED

Theorem vsr_step_inst_read1:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode
      [MLOAD;SLOAD;TLOAD;BLOCKHASH;BALANCE;CALLDATALOAD;
       EXTCODESIZE;BLOBHASH;ILOAD;DLOAD] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_read1 >> simp[] >> rw[] >>
  imp_res_tac vsr_R_ok_fields >>
  gvs[mload_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem vsr_step_inst_extcodehash:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = EXTCODEHASH /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_read1 >> simp[] >> rw[] >>
  imp_res_tac vsr_R_ok_fields >> gvs[]
QED

Theorem vsr_step_inst_write2:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [MSTORE;SSTORE;TSTORE] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  vsr_irule vsr_exec_write2 >> simp[] >> rw[] >>
  FIRST [vsr_irule vsr_mstore, vsr_irule vsr_sstore, vsr_irule vsr_tstore] >>
  simp[]
QED

Theorem vsr_step_inst_terminator:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [STOP;SINK] ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def, lift_result_def] >>
  imp_res_tac vsr_terminal_R_term >> simp[]
QED

Theorem vsr_step_inst_return:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = RETURN /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def, halt_state_def, set_returndata_def]) >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_revert:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = REVERT /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def, revert_state_def, set_returndata_def]) >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_control:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [JMP;JNZ] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_jump_to >> simp[]
QED

Theorem vsr_step_inst_djmp:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = DJMP /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_jump_to >> simp[]
QED

Theorem vsr_step_inst_ssa:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [PHI;ASSIGN;NOP] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  TRY (imp_res_tac resolve_phi_MEM >> res_tac >> gvs[]) >>
  TRY (vsr_irule vsr_update_var_R_ok >> simp[] >> NO_TAC) >>
  simp[lift_result_def]
QED

Theorem vsr_step_inst_assert:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def,
    revert_state_def, halt_state_def, set_returndata_def]) >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_sha3:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = SHA3 /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_step_inst_mcopy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = MCOPY /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_mcopy >> simp[]
QED

Theorem vsr_step_inst_istore:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = ISTORE /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_immutables_R_ok >> simp[]
QED

Theorem vsr_step_inst_data_copy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [DLOADBYTES;CODECOPY] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_write_memory >> simp[]
QED

Theorem vsr_step_inst_extcodecopy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = EXTCODECOPY /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_write_memory >> simp[]
QED

Theorem vsr_step_inst_copy:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [CALLDATACOPY;RETURNDATACOPY] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def,
    revert_state_def, halt_state_def, set_returndata_def]) >>
  TRY (vsr_irule vsr_write_memory >> simp[] >> NO_TAC) >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_offset:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = OFFSET /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_step_inst_param:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = PARAM ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac vsr_R_ok_fields >> simp[step_inst_base_def] >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_update_var_R_ok >> simp[]
QED

Theorem vsr_step_inst_ret:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = RET /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac vsr_R_ok_fields >> vsr_eval_ops_tac () >>
  `eval_operands inst.inst_operands s1 =
   eval_operands inst.inst_operands s2` by (
    vsr_irule vsr_eval_operands >> metis_tac[]) >>
  simp[step_inst_base_def] >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  imp_res_tac vsr_R_ok_R_term >> simp[]
QED

Theorem vsr_step_inst_log:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = LOG /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac vsr_R_ok_fields >> vsr_eval_ops_tac () >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[lift_result_def] >>
  Cases_on `h` >> simp[lift_result_def] >>
  rename1 `Lit tc :: rest` >>
  `!op. MEM op rest ==> eval_operand op s1 = eval_operand op s2` by
    (rw[] >> first_x_assum (qspec_then `op` mp_tac) >> simp[]) >>
  IF_CASES_TAC >> simp[lift_result_def] >>
  `2 <= LENGTH rest` by simp[] >>
  `MEM (HD rest) rest` by (Cases_on `rest` >> fs[]) >>
  `MEM (EL 1 rest) rest` by (irule rich_listTheory.EL_MEM >> simp[]) >>
  `eval_operand (HD rest) s1 = eval_operand (HD rest) s2` by res_tac >>
  `eval_operand (EL 1 rest) s1 = eval_operand (EL 1 rest) s2` by res_tac >>
  `eval_operands (DROP 2 rest) s1 = eval_operands (DROP 2 rest) s2` by (
    qsuff_tac `!ops. (!op. MEM op ops ==> eval_operand op s1 = eval_operand op s2) ==>
               eval_operands ops s1 = eval_operands ops s2`
    >- (disch_then irule >> rw[] >> res_tac >> metis_tac[MEM_DROP_IMP])
    >> Induct >> rw[eval_operands_def]) >>
  simp[] >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_logs_R_ok >> simp[]
QED

val _ = export_theory()
