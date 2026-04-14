(* venomStepPropsScript.sml
 *
 * Properties of Venom step_inst that are independent of codegen.
 * These are properties of the Venom semantics, useful across multiple proofs.
 *)

Theory venomStepProps
Ancestors
  venomExecSemantics venomState venomInst
Libs
  BasicProvers

(* ===================================================================
   Building blocks: each state-modifying helper preserves vs_halted
   =================================================================== *)

Theorem update_var_halted[simp]:
  !out v (st:venom_state). (update_var out v st).vs_halted = st.vs_halted
Proof
  rw[update_var_def]
QED

Theorem write_memory_with_expansion_halted[simp]:
  !off bytes (st:venom_state).
    (write_memory_with_expansion off bytes st).vs_halted = st.vs_halted
Proof
  rw[write_memory_with_expansion_def, LET_THM]
QED

Theorem jump_to_halted[simp]:
  !lbl (st:venom_state). (jump_to lbl st).vs_halted = st.vs_halted
Proof
  rw[jump_to_def]
QED

Theorem mstore_halted[simp]:
  !off v (st:venom_state). (mstore off v st).vs_halted = st.vs_halted
Proof
  rw[mstore_def, LET_THM]
QED

Theorem mstore8_halted[simp]:
  !off v (st:venom_state). (mstore8 off v st).vs_halted = st.vs_halted
Proof
  rw[mstore8_def, LET_THM]
QED

Theorem mcopy_halted[simp]:
  !dst src sz (st:venom_state). (mcopy dst src sz st).vs_halted = st.vs_halted
Proof
  rw[mcopy_def, LET_THM]
QED

Theorem sstore_halted[simp]:
  !key v (st:venom_state). (sstore key v st).vs_halted = st.vs_halted
Proof
  rw[sstore_def]
QED

Theorem tstore_halted[simp]:
  !key v (st:venom_state). (tstore key v st).vs_halted = st.vs_halted
Proof
  rw[tstore_def]
QED

(* ===================================================================
   Helper function OK results preserve vs_halted
   =================================================================== *)

Theorem exec_pure1_ok_halted:
  !f inst (st:venom_state) st'.
    exec_pure1 f inst st = OK st' ==> st'.vs_halted = st.vs_halted
Proof
  rw[exec_pure1_def] >> every_case_tac >> gvs[]
QED

Theorem exec_pure2_ok_halted:
  !f inst (st:venom_state) st'.
    exec_pure2 f inst st = OK st' ==> st'.vs_halted = st.vs_halted
Proof
  rw[exec_pure2_def] >> every_case_tac >> gvs[]
QED

Theorem exec_pure3_ok_halted:
  !f inst (st:venom_state) st'.
    exec_pure3 f inst st = OK st' ==> st'.vs_halted = st.vs_halted
Proof
  rw[exec_pure3_def] >> every_case_tac >> gvs[]
QED

Theorem exec_read0_ok_halted:
  !f inst (st:venom_state) st'.
    exec_read0 f inst st = OK st' ==> st'.vs_halted = st.vs_halted
Proof
  rw[exec_read0_def] >> every_case_tac >> gvs[]
QED

Theorem exec_read1_ok_halted:
  !f inst (st:venom_state) st'.
    exec_read1 f inst st = OK st' ==> st'.vs_halted = st.vs_halted
Proof
  rw[exec_read1_def] >> every_case_tac >> gvs[]
QED

(* exec_write2 is NOT generally halted-preserving — depends on f.
   Handled case-by-case in step_inst_base_ok_halted. *)

Theorem extract_venom_result_halted:
  !st out_v roff rsz run_res output (st':venom_state).
    extract_venom_result st out_v roff rsz run_res = SOME (output, st') ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[extract_venom_result_def, LET_THM] >>
  every_case_tac >> gvs[]
QED

Theorem exec_ext_call_ok_halted:
  !inst (st:venom_state) gas addr v ao as_ ro rs is_static st'.
    exec_ext_call inst st gas addr v ao as_ ro rs is_static = OK st' ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[exec_ext_call_def, LET_THM] >>
  every_case_tac >> gvs[] >>
  imp_res_tac extract_venom_result_halted >> gvs[]
QED

Theorem exec_delegatecall_ok_halted:
  !inst (st:venom_state) gas addr ao as_ ro rs st'.
    exec_delegatecall inst st gas addr ao as_ ro rs = OK st' ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[exec_delegatecall_def, LET_THM] >>
  every_case_tac >> gvs[] >>
  imp_res_tac extract_venom_result_halted >> gvs[]
QED

Theorem exec_create_ok_halted:
  !inst (st:venom_state) value offset sz salt_opt st'.
    exec_create inst st value offset sz salt_opt = OK st' ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[exec_create_def, LET_THM] >>
  every_case_tac >> gvs[] >>
  imp_res_tac extract_venom_result_halted >> gvs[]
QED

Theorem exec_alloca_ok_halted:
  !inst (st:venom_state) alloc_size st'.
    exec_alloca inst st alloc_size = OK st' ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[exec_alloca_def, LET_THM] >> every_case_tac >> gvs[]
QED

(* ===================================================================
   Main theorem: step_inst_base OK preserves vs_halted
   =================================================================== *)

Theorem step_inst_base_ok_halted:
  !inst (st:venom_state) st'.
    step_inst_base inst st = OK st' ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  TRY (imp_res_tac exec_pure1_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_pure2_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_pure3_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_read0_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_read1_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_ext_call_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_delegatecall_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_create_ok_halted >> gvs[] >> NO_TAC) >>
  TRY (imp_res_tac exec_alloca_ok_halted >> gvs[] >> NO_TAC) >>
  (* Remaining: direct OK cases — NOP, ASSERT, ASSERT_UNREACHABLE, ISTORE,
     LOG, MCOPY, CALLDATACOPY, RETURNDATACOPY, CODECOPY, EXTCODECOPY,
     DLOADBYTES, SHA3, JMP, JNZ, DJMP, PARAM, ASSIGN, PHI, OFFSET,
     and exec_write2 cases: MSTORE, SSTORE, TSTORE *)
  gvs[LET_THM, exec_write2_def, AllCaseEqs()]
QED

(* ===================================================================
   INVOKE OK preserves vs_halted
   =================================================================== *)

Theorem merge_callee_state_halted[simp]:
  !caller (callee:venom_state).
    (merge_callee_state caller callee).vs_halted = caller.vs_halted
Proof
  rw[merge_callee_state_def]
QED

Theorem foldl_update_var_halted:
  !pairs (st:venom_state).
    (FOLDL (\st' (out,v). update_var out v st') st pairs).vs_halted =
    st.vs_halted
Proof
  Induct >> rw[] >>
  Cases_on `h` >> rw[]
QED

Theorem bind_outputs_ok_halted:
  !outs vals (st:venom_state) st'.
    bind_outputs outs vals st = SOME st' ==> st'.vs_halted = st.vs_halted
Proof
  rw[bind_outputs_def] >>
  every_case_tac >> gvs[] >>
  rw[foldl_update_var_halted]
QED

(* ===================================================================
   Main result: step_inst OK preserves vs_halted
   =================================================================== *)

Theorem step_inst_ok_halted:
  !fuel ctx inst (st:venom_state) st'.
    step_inst fuel ctx inst st = OK st' ==>
    st'.vs_halted = st.vs_halted
Proof
  rw[step_inst_def] >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[]
  >- ((* INVOKE case *)
      every_case_tac >> gvs[] >>
      imp_res_tac bind_outputs_ok_halted >> gvs[])
  >> (* Non-INVOKE case *)
  imp_res_tac step_inst_base_ok_halted >> gvs[]
QED
