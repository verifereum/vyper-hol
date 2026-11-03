(* venomStepPropsScript.sml
 *
 * Properties of Venom step_inst that are independent of codegen.
 * These are properties of the Venom semantics, useful across multiple proofs.
 *
 * STATUS: Currently unused by the active codegen proof chain. This is small,
 * general Venom semantics infrastructure and may ultimately belong near the
 * shared Venom semantics/proofs rather than under codegen/proofs.
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
  rpt gen_tac >> Cases_on `inst.inst_opcode`
  >~ [`inst.inst_opcode = ADD`] >-
    (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SUB`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = MUL`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = Div`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = Mod`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SDIV`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SMOD`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = Exp`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = ADDMOD`] >- (rw[step_inst_base_def] >> drule exec_pure3_ok_halted >> simp[])
  >~ [`inst.inst_opcode = MULMOD`] >- (rw[step_inst_base_def] >> drule exec_pure3_ok_halted >> simp[])
  >~ [`inst.inst_opcode = EQ`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = LT`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = GT`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SLT`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SGT`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = ISZERO`] >- (rw[step_inst_base_def] >> drule exec_pure1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = AND`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = OR`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = XOR`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = NOT`] >- (rw[step_inst_base_def] >> drule exec_pure1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SHL`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SHR`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SAR`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SIGNEXTEND`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = BYTE`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = OFFSET`] >- (rw[step_inst_base_def] >> drule exec_pure2_ok_halted >> simp[])
  >~ [`inst.inst_opcode = MLOAD`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SLOAD`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = TLOAD`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = ILOAD`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = DLOAD`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = BLOCKHASH`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = BLOBHASH`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = BALANCE`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CALLDATALOAD`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = EXTCODESIZE`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = EXTCODEHASH`] >- (rw[step_inst_base_def] >> drule exec_read1_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CALLER`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = ADDRESS`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CALLVALUE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = GAS`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = ORIGIN`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = GASPRICE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CHAINID`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = COINBASE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = TIMESTAMP`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = NUMBER`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = PREVRANDAO`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = GASLIMIT`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = BASEFEE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = BLOBBASEFEE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = SELFBALANCE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CALLDATASIZE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = RETURNDATASIZE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = MEMTOP`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CODESIZE`] >- (rw[step_inst_base_def] >> drule exec_read0_ok_halted >> simp[])
  >~ [`inst.inst_opcode = MSTORE`] >- (rw[step_inst_base_def, exec_write2_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = MSTORE8`] >- (rw[step_inst_base_def, exec_write2_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = SSTORE`] >- (rw[step_inst_base_def, exec_write2_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = TSTORE`] >- (rw[step_inst_base_def, exec_write2_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = ISTORE`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[istore_def])
  >~ [`inst.inst_opcode = MCOPY`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = JMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = JNZ`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = DJMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = RET`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = RETFMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = DRET`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]))
  >~ [`inst.inst_opcode = RETURN`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = REVERT`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = STOP`] >- simp[step_inst_base_def]
  >~ [`inst.inst_opcode = SINK`] >- simp[step_inst_base_def]
  >~ [`inst.inst_opcode = PHI`] >- simp[step_inst_base_def]
  >~ [`inst.inst_opcode = INVALID`] >- simp[step_inst_base_def]
  >~ [`inst.inst_opcode = NOP`] >- simp[step_inst_base_def]
  >~ [`inst.inst_opcode = PARAM`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = ASSIGN`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = DALLOCA`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = GETFMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = SETFMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = INITIAL_FMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = BUMP`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = FMP_PARAM`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = RETPC_PARAM`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = ASSERT`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = ASSERT_UNREACHABLE`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = CALLDATACOPY`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = RETURNDATACOPY`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = SHA3`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = DLOADBYTES`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = CODECOPY`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = EXTCODECOPY`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = LOG`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = SELFDESTRUCT`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[])
  >~ [`inst.inst_opcode = CALL`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> drule exec_ext_call_ok_halted >> simp[])
  >~ [`inst.inst_opcode = STATICCALL`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> drule exec_ext_call_ok_halted >> simp[])
  >~ [`inst.inst_opcode = DELEGATECALL`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> drule exec_delegatecall_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CREATE`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> drule exec_create_ok_halted >> simp[])
  >~ [`inst.inst_opcode = CREATE2`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> drule exec_create_ok_halted >> simp[])
  >~ [`inst.inst_opcode = ALLOCA`] >- (rw[step_inst_base_def] >> every_case_tac >> gvs[] >> drule exec_alloca_ok_halted >> simp[]) >>
  simp[step_inst_base_def]
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
