(*
 * Execution Equivalence Proofs
 *
 * Proves that step_inst / run_block preserve state_equiv / result_equiv.
 * All theorems parameterized by variable exception set (vars).
 *
 * Internal proofs — consumers use props/execEquivPropsScript.sml
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_result_equiv  : Instruction step preserves result_equiv
 *   - run_block_state_equiv   : Block execution preserves state_equiv (OK case)
 *   - run_block_result_equiv  : Block execution preserves result_equiv (all cases)
 *)

Theory execEquivProofs
Ancestors
  stateEquivProofs stateEquiv venomExecSemantics venomState venomInst
Libs
  rich_listTheory finite_mapTheory

(* ==========================================================================
   exec_* Category Helpers
   ========================================================================== *)

Triviality exec_pure1_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure1 f inst s1) (exec_pure1 f inst s2)
Proof
  rw[exec_pure1_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_pure2_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure2 f inst s1) (exec_pure2 f inst s2)
Proof
  rw[exec_pure2_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_pure3_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure3 f inst s1) (exec_pure3 f inst s2)
Proof
  rw[exec_pure3_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_read0_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\ f s1 = f s2 ==>
    result_equiv vars (exec_read0 f inst s1) (exec_read0 f inst s2)
Proof
  rw[exec_read0_def] >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_read1_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!v. f v s1 = f v s2) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_read1 f inst s1) (exec_read1 f inst s2)
Proof
  rw[exec_read1_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt (CASE_TAC >> gvs[result_equiv_def]) >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_write2_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!v1 v2. state_equiv vars (f v1 v2 s1) (f v1 v2 s2)) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_write2 f inst s1) (exec_write2 f inst s2)
Proof
  rw[exec_write2_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt (CASE_TAC >> gvs[result_equiv_def])
QED

(* ==========================================================================
   step_inst: Per-category dispatch helpers
   Each handles a group of opcodes at the step_inst level.
   ========================================================================== *)

(* Opcodes that use exec_pure2 *)
Triviality step_inst_pure2_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode
      [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp;
       AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND;
       EQ; LT; GT; SLT; SGT; GEP] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_pure2_result_equiv >> simp[]
QED

(* Opcodes that use exec_pure1 *)
Triviality step_inst_pure1_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [NOT; ISZERO] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_pure1_result_equiv >> simp[]
QED

(* Opcodes that use exec_pure3 *)
Triviality step_inst_pure3_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [ADDMOD; MULMOD] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_pure3_result_equiv >> simp[]
QED

(* Opcodes that use exec_read0 — no operands, reads from state *)
Triviality step_inst_read0_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    MEM inst.inst_opcode
      [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE;
       CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO;
       GASLIMIT; BASEFEE; BLOBBASEFEE; SELFBALANCE;
       CALLDATASIZE; RETURNDATASIZE; MSIZE; CODESIZE] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_read0_result_equiv >> simp[] >>
  fs[state_equiv_def, execution_equiv_def]
QED

(* Opcodes that use exec_read1 — one operand, reads from state *)
Triviality step_inst_read1_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode
      [MLOAD; SLOAD; TLOAD; BLOCKHASH; BALANCE; CALLDATALOAD;
       EXTCODESIZE; BLOBHASH; ILOAD; DLOAD] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_read1_result_equiv >> simp[] >> rw[] >>
  gvs[mload_def, sload_def, tload_def,
      state_equiv_def, execution_equiv_def]
QED

(* EXTCODEHASH: read1 with if-then-else body *)
Triviality step_inst_extcodehash_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = EXTCODEHASH ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_read1_result_equiv >> simp[] >> rw[] >>
  gvs[state_equiv_def, execution_equiv_def]
QED

(* Opcodes that use exec_write2 — two operands, writes state *)
Triviality step_inst_write2_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [MSTORE; SSTORE; TSTORE] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  irule exec_write2_result_equiv >> simp[] >> rw[] >>
  FIRST [irule mstore_preserves, irule sstore_preserves,
         irule tstore_preserves] >> simp[]
QED

(* Terminators: STOP, RETURN, REVERT, SINK *)
Triviality step_inst_terminator_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    MEM inst.inst_opcode [STOP; RETURN; REVERT; SINK] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def, result_equiv_def,
               halt_state_def, revert_state_def,
               execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Control flow: JMP, JNZ *)
Triviality step_inst_control_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [JMP; JNZ] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule jump_to_preserves >> simp[]
QED

(* DJMP: dynamic jump uses selector to index into label list *)
Triviality step_inst_djmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = DJMP ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule jump_to_preserves >> simp[]
QED

(* Helper: resolve_phi result is a member of the operand list *)
Triviality resolve_phi_MEM:
  !prev_bb ops op. resolve_phi prev_bb ops = SOME op ==> MEM op ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >> rw[] >> metis_tac[]
QED

(* SSA: PHI, ASSIGN, NOP *)
Triviality step_inst_ssa_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [PHI; ASSIGN; NOP] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_prev_bb = s2.vs_prev_bb` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  TRY (irule update_var_preserves >> simp[] >> NO_TAC) >>
  TRY (simp[state_equiv_refl] >> NO_TAC) >>
  (* PHI: resolved operand must be in inst_operands *)
  imp_res_tac resolve_phi_MEM >>
  rename1 `resolve_phi _ _ = SOME phi_op` >>
  `eval_operand phi_op s1 = eval_operand phi_op s2` by (
    first_x_assum irule >> rw[] >> metis_tac[]) >>
  gvs[] >> irule update_var_preserves >> simp[]
QED

(* Assertions: ASSERT, ASSERT_UNREACHABLE *)
Triviality step_inst_assert_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt CASE_TAC >> gvs[result_equiv_def,
    revert_state_def, halt_state_def,
    execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality eval_operands_equiv:
  !vars ops s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> rw[eval_operands_def] >>
  `eval_operand h s1 = eval_operand h s2` by (
    irule eval_operand_equiv >> simp[] >> metis_tac[]) >>
  `eval_operands ops s1 = eval_operands ops s2` by (
    first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[]
QED

(* Hash: SHA3 *)
Triviality step_inst_sha3_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = SHA3 ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_memory = s2.vs_memory` by fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

(* MCOPY: memory-to-memory copy, 3 operands *)
Triviality step_inst_mcopy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = MCOPY ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_memory = s2.vs_memory` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, mcopy_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* ISTORE: writes to vs_immutables *)
Triviality step_inst_istore_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = ISTORE ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_immutables = s2.vs_immutables` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def,
    state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* DLOADBYTES/CODECOPY: copy from data section/code to memory, 3 operands *)
Triviality step_inst_data_copy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [DLOADBYTES; CODECOPY] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_data_section = s2.vs_data_section /\
   s1.vs_code = s2.vs_code` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* EXTCODECOPY: copy external code to memory, 4 operands *)
Triviality step_inst_extcodecopy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = EXTCODECOPY ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_accounts = s2.vs_accounts` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* OFFSET: label address + operand offset *)
Triviality step_inst_offset_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = OFFSET ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_label_offsets = s2.vs_label_offsets` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

(* LOG: appends event to vs_logs.
   Prove all operand evals are equal, then case analysis collapses. *)
Triviality step_inst_log_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = LOG ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  `s1.vs_memory = s2.vs_memory /\
   s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_logs = s2.vs_logs` by
    fs[state_equiv_def, execution_equiv_def] >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> Cases_on `op` >> simp[eval_operand_def] >>
    fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def] >>
  Cases_on `h` >> simp[result_equiv_def] >>
  rename1 `Lit tc :: rest` >>
  `!op. MEM op rest ==> eval_operand op s1 = eval_operand op s2`
    by (rw[] >> first_x_assum irule >> simp[]) >>
  Cases_on `LENGTH rest = w2n tc + 2` >> simp[result_equiv_def] >>
  `eval_operand (EL (w2n tc) rest) s1 =
   eval_operand (EL (w2n tc) rest) s2`
    by (first_x_assum irule >> irule EL_MEM >> simp[]) >>
  `eval_operand (EL (w2n tc + 1) rest) s1 =
   eval_operand (EL (w2n tc + 1) rest) s2`
    by (first_x_assum irule >> irule EL_MEM >> simp[]) >>
  sg `eval_operands (TAKE (w2n tc) rest) s1 =
      eval_operands (TAKE (w2n tc) rest) s2`
  >- (qsuff_tac `!ops. (!op. MEM op ops ==>
        eval_operand op s1 = eval_operand op s2) ==>
        eval_operands ops s1 = eval_operands ops s2`
      >- (disch_then irule >> rw[] >> first_x_assum irule >>
          imp_res_tac MEM_TAKE >> simp[])
      >> Induct >> rw[eval_operands_def]) >>
  simp[] >>
  rpt CASE_TAC >> gvs[result_equiv_def, state_equiv_def,
    execution_equiv_def, lookup_var_def]
QED

(* SELFDESTRUCT: transfers balance, halts *)
Triviality step_inst_selfdestruct_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = SELFDESTRUCT ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_accounts = s2.vs_accounts /\
   s1.vs_call_ctx = s2.vs_call_ctx` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, halt_state_def,
    execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* INVALID: always reverts *)
Triviality step_inst_invalid_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = INVALID ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def, result_equiv_def,
               halt_state_def, execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Copy: CALLDATACOPY, RETURNDATACOPY *)
Triviality step_inst_copy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [CALLDATACOPY; RETURNDATACOPY] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_memory = s2.vs_memory /\
   s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_returndata = s2.vs_returndata` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >>
  gvs[result_equiv_def, revert_state_def, halt_state_def,
      execution_equiv_def, lookup_var_def] >>
  TRY (fs[state_equiv_def, execution_equiv_def, lookup_var_def] >> NO_TAC) >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* PARAM: reads from vs_params (execution_equiv) + update_var *)
Triviality step_inst_param_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = PARAM ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rw[step_inst_def] >>
  `s1.vs_params = s2.vs_params` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

(* RET: eval_operands + halt_state *)
Triviality step_inst_ret_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = RET ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rpt gen_tac >> strip_tac >> simp[step_inst_def] >>
  sg `eval_operands inst.inst_operands s1 =
      eval_operands inst.inst_operands s2`
  >- (qsuff_tac `!ops. (!op. MEM op ops ==>
        eval_operand op s1 = eval_operand op s2) ==>
        eval_operands ops s1 = eval_operands ops s2`
      >- (disch_then irule >> rpt gen_tac >> strip_tac >>
          irule eval_operand_equiv >> simp[] >>
          metis_tac[])
      >> Induct >> rw[eval_operands_def]) >>
  rpt CASE_TAC >>
  gvs[result_equiv_def, state_equiv_def, execution_equiv_def]
QED

(* External calls: state_equiv => same EVM state => same run => equiv result.
   Key: execution_equiv gives equal accounts, memory, call_ctx, tx_params,
   so make_venom_call_state/make_venom_create_state produce identical EVM states,
   and extract_venom_result produces state_equiv states. *)

(* exec_ext_call preserves equiv when states and operands match *)
Triviality exec_ext_call_equiv:
  !vars inst s1 s2 gas addr value ao as_ ro rs is_static.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_ext_call inst s1 gas addr value ao as_ ro rs is_static)
      (exec_ext_call inst s2 gas addr value ao as_ ro rs is_static)
Proof
  rw[exec_ext_call_def, LET_THM] >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_prev_hashes = s2.vs_prev_hashes`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[read_memory_def, make_venom_call_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  simp[extract_venom_result_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  simp[update_var_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, FLOOKUP_UPDATE,
       write_memory_with_expansion_def] >>
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* exec_delegatecall preserves equiv when states and operands match *)
Triviality exec_delegatecall_equiv:
  !vars inst s1 s2 gas addr ao as_ ro rs.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_delegatecall inst s1 gas addr ao as_ ro rs)
      (exec_delegatecall inst s2 gas addr ao as_ ro rs)
Proof
  rw[exec_delegatecall_def, LET_THM] >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_prev_hashes = s2.vs_prev_hashes`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[read_memory_def, make_venom_delegatecall_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  simp[extract_venom_result_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  simp[update_var_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, FLOOKUP_UPDATE,
       write_memory_with_expansion_def] >>
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* exec_create preserves equiv when states and operands match *)
Triviality exec_create_equiv:
  !vars inst s1 s2 value offset sz salt_opt.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_create inst s1 value offset sz salt_opt)
      (exec_create inst s2 value offset sz salt_opt)
Proof
  rw[exec_create_def, LET_THM] >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_prev_hashes = s2.vs_prev_hashes`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[read_memory_def, make_venom_create_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  simp[extract_venom_result_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  simp[update_var_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, FLOOKUP_UPDATE,
       write_memory_with_expansion_def] >>
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Helper: exec_alloca preserves equiv (operands are literals) *)
Triviality exec_alloca_equiv:
  !vars inst s1 s2 alloc_size alloc_id.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_alloca inst s1 alloc_size alloc_id)
      (exec_alloca inst s2 alloc_size alloc_id)
Proof
  rw[exec_alloca_def, LET_THM] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  gvs[state_equiv_def, execution_equiv_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rw[] >> fs[]
QED

(* Allocation: operands are literals so state_equiv directly gives same result *)
Triviality step_inst_alloca_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    MEM inst.inst_opcode [ALLOCA; PALLOCA; CALLOCA] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  irule exec_alloca_equiv >> simp[]
QED

Triviality step_inst_ext_call_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [CALL; STATICCALL] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `s1.vs_call_ctx = s2.vs_call_ctx`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[step_inst_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  imp_res_tac eval_operand_equiv >> gvs[] >>
  irule exec_ext_call_equiv >> simp[]
QED

Triviality step_inst_delegatecall_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = DELEGATECALL ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  imp_res_tac eval_operand_equiv >> gvs[] >>
  irule exec_delegatecall_equiv >> simp[]
QED

Triviality step_inst_create_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [CREATE; CREATE2] ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def] >>
  imp_res_tac eval_operand_equiv >> gvs[] >>
  irule exec_create_equiv >> simp[]
QED

(* ==========================================================================
   step_inst: Main theorem — dispatches to helpers
   ========================================================================== *)

Theorem step_inst_result_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst inst s1) (step_inst inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  (* Dispatch: derive MEM for the opcode's category, then use helper *)
  FIRST [
    `MEM inst.inst_opcode [ADD;SUB;MUL;Div;SDIV;Mod;SMOD;Exp;
       AND;OR;XOR;SHL;SHR;SAR;SIGNEXTEND;EQ;LT;GT;SLT;SGT;GEP]`
       by simp[] >>
      drule_all step_inst_pure2_equiv >> simp[],
    `MEM inst.inst_opcode [NOT;ISZERO]` by simp[] >>
      drule_all step_inst_pure1_equiv >> simp[],
    `MEM inst.inst_opcode [ADDMOD;MULMOD]` by simp[] >>
      drule_all step_inst_pure3_equiv >> simp[],
    `MEM inst.inst_opcode
       [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;
        COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;
        BLOBBASEFEE;SELFBALANCE;CALLDATASIZE;RETURNDATASIZE;MSIZE;
        CODESIZE]`
      by simp[] >> drule_all step_inst_read0_equiv >> simp[],
    `MEM inst.inst_opcode
       [MLOAD;SLOAD;TLOAD;BLOCKHASH;BALANCE;CALLDATALOAD;
        EXTCODESIZE;BLOBHASH;ILOAD;DLOAD]`
      by simp[] >> drule_all step_inst_read1_equiv >> simp[],
    `inst.inst_opcode = EXTCODEHASH` by simp[] >>
      drule_all step_inst_extcodehash_equiv >> simp[],
    `MEM inst.inst_opcode [MSTORE;SSTORE;TSTORE]` by simp[] >>
      drule_all step_inst_write2_equiv >> simp[],
    `MEM inst.inst_opcode [STOP;RETURN;REVERT;SINK]` by simp[] >>
      drule_all step_inst_terminator_equiv >> simp[],
    `MEM inst.inst_opcode [JMP;JNZ]` by simp[] >>
      drule_all step_inst_control_equiv >> simp[],
    `MEM inst.inst_opcode [PHI;ASSIGN;NOP]` by simp[] >>
      drule_all step_inst_ssa_equiv >> simp[],
    `MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE]` by simp[] >>
      drule_all step_inst_assert_equiv >> simp[],
    `inst.inst_opcode = SHA3` by simp[] >>
      drule_all step_inst_sha3_equiv >> simp[],
    `MEM inst.inst_opcode [CALLDATACOPY;RETURNDATACOPY]` by simp[] >>
      drule_all step_inst_copy_equiv >> simp[],
    `inst.inst_opcode = MCOPY` by simp[] >>
      drule_all step_inst_mcopy_equiv >> simp[],
    `inst.inst_opcode = INVALID` by simp[] >>
      drule_all step_inst_invalid_equiv >> simp[],
    `inst.inst_opcode = LOG` by simp[] >>
      drule_all step_inst_log_equiv >> simp[],
    `inst.inst_opcode = SELFDESTRUCT` by simp[] >>
      drule_all step_inst_selfdestruct_equiv >> simp[],
    `inst.inst_opcode = DJMP` by simp[] >>
      drule_all step_inst_djmp_equiv >> simp[],
    `inst.inst_opcode = ISTORE` by simp[] >>
      drule_all step_inst_istore_equiv >> simp[],
    `MEM inst.inst_opcode [DLOADBYTES;CODECOPY]` by simp[] >>
      drule_all step_inst_data_copy_equiv >> simp[],
    `inst.inst_opcode = EXTCODECOPY` by simp[] >>
      drule_all step_inst_extcodecopy_equiv >> simp[],
    `inst.inst_opcode = OFFSET` by simp[] >>
      drule_all step_inst_offset_equiv >> simp[],
    `inst.inst_opcode = PARAM` by simp[] >>
      drule_all step_inst_param_equiv >> simp[],
    `inst.inst_opcode = RET` by simp[] >>
      drule_all step_inst_ret_equiv >> simp[],
    `MEM inst.inst_opcode [CALL;STATICCALL]` by simp[] >>
      drule_all step_inst_ext_call_equiv >> simp[],
    `inst.inst_opcode = DELEGATECALL` by simp[] >>
      drule_all step_inst_delegatecall_equiv >> simp[],
    `MEM inst.inst_opcode [CREATE;CREATE2]` by simp[] >>
      drule_all step_inst_create_equiv >> simp[],
    `MEM inst.inst_opcode [ALLOCA;PALLOCA;CALLOCA]` by simp[] >>
      drule_all step_inst_alloca_equiv >> simp[],
    (* INVOKE: handled in module sem, falls to Error in step_inst.
       Explicit so new opcode additions cause proof failure here. *)
    `inst.inst_opcode = INVOKE` by simp[] >>
      simp[step_inst_def, result_equiv_def]
  ]
QED

(* ==========================================================================
   block_step Preserves Equivalence
   ========================================================================== *)

Triviality block_step_result_equiv:
  !vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    let (r1, t1) = block_step bb s1 in
    let (r2, t2) = block_step bb s2 in
    t1 = t2 /\ result_equiv vars r1 r2
Proof
  rw[block_step_def, LET_THM] >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  simp[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >>
  simp[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME cur_inst` >>
  `MEM cur_inst bb.bb_instructions` by (
    fs[get_instruction_def] >>
    Cases_on `s2.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[] >>
    metis_tac[listTheory.EL_MEM]) >>
  `result_equiv vars (step_inst cur_inst s1) (step_inst cur_inst s2)` by (
    irule step_inst_result_equiv >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst cur_inst s1` >> Cases_on `step_inst cur_inst s2` >>
  gvs[result_equiv_def] >>
  Cases_on `is_terminator cur_inst.inst_opcode` >>
  simp[result_equiv_def] >>
  fs[next_inst_def, state_equiv_def, execution_equiv_def] >>
  rw[] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* ==========================================================================
   run_block Preserves Equivalence
   ========================================================================== *)

(* Induction on run_block to show result_equiv is preserved.
   Requires no INVOKE instructions in block (for cross-function equiv,
   use run_function-level simulation). *)
Theorem run_block_result_equiv:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 1 run_block_ind) >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  (* Unfold both LHS and RHS *)
  simp[Once run_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >>
  gvs[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  (* No INVOKE in this block *)
  `inst.inst_opcode <> INVOKE` by
    (gvs[listTheory.EVERY_MEM, get_instruction_def] >>
     first_x_assum irule >> irule listTheory.EL_MEM >> simp[]) >>
  simp[] >> gvs[] >>
  (* Derive operand condition for this specific inst *)
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by
    (gvs[get_instruction_def] >> metis_tac[listTheory.EL_MEM]) >>
  drule_all step_inst_result_equiv >> strip_tac >>
  Cases_on `step_inst inst s1` >> Cases_on `step_inst inst s2` >>
  gvs[result_equiv_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >-
    (* Terminator: check vs_halted *)
    (`v.vs_halted = v'.vs_halted` by
       fs[state_equiv_def, execution_equiv_def] >>
     Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
     fs[state_equiv_def]) >>
  (* Non-terminator: recurse via IH *)
  first_x_assum irule >> simp[] >>
  fs[state_equiv_def, execution_equiv_def, next_inst_def] >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* Corollary: OK case gives state_equiv *)
Theorem run_block_state_equiv:
  !fuel ctx vars bb s1 s2 r1.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    run_block fuel ctx bb s1 = OK r1
  ==>
    ?r2. run_block fuel ctx bb s2 = OK r2 /\ state_equiv vars r1 r2
Proof
  rw[] >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by
    (irule run_block_result_equiv >> metis_tac[]) >>
  gvs[result_equiv_def] >>
  Cases_on `run_block fuel ctx bb s2` >> gvs[result_equiv_def]
QED
