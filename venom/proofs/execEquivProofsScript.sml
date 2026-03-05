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
  rich_listTheory

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
       EXTCODESIZE; BLOBHASH] ==>
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
               revert_state_def, execution_equiv_def, lookup_var_def] >>
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
  gvs[result_equiv_def, revert_state_def,
      execution_equiv_def, lookup_var_def] >>
  TRY (fs[state_equiv_def, execution_equiv_def, lookup_var_def] >> NO_TAC) >>
  irule write_memory_with_expansion_preserves >> simp[]
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
        EXTCODESIZE;BLOBHASH]`
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
    (* Unimplemented opcodes: wildcard gives Error *)
    simp[step_inst_def, result_equiv_def]
  ]
QED

(* ==========================================================================
   step_in_block Preserves Equivalence
   ========================================================================== *)

Triviality step_in_block_result_equiv:
  !vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    let (r1, t1) = step_in_block bb s1 in
    let (r2, t2) = step_in_block bb s2 in
    t1 = t2 /\ result_equiv vars r1 r2
Proof
  rw[step_in_block_def, LET_THM] >>
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

(* Induction on run_block to show result_equiv is preserved *)
Theorem run_block_result_equiv:
  !vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block bb s1) (run_block bb s2)
Proof
  gen_tac >>
  `!bb s1. (!inst. MEM inst bb.bb_instructions ==>
              !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
           !s2. state_equiv vars s1 s2 ==>
           result_equiv vars (run_block bb s1) (run_block bb s2)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac run_block_ind >> rw[] >>
  simp[Once run_block_def] >>
  drule_all step_in_block_result_equiv >>
  Cases_on `step_in_block bb s1` >>
  Cases_on `step_in_block bb s2` >>
  simp[LET_THM] >> strip_tac >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >> simp[] >>
  Cases_on `q` >> Cases_on `q'` >> gvs[result_equiv_def] >>
  `v.vs_halted = v'.vs_halted` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[] >-
    (simp[result_equiv_def] >> fs[state_equiv_def]) >>
  Cases_on `r` >> gvs[result_equiv_def] >>
  first_x_assum irule >> simp[] >> first_x_assum ACCEPT_TAC
QED

(* Corollary: OK case gives state_equiv *)
Theorem run_block_state_equiv:
  !vars bb s1 s2 r1.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    run_block bb s1 = OK r1
  ==>
    ?r2. run_block bb s2 = OK r2 /\ state_equiv vars r1 r2
Proof
  rw[] >>
  drule_all run_block_result_equiv >>
  simp[result_equiv_def] >>
  Cases_on `run_block bb s2` >> gvs[result_equiv_def]
QED
