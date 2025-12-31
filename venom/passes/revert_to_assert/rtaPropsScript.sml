(*
 * Revert-to-Assert Pass: Helper Lemmas
 *
 * This theory provides helper lemmas for proving correctness of the
 * revert-to-assert transformation pass.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - step_iszero_value             : ISZERO produces bool_to_word (x = 0w)
 *   - step_assert_behavior          : ASSERT reverts on 0w, continues otherwise
 *   - step_assert_zero_reverts      : ASSERT 0w reverts
 *   - step_assert_nonzero_passes    : ASSERT nonzero continues
 *   - simple_revert_block_reverts   : Simple revert block always reverts
 *
 * STATE_EQUIV_EXCEPT PROPERTIES (in rtaDefsTheory):
 *   - state_equiv_except_refl/sym/trans, state_equiv_implies_except
 *   - update_var_same_preserves, jump_to_except_preserves, revert_state_except_preserves
 *
 * ADDITIONAL PROPERTIES (this file):
 *   - update_var_state_equiv_except_insert : update_var x creates {x}-equiv
 *   - revert_state_update_var       : revert_state insensitive to variables
 *   - revert_state_state_equiv      : revert_state preserves state_equiv
 *   - jump_to_update_var_comm       : jump_to and update_var commute
 *
 * HELPER THEOREMS:
 *   - bool_to_word_eq_0w            : bool_to_word b = 0w iff ~b
 *   - bool_to_word_neq_0w           : bool_to_word b <> 0w iff b
 *   - eval_operand_update_var_same  : eval (Var x) after update_var x
 *   - eval_operand_update_var_other : eval (Var y) after update_var x, x <> y
 *
 * ============================================================================
 *)

Theory rtaProps
Ancestors
  rtaDefs stateEquiv venomSemProps
Libs
  finite_mapTheory venomStateTheory venomSemTheory venomInstTheory venomSemPropsTheory

(* ==========================================================================
   NOTE: bool_to_word properties and basic instruction behavior lemmas
   (step_iszero_value, step_assert_behavior, step_revert_always_reverts,
   step_jnz_behavior, step_jmp_behavior) are now in venomSemPropsTheory.
   ========================================================================== *)

(* ==========================================================================
   Operand Evaluation with Variable Updates
   ========================================================================== *)

(* WHY THIS IS TRUE: update_var x v s sets vs_vars |+ (x, v), so
   lookup_var x returns SOME v. eval_operand (Var x) uses lookup_var. *)
Theorem eval_operand_update_var_same:
  !x v s. eval_operand (Var x) (update_var x v s) = SOME v
Proof
  rw[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* WHY THIS IS TRUE: update_var x doesn't affect lookup of other variables.
   FLOOKUP (fm |+ (x,v)) y = FLOOKUP fm y when x <> y. *)
Theorem eval_operand_update_var_other:
  !x y v s. x <> y ==> eval_operand (Var y) (update_var x v s) = eval_operand (Var y) s
Proof
  rw[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* WHY THIS IS TRUE: update_var only affects vs_vars, not memory, so
   evaluating a literal is unchanged. *)
Theorem eval_operand_update_var_lit:
  !x v s w. eval_operand (Lit w) (update_var x v s) = SOME w
Proof
  rw[eval_operand_def]
QED

(* ==========================================================================
   ASSERT Instruction Behavior - Special Cases
   (Base lemma step_assert_behavior is in venomSemPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: Special case of step_assert_behavior with cond = 0w. *)
Theorem step_assert_zero_reverts:
  !s cond_op id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    Revert (revert_state s)
Proof
  rw[] >> drule step_assert_behavior >> simp[]
QED

(* WHY THIS IS TRUE: Special case of step_assert_behavior with cond <> 0w. *)
Theorem step_assert_nonzero_passes:
  !s cond cond_op id.
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    OK s
Proof
  rw[] >> drule step_assert_behavior >> simp[]
QED

(* ==========================================================================
   JNZ Instruction Behavior - Special Cases
   (Base lemma step_jnz_behavior is in venomSemPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: Special case when cond <> 0w. *)
Theorem step_jnz_nonzero_jumps:
  !s cond cond_op if_nonzero if_zero id.
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    OK (jump_to if_nonzero s)
Proof
  rw[] >> drule step_jnz_behavior >> simp[]
QED

(* WHY THIS IS TRUE: Special case when cond = 0w. *)
Theorem step_jnz_zero_jumps:
  !s cond_op if_nonzero if_zero id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    OK (jump_to if_zero s)
Proof
  rw[] >> drule step_jnz_behavior >> simp[]
QED

(* ==========================================================================
   run_block Helper Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: step_in_block on a single-instruction terminator block
   returns the result of step_inst with is_term = T. *)
Theorem step_in_block_single_terminator:
  !fn bb s inst.
    bb.bb_instructions = [inst] /\
    is_terminator inst.inst_opcode ==>
    step_in_block fn bb (s with vs_inst_idx := 0) =
    (step_inst inst (s with vs_inst_idx := 0), T)
Proof
  rw[step_in_block_def, get_instruction_def] >>
  Cases_on `step_inst inst (s with vs_inst_idx := 0)` >> simp[]
QED

(* WHY THIS IS TRUE: run_block on a single-instruction REVERT block returns Revert. *)
Theorem run_block_single_revert:
  !fn bb s inst.
    bb.bb_instructions = [inst] /\
    inst.inst_opcode = REVERT ==>
    run_block fn bb (s with vs_inst_idx := 0) =
    Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rpt strip_tac >>
  simp[Once run_block_def, step_in_block_def, get_instruction_def,
       step_inst_def, is_terminator_def]
QED

(* ==========================================================================
   Simple Revert Block Execution
   (step_jmp_behavior is in venomSemPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: A block with only [revert 0 0] will:
   1. step_in_block gets instruction at idx 0 -> the REVERT instruction
   2. step_inst returns Revert (revert_state s)
   3. run_block propagates this Revert result *)
Theorem simple_revert_block_reverts:
  !fn bb s.
    is_simple_revert_block bb ==>
    run_block fn bb (s with vs_inst_idx := 0) =
    Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rw[is_simple_revert_block_def] >>
  `bb.bb_instructions = [HD bb.bb_instructions]` by (
    Cases_on `bb.bb_instructions` >> fs[]
  ) >>
  irule run_block_single_revert >>
  qexists_tac `HD bb.bb_instructions` >>
  simp[]
QED

(* ==========================================================================
   run_function at Simple Revert Block
   ========================================================================== *)

(* WHY THIS IS TRUE: A simple revert block executes its single REVERT instruction
   and produces Revert result. run_function at fuel > 0 unfolds to run_block. *)
Theorem run_function_at_simple_revert:
  !fn s fuel bb.
    is_simple_revert_block bb /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    fuel > 0 ==>
    run_function fuel fn (s with vs_inst_idx := 0) =
      Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rw[] >>
  `fuel > 0` by simp[] >>
  Cases_on `fuel` >- fs[] >>
  simp[Once run_function_def] >>
  `run_block fn bb (s with vs_inst_idx := 0) =
   Revert (revert_state (s with vs_inst_idx := 0))`
    by (irule simple_revert_block_reverts >> simp[]) >>
  simp[]
QED

(* ==========================================================================
   state_equiv_except Properties

   NOTE: Basic properties (refl, sym, trans, state_equiv_implies_except,
   update_var_same_preserves, jump_to_except_preserves, revert_state_except_preserves,
   state_equiv_except_subset) are proven in rtaDefsTheory.
   ========================================================================== *)

(* WHY THIS IS TRUE: update_var x v s adds (x, v) to vs_vars.
   For any y not in {x}, lookup_var y is unchanged.
   Other state components (memory, storage, etc.) unchanged. *)
Theorem update_var_state_equiv_except_insert:
  !x v s.
    state_equiv_except {x} s (update_var x v s)
Proof
  rw[state_equiv_except_def, execution_equiv_except_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* ==========================================================================
   revert_state Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: revert_state only sets vs_halted := T and
   vs_reverted := T. It doesn't depend on vs_vars at all.
   So revert_state (update_var x v s) and revert_state s differ only
   in vs_vars, which is unchanged by revert_state. *)
Theorem revert_state_update_var:
  !x v s.
    revert_state (update_var x v s) = (revert_state s) with vs_vars := (s.vs_vars |+ (x, v))
Proof
  rw[revert_state_def, update_var_def]
QED

(* NOTE: revert_state_state_equiv is available from stateEquivTheory *)

(* ==========================================================================
   jump_to Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: jump_to only changes control flow fields, not variables.
   So update_var commutes with jump_to (they modify disjoint state components). *)
Theorem jump_to_update_var_comm:
  !x v lbl s.
    jump_to lbl (update_var x v s) = update_var x v (jump_to lbl s)
Proof
  rw[jump_to_def, update_var_def]
QED

(* ==========================================================================
   Combined Lemmas for Transformation Patterns
   ========================================================================== *)

(* WHY THIS IS TRUE: After ISZERO on cond, output contains bool_to_word (cond = 0w).
   If cond <> 0w, then cond = 0w is false, so output = 0w.
   ASSERT on 0w reverts. This matches JNZ taking the revert branch. *)
Theorem iszero_then_assert_when_nonzero:
  !s cond cond_op out id1 id2.
    eval_operand cond_op s = SOME cond /\
    cond <> 0w ==>
    let s1 = update_var out (bool_to_word (cond = 0w)) s in
    step_inst <| inst_id := id2; inst_opcode := ASSERT;
                 inst_operands := [Var out]; inst_outputs := [] |> s1 =
    Revert (revert_state s1)
Proof
  rw[] >>
  `(cond = 0w) = F` by gvs[] >>
  pop_assum (fn th => simp[th, bool_to_word_F]) >>
  simp[eval_operand_update_var_same] >>
  irule step_assert_zero_reverts >>
  simp[eval_operand_update_var_same]
QED

(* WHY THIS IS TRUE: After ISZERO on cond, output contains bool_to_word (cond = 0w).
   If cond = 0w, then cond = 0w is true, so output = 1w <> 0w.
   ASSERT on nonzero succeeds. This matches JNZ taking the else branch. *)
Theorem iszero_then_assert_when_zero:
  !s cond cond_op out id1 id2.
    eval_operand cond_op s = SOME cond /\
    cond = 0w ==>
    let s1 = update_var out (bool_to_word (cond = 0w)) s in
    step_inst <| inst_id := id2; inst_opcode := ASSERT;
                 inst_operands := [Var out]; inst_outputs := [] |> s1 =
    OK s1
Proof
  rw[] >>
  simp[bool_to_word_T] >>
  irule step_assert_nonzero_passes >>
  simp[eval_operand_update_var_same]
QED

(* WHY THIS IS TRUE: For pattern 2, when cond <> 0w, ASSERT passes and
   we jump to then_label. JNZ would also jump to then_label (if_nonzero).
   The states are identical. *)
Theorem assert_when_nonzero_then_jmp:
  !s cond cond_op then_label id1 id2.
    eval_operand cond_op s = SOME cond /\
    cond <> 0w ==>
    step_inst <| inst_id := id1; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s = OK s
Proof
  rw[] >> drule step_assert_behavior >> simp[]
QED

(* WHY THIS IS TRUE: For pattern 2, when cond = 0w, ASSERT reverts.
   JNZ would jump to revert_label and execute revert. Both revert. *)
Theorem assert_when_zero_reverts:
  !s cond_op id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    Revert (revert_state s)
Proof
  rw[] >> drule step_assert_behavior >> simp[]
QED

(* ==========================================================================
   state_equiv_except Preservation Through Execution

   These lemmas show that if fresh vars are not used in operands, then
   state_equiv_except is preserved through step_inst, run_block, run_function.
   ========================================================================== *)

(* --------------------------------------------------------------------------
   Helper: resolve_phi returns a MEM element
   -------------------------------------------------------------------------- *)

Theorem resolve_phi_MEM:
  !prev ops val_op. resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >> gvs[AllCaseEqs()]
QED

(* --------------------------------------------------------------------------
   Category helpers for step_inst_result_equiv_except

   We split the 93 opcode cases into manageable categories:
   1. Context reads (18): CALLER, ADDRESS, CALLVALUE, GAS, ORIGIN, GASPRICE,
      CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE,
      BLOBBASEFEE, SELFBALANCE, CALLDATASIZE, RETURNDATASIZE, MSIZE
   2. 1-op loads (6): MLOAD, SLOAD, TLOAD, CALLDATALOAD, BLOCKHASH, BALANCE
   3. 2-op stores (3): MSTORE, SSTORE, TSTORE
   4. Control flow (2): JMP, JNZ
   5. SSA (3): PHI, ASSIGN, NOP
   6. Assertions (2): ASSERT, ASSERT_UNREACHABLE
   7. Termination (4): STOP, RETURN, REVERT, SINK
   8. 3-op copy (2): CALLDATACOPY, RETURNDATACOPY
   9. Hash (2): SHA3, SHA3_64
   10. Binop/Unop/Modop (22): handled by existing helpers
   11. Unimplemented: trivial (Error)
   -------------------------------------------------------------------------- *)

(*
 * Helper 1: Context read opcodes (no operands, read context field)
 * These all have shape: case outputs of [out] => OK (update_var out (context_val s) s)
 *)
Theorem step_inst_context_read_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    op IN {CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
           COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
           BLOBBASEFEE; SELFBALANCE; CALLDATASIZE; RETURNDATASIZE; MSIZE} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >> rpt CASE_TAC >> gvs[] >>
  `s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_tx_ctx = s2.vs_tx_ctx /\
   s1.vs_block_ctx = s2.vs_block_ctx /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_returndata = s2.vs_returndata /\ s1.vs_memory = s2.vs_memory`
     by fs[state_equiv_except_def, execution_equiv_except_def] >>
  gvs[] >> irule update_var_same_preserves >> simp[]
QED

(*
 * Helper 2: 1-operand load opcodes
 * These have shape: case [op1] => eval op1 => case [out] => OK (update_var out (load_fn arg s) s)
 *)
Theorem step_inst_load1_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {MLOAD; SLOAD; TLOAD; CALLDATALOAD; BLOCKHASH; BALANCE} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >> rpt CASE_TAC >> gvs[] >>
  `eval_operand h' s1 = eval_operand h' s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >> gvs[] >>
  TRY (drule_all mload_except_same >> strip_tac >> gvs[]) >>
  TRY (drule_all sload_except_same >> strip_tac >> gvs[]) >>
  TRY (drule_all tload_except_same >> strip_tac >> gvs[]) >>
  TRY (`s1.vs_call_ctx = s2.vs_call_ctx` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[]) >>
  TRY (`s1.vs_block_ctx = s2.vs_block_ctx` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[]) >>
  TRY (`s1.vs_accounts = s2.vs_accounts` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[]) >>
  irule update_var_same_preserves >> simp[]
QED

(*
 * Helper 3: 2-operand store opcodes
 * These have shape: case [op1; op2] => eval both => OK (store_fn args s)
 *)
Theorem step_inst_store2_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {MSTORE; SSTORE; TSTORE} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >> rpt CASE_TAC >> gvs[] >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >>
  `eval_operand h' s1 = eval_operand h' s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >> gvs[] >>
  TRY (irule mstore_except_preserves >> simp[]) >>
  TRY (irule sstore_except_preserves >> simp[]) >>
  TRY (irule tstore_except_preserves >> simp[])
QED

(*
 * Helper 4: Control flow opcodes
 *)
Theorem step_inst_control_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {JMP; JNZ} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >> rpt CASE_TAC >> gvs[] >>
  TRY (`eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >> gvs[]) >>
  irule jump_to_except_preserves >> simp[]
QED

(*
 * Helper 5: SSA opcodes (PHI, ASSIGN, NOP)
 *)
Theorem step_inst_ssa_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {PHI; ASSIGN; NOP} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> `s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_except_def]
  >- ((* PHI *)
    simp[step_inst_def] >>
    `!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2`
      by (rw[] >> irule eval_operand_except >> qexists_tac `fresh` >>
          simp[] >> metis_tac[]) >>
    rpt CASE_TAC >> gvs[] >>
    TRY (imp_res_tac resolve_phi_MEM >> first_x_assum drule >> simp[]) >>
    TRY (irule update_var_same_preserves >> simp[]) >>
    `eval_operand x' s1 = eval_operand x' s2`
      by (irule eval_operand_except >> qexists_tac `fresh` >>
          simp[] >> metis_tac[]) >>
    gvs[] >> irule update_var_same_preserves >> simp[])
  >- ((* ASSIGN *)
    simp[step_inst_def] >>
    `!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2`
      by (rw[] >> irule eval_operand_except >> qexists_tac `fresh` >>
          simp[] >> metis_tac[]) >>
    rpt CASE_TAC >> gvs[] >>
    TRY (irule update_var_same_preserves >> simp[]))
  >- ((* NOP *)
    simp[step_inst_def, result_equiv_except_def, state_equiv_except_refl])
QED

(*
 * Helper 6: Assertion opcodes
 *)
Theorem step_inst_assert_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {ASSERT; ASSERT_UNREACHABLE} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >> rpt CASE_TAC >> gvs[] >>
  TRY (`eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >> gvs[]) >>
  TRY (irule revert_state_from_state_except >> simp[]) >>
  TRY (irule halt_state_from_state_except >> simp[]) >>
  simp[state_equiv_except_refl]
QED

(*
 * Helper 7: Termination opcodes (no operands)
 *)
Theorem step_inst_termination_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    op IN {STOP; RETURN; REVERT; SINK} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >>
  simp[step_inst_def] >>
  TRY (irule halt_state_from_state_except >> simp[]) >>
  TRY (irule revert_state_from_state_except >> simp[])
QED

(*
 * Helper 8: 3-operand copy opcodes
 *)
Theorem step_inst_copy3_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {CALLDATACOPY; RETURNDATACOPY} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >> rpt CASE_TAC >> gvs[] >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >>
  `eval_operand h' s1 = eval_operand h' s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >>
  `eval_operand h'' s1 = eval_operand h'' s2` by
    (irule eval_operand_except >> qexists_tac `fresh` >> simp[]) >> gvs[] >>
  TRY (`s1.vs_call_ctx = s2.vs_call_ctx` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[]) >>
  TRY (`s1.vs_returndata = s2.vs_returndata` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[]) >>
  TRY (irule write_memory_with_expansion_except_preserves >> simp[]) >>
  TRY (irule revert_state_from_state_except >> simp[])
QED

(*
 * Helper 9: Hash opcodes
 *)
Theorem step_inst_hash_except:
  !fresh s1 s2 inst op.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    op IN {SHA3; SHA3_64} /\
    inst.inst_opcode = op ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> simp[step_inst_def] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2`
    by (rw[] >> irule eval_operand_except >> qexists_tac `fresh` >>
        simp[] >> metis_tac[])
  >- ((* SHA3 *)
    rpt CASE_TAC >> gvs[] >>
    `s1.vs_memory = s2.vs_memory` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[] >>
    irule update_var_same_preserves >> simp[])
  >- ((* SHA3_64 *)
    rpt CASE_TAC >> gvs[] >>
    irule update_var_same_preserves >> simp[])
QED

(*
 * Helper: If all operands in a list don't reference fresh vars, and states
 * are equiv_except, then all operands evaluate the same.
 *)
Theorem eval_operands_except:
  !fresh ops s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!op. MEM op ops ==> !x. op = Var x ==> x NOTIN fresh) ==>
    MAP (\op. eval_operand op s1) ops = MAP (\op. eval_operand op s2) ops
Proof
  Induct_on `ops` >> rw[] >- (
    irule eval_operand_except >> rw[] >>
    qexists_tac `fresh` >> rw[]
  ) >- (
    first_x_assum irule >> rw[] >>
    qexists_tac `fresh` >> rw[] >>
    first_x_assum (qspec_then `Var x` mp_tac) >> simp[]
  )
QED

(*
 * Helper: exec_binop preserves result_equiv_except when operands don't
 * reference fresh vars.
 *)
Theorem exec_binop_result_equiv_except:
  !fresh f inst s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    result_equiv_except fresh (exec_binop f inst s1) (exec_binop f inst s2)
Proof
  rw[exec_binop_def] >>
  (* Case split on operands *)
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  (* Establish operand equivalence *)
  `eval_operand h s1 = eval_operand h s2` by (
    irule eval_operand_except >> qexists_tac `fresh` >> simp[]
  ) >>
  `eval_operand h' s1 = eval_operand h' s2` by (
    irule eval_operand_except >> qexists_tac `fresh` >> simp[]
  ) >>
  rpt CASE_TAC >> gvs[] >>
  irule update_var_same_preserves >> simp[]
QED

(*
 * Helper: exec_unop preserves result_equiv_except when operands don't
 * reference fresh vars.
 *)
Theorem exec_unop_result_equiv_except:
  !fresh f inst s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    result_equiv_except fresh (exec_unop f inst s1) (exec_unop f inst s2)
Proof
  rw[exec_unop_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `eval_operand h s1 = eval_operand h s2` by (
    irule eval_operand_except >> qexists_tac `fresh` >> simp[]
  ) >>
  rpt CASE_TAC >> gvs[] >>
  irule update_var_same_preserves >> simp[]
QED

(*
 * Helper: exec_modop preserves result_equiv_except when operands don't
 * reference fresh vars.
 *)
Theorem exec_modop_result_equiv_except:
  !fresh f inst s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    result_equiv_except fresh (exec_modop f inst s1) (exec_modop f inst s2)
Proof
  rw[exec_modop_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >- (
    (* Exactly 3 operands: [h; h'; h''] = [op1; op2; op3] *)
    `eval_operand h s1 = eval_operand h s2` by (
      irule eval_operand_except >> qexists_tac `fresh` >> simp[]
    ) >>
    `eval_operand h' s1 = eval_operand h' s2` by (
      irule eval_operand_except >> qexists_tac `fresh` >> simp[]
    ) >>
    `eval_operand h'' s1 = eval_operand h'' s2` by (
      irule eval_operand_except >> qexists_tac `fresh` >> simp[]
    ) >>
    rpt CASE_TAC >> gvs[] >>
    irule update_var_same_preserves >> simp[]
  )
  (* Wrong number of operands - both sides error *)
QED

(*
 * Key lemma: step_inst preserves result_equiv_except when operands don't
 * reference fresh vars.
 *
 * WHY THIS IS TRUE: If operands evaluate the same, then:
 * - Computed values are the same (arithmetic, comparisons, etc.)
 * - Branch decisions are the same (JNZ, ASSERT)
 *)
Theorem step_inst_result_equiv_except:
  !fresh inst s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    result_equiv_except fresh (step_inst inst s1) (step_inst inst s2)
Proof
  rw[] >> Cases_on `inst.inst_opcode` >> simp[step_inst_def] >>
  TRY (irule exec_binop_result_equiv_except >> simp[]) >>
  TRY (irule exec_unop_result_equiv_except >> simp[]) >>
  TRY (irule exec_modop_result_equiv_except >> simp[]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2`
    by (rw[] >> irule eval_operand_except >> qexists_tac `fresh` >> simp[] >>
        metis_tac[]) >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_storage = s2.vs_storage /\
   s1.vs_transient = s2.vs_transient /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_accounts = s2.vs_accounts /\ s1.vs_returndata = s2.vs_returndata /\
   s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_except_def, execution_equiv_except_def] >> gvs[]
  (* MLOAD *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >> Cases_on `eval_operand h s2` >> gvs[] >>
      Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[] >>
      `mload (w2n x) s1 = mload (w2n x) s2`
        by (irule mload_except_same >> qexists_tac `fresh` >> simp[]) >>
      simp[update_var_same_preserves])
  (* MSTORE *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[] >> Cases_on `eval_operand h s2` >> gvs[] >>
      Cases_on `eval_operand h' s2` >> gvs[] >>
      irule mstore_except_preserves >> simp[])
  (* MSIZE *)
  >- (Cases_on `inst.inst_outputs` >> gvs[update_var_same_preserves] >>
      Cases_on `t` >> gvs[update_var_same_preserves])
  (* SLOAD *)
  >- (TRY (irule halt_state_from_state_except >> simp[]) >>
      TRY (irule revert_state_from_state_except >> simp[]) >>
      Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `eval_operand h s2` >> gvs[] >> Cases_on `inst.inst_outputs` >>
      gvs[] >> Cases_on `t` >> gvs[] >>
      `sload x s1 = sload x s2`
        by (irule sload_except_same >> qexists_tac `fresh` >> simp[]) >>
      simp[update_var_same_preserves])
  (* SSTORE *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[] >> Cases_on `eval_operand h s2` >> gvs[] >>
      Cases_on `eval_operand h' s2` >> gvs[] >>
      irule sstore_except_preserves >> simp[])
  (* TLOAD *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `eval_operand h s2` >> gvs[] >> Cases_on `inst.inst_outputs` >>
      gvs[] >> Cases_on `t` >> gvs[] >>
      `tload x s1 = tload x s2`
        by (irule tload_except_same >> qexists_tac `fresh` >> simp[]) >>
      simp[update_var_same_preserves])
  (* TSTORE *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `t'` >> gvs[] >> Cases_on `eval_operand h s2` >> gvs[] >>
      Cases_on `eval_operand h' s2` >> gvs[] >>
      irule tstore_except_preserves >> simp[])
  (* JMP *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `h` >> gvs[] >>
      Cases_on `t` >> gvs[] >> irule jump_to_except_preserves >> simp[])
  (* JNZ *)
  >- (rpt (CHANGED_TAC (Cases_on `inst.inst_operands` >> gvs[])) >>
      rpt CASE_TAC >> gvs[result_equiv_except_def] >>
      irule jump_to_except_preserves >> simp[])
  (* RETURN *)
  >- (irule halt_state_from_state_except >> simp[])
  (* REVERT *)
  >- (irule revert_state_from_state_except >> simp[])
  (* STOP *)
  >- (TRY (irule halt_state_from_state_except >> simp[]) >>
      TRY (irule revert_state_from_state_except >> simp[]) >>
      TRY (irule jump_to_except_preserves >> simp[]))
  (* SINK *)
  >- (irule halt_state_from_state_except >> simp[])
  (* PHI *)
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `s2.vs_prev_bb` >> gvs[] >>
      Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
      Cases_on `eval_operand x' s1` >> gvs[]
      >- (`MEM x' inst.inst_operands` by (imp_res_tac resolve_phi_MEM) >>
          `eval_operand x' s1 = eval_operand x' s2` by gvs[] >> gvs[])
      >- (`MEM x' inst.inst_operands` by (imp_res_tac resolve_phi_MEM) >>
          `eval_operand x' s1 = eval_operand x' s2` by gvs[] >>
          gvs[update_var_same_preserves]))
  (* ASSIGN *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `eval_operand h s2` >> gvs[update_var_same_preserves])
  (* CALLER through BLOBBASEFEE - context reads *)
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `eval_operand h s2` >> gvs[] >> Cases_on `inst.inst_outputs` >>
      gvs[] >> Cases_on `t` >> gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  (* CALLDATACOPY *)
  >- (rpt CASE_TAC >> gvs[result_equiv_except_def] >>
      irule write_memory_with_expansion_except_preserves >> simp[])
  (* More context reads *)
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  (* BALANCE *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `eval_operand h s2` >> gvs[] >> Cases_on `inst.inst_outputs` >>
      gvs[] >> Cases_on `t` >> gvs[update_var_same_preserves])
  (* BLOCKHASH *)
  >- (Cases_on `inst.inst_operands` >> gvs[] >> Cases_on `t` >> gvs[] >>
      Cases_on `eval_operand h s2` >> gvs[] >> Cases_on `inst.inst_outputs` >>
      gvs[] >> Cases_on `t` >> gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  (* RETURNDATACOPY *)
  >- (rpt CASE_TAC >> gvs[result_equiv_except_def] >>
      TRY (irule write_memory_with_expansion_except_preserves >> simp[]) >>
      TRY (irule revert_state_from_state_except >> simp[]))
  >- (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >>
      gvs[update_var_same_preserves])
  (* SHA3 *)
  >- (rpt CASE_TAC >> gvs[result_equiv_except_def, update_var_same_preserves])
  (* SHA3_64 *)
  >- (rpt CASE_TAC >> gvs[result_equiv_except_def, update_var_same_preserves])
  (* ASSERT *)
  >- (rpt CASE_TAC >> gvs[result_equiv_except_def] >>
      TRY (irule revert_state_from_state_except >> simp[]) >>
      TRY (simp[state_equiv_except_refl]))
  (* ASSERT_UNREACHABLE *)
  >- (rpt CASE_TAC >> gvs[result_equiv_except_def] >>
      TRY (irule halt_state_from_state_except >> simp[]) >>
      TRY (simp[state_equiv_except_refl]))
QED

(* step_in_block preserves result_equiv_except *)
Theorem step_in_block_result_equiv_except:
  !fresh fn bb s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    let (r1, t1) = step_in_block fn bb s1 in
    let (r2, t2) = step_in_block fn bb s2 in
    t1 = t2 /\ result_equiv_except fresh r1 r2
Proof
  rw[step_in_block_def, LET_THM] >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by fs[state_equiv_except_def] >> simp[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >>
  simp[result_equiv_except_def] >>
  `MEM x bb.bb_instructions` by (
    fs[get_instruction_def] >> rw[] >>
    Cases_on `s2.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[] >>
    metis_tac[listTheory.EL_MEM]) >>
  `result_equiv_except fresh (step_inst x s1) (step_inst x s2)` by (
    irule step_inst_result_equiv_except >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst x s1` >> Cases_on `step_inst x s2` >>
  gvs[result_equiv_except_def] >>
  Cases_on `is_terminator x.inst_opcode` >>
  simp[result_equiv_except_def] >>
  fs[next_inst_def, state_equiv_except_def, execution_equiv_except_def] >>
  rw[] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* run_block preserves result_equiv_except *)
Theorem run_block_result_equiv_except:
  !fresh fn bb s1 s2.
    state_equiv_except fresh s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) ==>
    result_equiv_except fresh (run_block fn bb s1) (run_block fn bb s2)
Proof
  CONV_TAC (RESORT_FORALL_CONV (fn [fresh, fn_, bb, s1, s2] =>
    [fn_, bb, s1, fresh, s2])) >>
  ho_match_mp_tac run_block_ind >> rw[] >>
  drule_all step_in_block_result_equiv_except >> simp[LET_THM] >> strip_tac >>
  Cases_on `step_in_block fn bb s1` >> Cases_on `step_in_block fn bb s2` >>
  gvs[] >>
  first_x_assum (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  simp[Once run_block_def] >>
  PURE_ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  Cases_on `q` >> gvs[result_equiv_except_def]
  >- (
    Cases_on `q'` >> gvs[result_equiv_except_def] >>
    `v.vs_halted = v'.vs_halted` by fs[state_equiv_except_def, execution_equiv_except_def] >>
    Cases_on `v.vs_halted` >> simp[result_equiv_except_def]
    >- (
      (* v.vs_halted = T: run_block returns Halt, need execution_equiv_except *)
      fs[state_equiv_except_def])
    >- (
      gvs[] >>
      Cases_on `r` >> simp[result_equiv_except_def] >>
      PURE_ONCE_REWRITE_TAC[GSYM run_block_def] >>
      first_x_assum irule >> simp[] >> metis_tac[]))
  >- (Cases_on `q'` >> gvs[result_equiv_except_def])
  >- (Cases_on `q'` >> gvs[result_equiv_except_def])
  >- (Cases_on `q'` >> gvs[result_equiv_except_def])
QED

(* ==========================================================================
   result_equiv_except Transitivity
   ========================================================================== *)

(* WHY THIS IS TRUE: result_equiv_except compares results by type:
   - OK/OK uses state_equiv_except which is transitive
   - Halt/Halt, Revert/Revert use execution_equiv_except which is transitive
   - Error/Error is always T
   Mismatched types are always F, so transitivity holds vacuously. *)
Theorem result_equiv_except_trans:
  !fresh r1 r2 r3.
    result_equiv_except fresh r1 r2 /\
    result_equiv_except fresh r2 r3 ==>
    result_equiv_except fresh r1 r3
Proof
  rw[result_equiv_except_def] >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >> fs[] >>
  metis_tac[state_equiv_except_trans, execution_equiv_except_trans]
QED

(* ==========================================================================
   transform_block_insts Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: When EVERY instruction in the prefix has transform_jnz = NONE,
   each is passed through unchanged by transform_block_insts. After n such
   instructions, we have the original TAKE n plus the transformation of DROP n. *)
Theorem transform_block_insts_TAKE_DROP:
  !n fn insts.
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n insts)
    ==>
    transform_block_insts fn insts =
      TAKE n insts ++ transform_block_insts fn (DROP n insts)
Proof
  Induct_on `n` >- simp[rich_listTheory.TAKE, rich_listTheory.DROP] >>
  rpt strip_tac >>
  Cases_on `insts`
  >- REWRITE_TAC[transform_block_insts_def, listTheory.TAKE_nil, listTheory.DROP_nil, listTheory.APPEND]
  >- (
    `transform_jnz fn h = NONE` by (
      pop_assum mp_tac >> REWRITE_TAC[rich_listTheory.TAKE, listTheory.EVERY_DEF] >> simp[]) >>
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    REWRITE_TAC[rich_listTheory.TAKE, rich_listTheory.DROP, listTheory.APPEND] >>
    AP_TERM_TAC >>
    first_x_assum irule >>
    pop_assum mp_tac >> REWRITE_TAC[rich_listTheory.TAKE, listTheory.EVERY_DEF] >> simp[] >>
    pop_assum mp_tac >> REWRITE_TAC[rich_listTheory.TAKE, listTheory.EVERY_DEF] >> simp[]
  )
QED

(* WHY THIS IS TRUE: transform_block_insts either keeps instructions (NONE case)
   or replaces them with multiple instructions (SOME case). Never fewer. *)
Theorem transform_block_insts_length_ge:
  !fn insts. LENGTH (transform_block_insts fn insts) >= LENGTH insts
Proof
  Induct_on `insts` >- simp[transform_block_insts_def] >>
  rw[] >> Cases_on `transform_jnz fn h`
  >- (
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    simp[listTheory.LENGTH] >> first_x_assum (qspec_then `fn` mp_tac) >> decide_tac
  )
  >- (
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    simp[] >>
    gvs[transform_jnz_def, AllCaseEqs()]
    >- (
      simp[transform_pattern1_def, mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def] >>
      first_x_assum (qspec_then `fn` mp_tac) >> decide_tac
    )
    >- (
      simp[transform_pattern2_def, mk_assert_inst_def, mk_jmp_inst_def] >>
      first_x_assum (qspec_then `fn` mp_tac) >> decide_tac
    )
  )
QED

(* WHY THIS IS TRUE: With prefix of NONEs, first n instructions are unchanged.
   At index n, transform_jnz returns SOME new_insts, so HD new_insts is at index n. *)
Theorem transform_block_insts_EL_transformed:
  !fn insts n new_insts.
    n < LENGTH insts /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME new_insts
    ==>
    EL n (transform_block_insts fn insts) = HD new_insts
Proof
  rw[] >>
  `transform_block_insts fn insts =
   TAKE n insts ++ transform_block_insts fn (DROP n insts)` by
     (irule transform_block_insts_TAKE_DROP >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `DROP n insts = EL n insts :: DROP (SUC n) insts` by
    simp[rich_listTheory.DROP_CONS_EL] >>
  pop_assum SUBST1_TAC >>
  simp[transform_block_insts_def] >>
  Cases_on `new_insts` >> gvs[]
  >- gvs[transform_jnz_def, AllCaseEqs(), transform_pattern1_def,
         transform_pattern2_def]
  >- simp[listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE]
QED

(* WHY THIS IS TRUE: With n NONE transforms followed by pattern1 (which adds 3 insts),
   the result has at least n + 3 elements. *)
Theorem transform_block_insts_length_pattern1:
  !fn insts n cond_op label.
    n < LENGTH insts /\
    EVERY (λi. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME (transform_pattern1 (EL n insts) cond_op label)
    ==>
    LENGTH (transform_block_insts fn insts) >= n + 3
Proof
  rw[] >>
  `LENGTH (transform_pattern1 (EL n insts) cond_op label) = 3` by
    simp[transform_pattern1_def, LET_THM, mk_iszero_inst_def,
         mk_assert_inst_def, mk_jmp_inst_def] >>
  `transform_block_insts fn insts = TAKE n insts ++ transform_block_insts fn (DROP n insts)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `LENGTH (TAKE n insts) = n` by simp[listTheory.LENGTH_TAKE] >>
  `DROP n insts = EL n insts :: DROP (n + 1) insts` by (
    `n < LENGTH insts` by simp[] >>
    metis_tac[rich_listTheory.DROP_EL_CONS]
  ) >>
  `transform_block_insts fn (DROP n insts) =
   transform_pattern1 (EL n insts) cond_op label ++ transform_block_insts fn (DROP (n + 1) insts)` by (
    simp[transform_block_insts_def]
  ) >>
  simp[listTheory.LENGTH_APPEND]
QED

(* WHY THIS IS TRUE: With n NONE transforms followed by pattern2 (which adds 2 insts),
   the result has at least n + 2 elements. *)
Theorem transform_block_insts_length_pattern2:
  !fn insts n cond_op label.
    n < LENGTH insts /\
    EVERY (λi. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME (transform_pattern2 (EL n insts) cond_op label)
    ==>
    LENGTH (transform_block_insts fn insts) >= n + 2
Proof
  rw[] >>
  `LENGTH (transform_pattern2 (EL n insts) cond_op label) = 2` by
    simp[transform_pattern2_def, LET_THM, mk_assert_inst_def, mk_jmp_inst_def] >>
  `transform_block_insts fn insts = TAKE n insts ++ transform_block_insts fn (DROP n insts)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `LENGTH (TAKE n insts) = n` by simp[listTheory.LENGTH_TAKE] >>
  `DROP n insts = EL n insts :: DROP (n + 1) insts` by (
    `n < LENGTH insts` by simp[] >>
    metis_tac[rich_listTheory.DROP_EL_CONS]
  ) >>
  `transform_block_insts fn (DROP n insts) =
   transform_pattern2 (EL n insts) cond_op label ++ transform_block_insts fn (DROP (n + 1) insts)` by (
    simp[transform_block_insts_def]
  ) >>
  simp[listTheory.LENGTH_APPEND]
QED

val _ = export_theory();
