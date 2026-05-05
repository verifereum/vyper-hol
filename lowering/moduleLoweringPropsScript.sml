
(* -*- sml -*- *)
(*
 * Module Lowering Properties
 *
 * TOP-LEVEL:
 *   compile_selector_dispatch_linear_correct — linear dispatch: partial CFG
 *   compile_selector_dispatch_sparse_correct — sparse dispatch: partial CFG
 *   compile_entry_point_kwargs_correct — kwargs init + JMP: partial CFG
 *   compile_entry_checks_correct — nonpayable/calldatasize checks (single-block)
 *   compile_entry_checks_nonpayable_revert — nonpayable revert (derived)
 *   compile_constructor_epilogue_correct — runtime code copy + RETURN (single-block)
 *   compile_generate_runtime_correct — top-level module correctness (stitching)
 *
 * Definitions:
 *   runtime_input_labels — labels the caller must supply as external
 *   runtime_inputs_ok — well-formed runtime compilation inputs
 *   dispatch_labels_covered — selector labels ⊆ external fn entry labels
 *
 * Helper (no standalone correctness — always composed):
 *   compile_decode_args_nil   — empty arg list is no-op
 *   compile_init_kwargs_nil   — empty kwargs list is no-op
 *
 * Source: module.py (VenomModuleCompiler)
 * Lowering: moduleLoweringScript.sml
 *
 * NOTE on execution models:
 *   - Selector dispatch and entry_point_kwargs create partial CFGs that
 *     jump to external labels (fn bodies, fallback, common body).
 *     These use run_compiled_fragment which treats exit to a non-assembled
 *     label as OK (returning the state at the exit point).
 *   - Entry checks and constructor epilogue stay within a single block,
 *     so they use the simpler run_inst_seq/emitted_insts pattern.
 *   - compile_decode_args and compile_init_kwargs are fragments (no terminator)
 *     always composed within a larger compilation. No standalone theorem;
 *     correctness is proved at the wrapper level (entry_point_kwargs for
 *     kwargs, compile_external_function_body for positional args).
 *)

Theory moduleLoweringProps
Ancestors
  stmtLoweringProps
  emitHelperProps
  exprLoweringProps
  moduleLowering compileEnv context
  venomExecSemantics venomState venomInst
  venomExecProps
  instIdxIndep
  stateEquiv
  abiEncoder finite_map
Libs
  bossLib wordsLib listLib

(* ===== bool_to_word condition bridge ===== *)

Theorem bool_to_word_neq_0w[local]:
  !b. (bool_to_word b <> 0w) = b
Proof
  Cases >> EVAL_TAC
QED

Theorem bool_to_word_eq_0w[local]:
  !b. (bool_to_word b = 0w) = ~b
Proof
  Cases >> EVAL_TAC
QED

(* ===== jump_to boundary lemmas ===== *)
(* jump_to boundary lemma: all fields except vs_prev_bb, vs_current_bb,
   vs_inst_idx are preserved. Use these instead of unfolding jump_to_def
   in consumer proofs — avoids fragile record update normalization. *)
Theorem jump_to_vs_current_bb[local]:
  !lbl ss. (jump_to lbl ss).vs_current_bb = lbl
Proof
  simp[jump_to_def]
QED

Theorem jump_to_vs_inst_idx[local]:
  !lbl ss. (jump_to lbl ss).vs_inst_idx = 0
Proof
  simp[jump_to_def]
QED

Theorem jump_to_vs_halted[local]:
  !lbl ss. (jump_to lbl ss).vs_halted <=> ss.vs_halted
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_memory[local]:
  !lbl ss. (jump_to lbl ss).vs_memory = ss.vs_memory
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_call_ctx[local]:
  !lbl ss. (jump_to lbl ss).vs_call_ctx = ss.vs_call_ctx
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_vars[local]:
  !lbl ss. (jump_to lbl ss).vs_vars = ss.vs_vars
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_accounts[local]:
  !lbl ss. (jump_to lbl ss).vs_accounts = ss.vs_accounts
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_labels[local]:
  !lbl ss. (jump_to lbl ss).vs_labels = ss.vs_labels
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_returndata[local]:
  !lbl ss. (jump_to lbl ss).vs_returndata = ss.vs_returndata
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_logs[local]:
  !lbl ss. (jump_to lbl ss).vs_logs = ss.vs_logs
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_transient[local]:
  !lbl ss. (jump_to lbl ss).vs_transient = ss.vs_transient
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem jump_to_vs_immutables[local]:
  !lbl ss. (jump_to lbl ss).vs_immutables = ss.vs_immutables
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem eval_operand_jump_to[local]:
  !op lbl ss. eval_operand op (jump_to lbl ss) = eval_operand op ss
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, jump_to_def,
    venom_state_component_equality]
QED

Theorem jump_to_vs_prev_bb[local]:
  !lbl ss. (jump_to lbl ss).vs_prev_bb = SOME ss.vs_current_bb
Proof
  simp[jump_to_def]
QED

Theorem fresh_vars_wrt_jump_to_eq[local]:
  ∀st ss lbl. fresh_vars_wrt st (jump_to lbl ss) ⇔ fresh_vars_wrt st ss
Proof
  simp[fresh_vars_wrt_def, jump_to_vs_vars]
QED

Theorem observable_equiv_jump_to[local]:
  !ss lbl. observable_equiv ss (jump_to lbl ss)
Proof
  simp[observable_equiv_def, jump_to_vs_accounts, jump_to_vs_returndata,
       jump_to_vs_halted, jump_to_vs_logs, jump_to_vs_transient,
       jump_to_vs_immutables]
QED

Theorem observable_equiv_jump_to_cong[local]:
  !s1 s2 lbl. observable_equiv s1 s2 ==>
    observable_equiv (jump_to lbl s1) (jump_to lbl s2)
Proof
  simp[observable_equiv_def, jump_to_vs_accounts, jump_to_vs_returndata,
       jump_to_vs_halted, jump_to_vs_logs, jump_to_vs_transient,
       jump_to_vs_immutables]
QED

Theorem observable_equiv_trans[local]:
  !s1 s2 s3. observable_equiv s1 s2 /\ observable_equiv s2 s3 ==> observable_equiv s1 s3
Proof
  simp[observable_equiv_def]
QED

(* ===== update_var preserves vs_halted ===== *)
(* Per-opcode EVERY-pure helpers for run_inst_seq_preserves_observable_and_memory.
   These follow the exact pattern of emit_op_EQ_everything_pure. *)
Theorem emit_op_CALLDATASIZE_everything_pure[local]:
  !st v st'. emit_op CALLDATASIZE [] st = (v,st') ==>
    EVERY (\i. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st st')
Proof
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> simp[mk_inst_opcode]
QED

Theorem emit_op_LT_everything_pure[local]:
  !op1 op2 st v st'. emit_op LT [op1; op2] st = (v,st') ==>
    EVERY (\i. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st st')
Proof
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> simp[mk_inst_opcode]
QED

Theorem emit_op_ISZERO_everything_pure[local]:
  !op1 st v st'. emit_op ISZERO [op1] st = (v,st') ==>
    EVERY (\i. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st st')
Proof
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> simp[mk_inst_opcode]
QED

Theorem emit_op_CALLDATALOAD_everything_pure[local]:
  !op1 st v st'. emit_op CALLDATALOAD [op1] st = (v,st') ==>
    EVERY (\i. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st st')
Proof
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> simp[mk_inst_opcode]
QED

Theorem emit_op_SHR_everything_pure[local]:
  !op1 op2 st v st'. emit_op SHR [op1; op2] st = (v,st') ==>
    EVERY (\i. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st st')
Proof
  rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> simp[mk_inst_opcode]
QED

(* Helper: compose emitted_insts across two inst_extends steps.
   Avoids simp[inst_extends_def] in large consumer contexts. *)
Theorem emitted_insts_append_from_extends[local]:
  ∀st st1 st2.
    inst_extends st st1 ∧ inst_extends st1 st2
    ⇒ emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2
Proof
  metis_tac[emitted_insts_append, inst_extends_def]
QED

(* Boundary lemma: derive inst_extends for the middle segment from outer segments.
   Given st extends to st1 and st to st2, with emitted_insts st st2 split at st1,
   we get st1 extends to st2. Avoids simp[inst_extends_def] in consumers. *)
Theorem inst_extends_middle[local]:
  ∀st st1 st2.
    inst_extends st st1 ∧ inst_extends st st2 ∧
    emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2
    ⇒ inst_extends st1 st2
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `inst_extends st st2` (fn th1 =>
    qpat_x_assum `inst_extends st st1` (fn th2 =>
      qpat_x_assum `emitted_insts st st2 = _` (fn th3 =>
        simp[inst_extends_def,
             REWRITE_RULE[inst_extends_def] th1,
             REWRITE_RULE[inst_extends_def] th2,
             th3, listTheory.APPEND_ASSOC])))
QED

(* 3-segment EVERY composition: proves EVERY P on the composite emitted_insts
   from per-segment facts. Tiny context — avoids simp/metis in 50+ assumption consumers. *)
Theorem emitted_insts_every_append3[local]:
  ∀P st st1 st2 st3.
    inst_extends st st1 ∧ inst_extends st1 st2 ∧ inst_extends st2 st3 ∧
    EVERY P (emitted_insts st st1) ∧
    EVERY P (emitted_insts st1 st2) ∧
    EVERY P (emitted_insts st2 st3)
    ⇒ EVERY P (emitted_insts st st3)
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2`
    by metis_tac[emitted_insts_append_from_extends] >>
  `inst_extends st st2` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st3 = emitted_insts st st2 ++ emitted_insts st2 st3`
    by metis_tac[emitted_insts_append_from_extends] >>
  simp[listTheory.EVERY_APPEND]
QED

(* Opcodes in the "everything_pure" set are not terminators and not INVOKE.
   Used to derive EVERY purity conclusions from segment-level purity facts. *)
Theorem pure_opcodes_not_terminator_not_invoke[local]:
  !opc. opc IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                ISZERO; AND; OR; XOR; NOT;
                CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                MLOAD; SLOAD; TLOAD; OFFSET; PARAM}
    ==> ¬is_terminator opc ∧ opc ≠ INVOKE
Proof
  Cases_on `opc` >> EVAL_TAC
QED

(* Monotonicity bridges: avoid HO matching in consumer proofs *)
Theorem pure_every_imp_not_terminator[local]:
  !ls. EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                ISZERO; AND; OR; XOR; NOT;
                CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                MLOAD; SLOAD; TLOAD; OFFSET; PARAM}) ls
    ==> EVERY (λi. ¬is_terminator i.inst_opcode) ls
Proof
  Induct >> simp[pure_opcodes_not_terminator_not_invoke]
QED

Theorem pure_every_imp_not_invoke[local]:
  !ls. EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                ISZERO; AND; OR; XOR; NOT;
                CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;

                GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                MLOAD; SLOAD; TLOAD; OFFSET; PARAM}) ls
    ==> EVERY (λi. i.inst_opcode ≠ INVOKE) ls
Proof
  Induct >> simp[pure_opcodes_not_terminator_not_invoke]
QED

(* Non-terminator instructions preserve vs_current_bb: the only
   instructions that modify vs_current_bb are JMP, JNZ, DJMP (via
   jump_to), which are all terminators. *)
Theorem step_inst_base_not_terminator_preserves_current_bb[local]:
  !i s s'.
    step_inst_base i s = OK s' /\
    ~is_terminator i.inst_opcode
    ==> s'.vs_current_bb = s.vs_current_bb
Proof
  rw[step_inst_base_def] >>
  gvs[is_terminator_def, AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def, jump_to_def,
     revert_state_def, set_returndata_def, halt_state_def,
     eval_operands_def] >>
  simp[venom_state_component_equality]
QED

(* Non-terminator instructions preserve vs_current_bb through a whole
   instruction sequence. Proved by direct induction on the list. *)
Theorem run_inst_seq_preserves_current_bb[local]:
  !is ss ss'.
    run_inst_seq is ss = OK ss' /\
    EVERY (\i. ~is_terminator i.inst_opcode) is /\
    EVERY (\i. i.inst_opcode <> INVOKE) is /\
    ~ss.vs_halted
    ==> ss'.vs_current_bb = ss.vs_current_bb
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h ss` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h ss = OK mid` >>
  `mid.vs_current_bb = ss.vs_current_bb` by (
    drule step_inst_base_not_terminator_preserves_current_bb >> simp[]) >>
  `ss'.vs_current_bb = mid.vs_current_bb` by (
    first_x_assum irule >> simp[] >>
    drule step_inst_base_OK_preserves_halted >> simp[]) >>
  simp[]
QED

(* ===== Local Helpers for compile_state_ok chaining ===== *)

Theorem compiler_labels_future_mono:
  !m n. m >= n ==> compiler_labels_future m SUBSET compiler_labels_future n
Proof
  rpt gen_tac >> strip_tac >>
  simp[compiler_labels_future_def] >>
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_GSPEC] >>
  rpt gen_tac >> strip_tac >>
  qexistsl [`s''`, `k`] >> simp[]
QED

Theorem SUBSET_LEFT_UNION:
  !s t u. s SUBSET t ==> s SUBSET t UNION u
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION]
QED

Theorem SUBSET_RIGHT_UNION:
  !s t u. s SUBSET u ==> s SUBSET t UNION u
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION]
QED

Theorem bound_labels_subset_trans:
  !st1 st2 st3.
    bound_labels st2 SUBSET bound_labels st1 UNION compiler_labels_future st1.cs_next_label /\
    bound_labels st3 SUBSET bound_labels st2 UNION compiler_labels_future st2.cs_next_label /\
    st2.cs_next_label >= st1.cs_next_label
    ==>
    bound_labels st3 SUBSET bound_labels st1 UNION compiler_labels_future st1.cs_next_label
Proof
  rpt strip_tac >>
  `compiler_labels_future st2.cs_next_label SUBSET compiler_labels_future st1.cs_next_label`
    by (drule compiler_labels_future_mono >> simp[]) >>
  `compiler_labels_future st2.cs_next_label SUBSET
   bound_labels st1 UNION compiler_labels_future st1.cs_next_label`
    by metis_tac[SUBSET_RIGHT_UNION] >>
  `bound_labels st2 UNION compiler_labels_future st2.cs_next_label SUBSET
   bound_labels st1 UNION compiler_labels_future st1.cs_next_label`
    by (simp[pred_setTheory.UNION_SUBSET] >> metis_tac[SUBSET_LEFT_UNION]) >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem bound_labels_emit_op_fresh_label_inst_subset:
  ∀st st'.
    compile_state_ok st ∧
    bound_labels st' = bound_labels st ∧
    st'.cs_next_label ≥ st.cs_next_label ∧
    compile_state_ok st'
    ⇒ bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label
Proof
  rpt strip_tac >>
  fs[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION]
QED


Theorem bound_labels_new_block_insert_subset:
  ∀st st' new_lbl.
    compile_state_ok st ∧
    bound_labels st' = new_lbl INSERT bound_labels st ∧
    st'.cs_next_label ≥ st.cs_next_label ∧
    new_lbl ∈ compiler_labels_future st.cs_next_label ∧
    compile_state_ok st'
    ⇒ bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
       pred_setTheory.IN_INSERT] >>
  metis_tac[]
QED

Theorem INSERT_UNION_SUBSET[local]:
  ∀x s t. x INSERT s ⊆ s ∪ t ⇔ x ∈ s ∨ x ∈ t
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
       pred_setTheory.IN_INSERT] >>
  metis_tac[]
QED

Theorem bound_labels_mono_new_block[local]:
  !st st' new_lbl.
    bound_labels st' = new_lbl INSERT bound_labels st
    ==> bound_labels st SUBSET bound_labels st'
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_INSERT]
QED


Theorem bound_labels_double_insert_subset:
  ∀st st' lbl1 lbl2.
    compile_state_ok st ∧
    bound_labels st' = lbl1 INSERT lbl2 INSERT bound_labels st ∧
    st'.cs_next_label ≥ st.cs_next_label ∧
    lbl1 ∈ compiler_labels_future st.cs_next_label ∧
    lbl2 ∈ compiler_labels_future st.cs_next_label ∧
    compile_state_ok st'
    ⇒ bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
       pred_setTheory.IN_INSERT] >>
  metis_tac[]
QED

(* ===== Shared Fragment Helper ===== *)

Theorem IN_set_MEM[local]:
  ∀x l. x ∈ set l ⇔ MEM x l
Proof
  Induct_on `l` >> simp[]
QED

Theorem FIND_NONE_imp:
  ∀P l. (∀x. MEM x l ⇒ ¬P x) ⇒ FIND P l = NONE
Proof
  Induct_on `l` >> simp[listTheory.FIND_thm]
QED

Theorem FIND_MEM_imp_exists[local]:
  ∀P l. (∃x. MEM x l ∧ P x) ⇒ IS_SOME (FIND P l)
Proof
  Induct_on `l` >> simp[listTheory.FIND_thm] >>
  rpt gen_tac >> Cases_on `P h` >> simp[] >> metis_tac[]
QED

Theorem FIND_MEM_imp[local]:
  ∀P l x. MEM x l ∧ P x ⇒ IS_SOME (FIND P l)
Proof
  metis_tac[FIND_MEM_imp_exists]
QED

Theorem lookup_block_append:
  !l lbl l2.
    lookup_block lbl l = NONE ==>
    lookup_block lbl (l ++ l2) = lookup_block lbl l2
Proof
  Induct_on `l` >> rpt strip_tac >> gvs[lookup_block_def] >>
  gvs[listTheory.FIND_thm]
QED

Theorem lookup_block_append_found:
  !l lbl l2.
    IS_SOME (lookup_block lbl l) ==>
    lookup_block lbl (l ++ l2) = lookup_block lbl l
Proof
  rpt gen_tac >> Induct_on `l` >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  gen_tac >> strip_tac >>
  Cases_on `h.bb_label = lbl` >> fs[lookup_block_def]
QED

Theorem FIND_APPEND_found[local]:
  !P l l2.
    IS_SOME (FIND P l) ==>
    FIND P (l ++ l2) = FIND P l
Proof
  rpt gen_tac >> Induct_on `l` >>
  simp[listTheory.FIND_thm] >>
  gen_tac >> strip_tac >>
  Cases_on `P h` >> fs[]
QED
Theorem new_block_creates_assembled_block:
  ∀st label old st'.
    new_block label st = (old, st') ⇒
    FIND (λbb. bb.bb_label = st.cs_current_bb) st'.cs_blocks = SOME <|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts|> ∧
    st'.cs_current_bb = label ∧
    st'.cs_current_insts = []
Proof
  rpt strip_tac >> imp_res_tac new_block_props >> gvs[listTheory.FIND_thm]
QED
Theorem lbl_notin_bound_labels_imp:
  ∀st st' lbl.
    label_external st lbl ∧ compile_state_ok st ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label
    ⇒ lbl ∉ bound_labels st'
Proof
  rpt strip_tac >> fs[label_external_def] >>
  metis_tac[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
            pred_setTheory.IN_INSERT, bound_labels_def]
QED

Theorem notin_bound_labels_find_none:
  ∀st' lbl.
    lbl ∉ bound_labels st' ⇒
    lookup_block lbl (assemble_blocks st') = NONE
Proof
  rpt strip_tac >>
  simp[lookup_block_def, assemble_blocks_def] >>
  irule FIND_NONE_imp >>
  rpt strip_tac >>
  fs[bound_labels_def, pred_setTheory.IN_INSERT, listTheory.MEM_APPEND] >-
  metis_tac[listTheory.MEM_MAP] >>
  fs[venomInstTheory.basic_block_component_equality]
QED

Theorem label_external_not_in_assembled:
  ∀st st' lbl.
    label_external st lbl ∧ compile_state_ok st ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label
    ⇒ lookup_block lbl (assemble_blocks st') = NONE
Proof
  metis_tac[lbl_notin_bound_labels_imp, notin_bound_labels_find_none]
QED

Theorem label_external_through_compile_ops:
  ∀st st' lbl.
    compile_state_ok st ∧ label_external st lbl ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    st'.cs_next_label ≥ st.cs_next_label ∧ compile_state_ok st'
    ⇒ label_external st' lbl
Proof
  rpt strip_tac >> fs[label_external_def] >>
  conj_tac >- metis_tac[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
                        pred_setTheory.IN_INSERT, bound_labels_def] >>
  drule compiler_labels_future_mono >> metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem EVERY_label_external_preserved:
  ∀st st' lbls.
    EVERY (label_external st) lbls ∧
    compile_state_ok st ∧ compile_state_ok st' ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    st'.cs_next_label ≥ st.cs_next_label
    ⇒
    EVERY (label_external st') lbls
Proof
  Induct_on `lbls` >- simp[] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  conj_tac >-
    (mp_tac (Q.SPECL [`st`,`st'`,`h`] label_external_through_compile_ops) >> simp[]) >>
  first_x_assum (qspecl_then [`st`,`st'`] mp_tac) >> simp[]
QED

Theorem EVERY_label_external_MAP_SND_cons:
  ∀P sel fn_label rest.
    EVERY P (MAP SND ((sel,fn_label)::rest)) ⇒
    P fn_label ∧ EVERY P (MAP SND rest)
Proof
  rpt strip_tac >> fs[]
QED


Theorem fresh_label_output_in_compiler_labels_future:
  ∀suffix k n.
    n ≤ k ⇒ fresh_label_output suffix k ∈ compiler_labels_future n
Proof
  rpt strip_tac >>
  simp[compiler_labels_future_def] >>
  qexistsl [`suffix`, `k`] >> simp[]
QED

(* If lbl is external to st, it cannot equal any fresh_label_output from
   compiler_labels_future. Key for showing caller labels ≠ compiler labels. *)
Theorem label_external_neq_compiler_label:
  !st lbl suffix k.
    label_external st lbl /\
    fresh_label_output suffix k IN compiler_labels_future st.cs_next_label
    ==> lbl <> fresh_label_output suffix k
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  fs[label_external_def] >>
  metis_tac[]
QED

Theorem fresh_label_in_compiler_labels_future:
  ∀suffix st lbl st'.
    fresh_label suffix st = (lbl,st') ∧ compile_state_ok st ⇒
    lbl ∈ compiler_labels_future st.cs_next_label
Proof
  rpt strip_tac >>
  fs[fresh_label_def] >>
  qpat_x_assum `fresh_label_output _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule fresh_label_output_in_compiler_labels_future >>
  decide_tac
QED

(* If lbl is external to st and new_block other_lbl st = (_,st') with
   lbl <> other_lbl, then lbl remains external to st'. Bound_labels grows
   by one element (other_lbl) and cs_next_label is unchanged, so lbl stays
   out of both bound_labels and compiler_labels_future. *)
Theorem label_external_new_block_other:
  !lbl other_lbl st st' old.
    new_block other_lbl st = (old,st') /\
    compile_state_ok st /\
    label_external st other_lbl /\
    label_external st lbl /\
    lbl <> other_lbl
    ==> label_external st' lbl /\ compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  `compile_state_ok st' /\
   bound_labels st' = other_lbl INSERT bound_labels st /\
   st'.cs_next_label = st.cs_next_label /\
   st'.cs_current_bb = other_lbl /\
   old = st.cs_current_bb`
    by metis_tac[compile_state_ok_new_block] >>
  conj_tac >- gvs[label_external_def] >> gvs[]
QED

Theorem label_external_preserved_through_step:
  ∀st cs7 match_lbl next_lbl lbl.
    label_external st lbl ∧
    compile_state_ok st ∧
    compile_state_ok cs7 ∧
    bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st ∧
    cs7.cs_next_label ≥ st.cs_next_label ∧
    match_lbl ∈ compiler_labels_future st.cs_next_label ∧
    next_lbl ∈ compiler_labels_future st.cs_next_label
    ⇒ label_external cs7 lbl
Proof
  rpt strip_tac >>
  fs[label_external_def] >>
  conj_tac >- (
    simp[pred_setTheory.IN_INSERT] >>
    metis_tac[label_external_neq_compiler_label, bound_labels_def]) >>
  drule compiler_labels_future_mono >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED
(* ===== Emitted Instructions in Assembled Block ===== *)

(* If st and st' share the same block structure (no new_block was called),
   then the assembled current block contains ALL of st'.cs_current_insts,
   and the "emitted" part starts at LENGTH st.cs_current_insts.
   compile_state_ok st ensures st.cs_current_bb is distinct from all
   labels in st.cs_blocks, so lookup_block finds the correct (last) block. *)
Theorem current_bb_not_in_blocks[local]:
  !st. compile_state_ok st ==>
    !bb. MEM bb st.cs_blocks ==> bb.bb_label <> st.cs_current_bb
Proof
  simp[compile_state_ok_def] >> rpt strip_tac >>
  Cases_on `bb` >> fs[listTheory.MEM_MAP] >>
  first_x_assum (qspec_then `basic_block s l` mp_tac) >> simp[]
QED

Theorem current_bb_not_in_blocks_MAP[local]:
  ∀st. compile_state_ok st ⇒
       ¬MEM st.cs_current_bb (MAP (λbb. bb.bb_label) st.cs_blocks)
Proof
  simp[listTheory.MEM_MAP, PULL_EXISTS] >>
  metis_tac[current_bb_not_in_blocks]
QED

Theorem same_blocks_lookup_current:
  !st st' bb.
    same_blocks st st' /\ compile_state_ok st /\
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb
    ==>
    bb.bb_instructions = st'.cs_current_insts
Proof
  rpt strip_tac >>
  fs[same_blocks_def, compile_state_ok_def] >>
  drule lookup_block_assemble_current >> simp[]
QED

Theorem emitted_insts_in_assembled_block:
  !st st'. compile_state_ok st /\ st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_blocks = st.cs_blocks ==>
    !bb. lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ==>
         bb.bb_instructions = st'.cs_current_insts /\
         (EVERY (\i. ~is_terminator i.inst_opcode) (DROP (LENGTH st.cs_current_insts) bb.bb_instructions) ==>
          (!k. k < LENGTH (emitted_insts st st') ==>
               get_instruction bb (LENGTH st.cs_current_insts + k) = SOME (EL k (emitted_insts st st'))) /\
          (!k is. emitted_insts st st' = is ==>
               EVERY (\i. ~is_terminator i.inst_opcode) is ==>
               !k. k < LENGTH is ==> get_instruction bb (LENGTH st.cs_current_insts + k) = SOME (EL k is)))
Proof
  rpt strip_tac >>
  `same_blocks st st'` by simp[same_blocks_def] >> drule_all_then (fn th => simp[th]) same_blocks_lookup_current >>
  drule same_blocks_lookup_current >> simp[emitted_insts_def] >> strip_tac >> gvs[get_instruction_def] >>
  gvs[emitted_insts_def, listTheory.EL_DROP, listTheory.LENGTH_DROP]
QED

Theorem emitted_insts_get_instruction:
  !st st' bb idx is.
    same_blocks st st' /\ compile_state_ok st /\
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb /\
    emitted_insts st st' = is /\
    idx = LENGTH st.cs_current_insts
    ==>
    !k. k < LENGTH is ==> get_instruction bb (idx + k) = SOME (EL k is)
Proof
  rpt strip_tac >>
  drule same_blocks_lookup_current >> simp[emitted_insts_def] >> strip_tac >>
  gvs[get_instruction_def] >>
  gvs[emitted_insts_def, listTheory.EL_DROP, listTheory.LENGTH_DROP]
QED



(* ===== Fragment Execution Model ===== *)
Definition run_fragment_blocks_def:
  run_fragment_blocks 0 ctx fn ss = Error "out of fuel" ∧
  run_fragment_blocks (SUC fuel) ctx fn ss =
    case lookup_block ss.vs_current_bb fn.fn_blocks of
      NONE => OK ss
    | SOME bb =>
        case exec_block fuel ctx bb (ss with vs_inst_idx := 0) of
          OK ss' =>
            if ss'.vs_halted then Halt ss'
            else run_fragment_blocks fuel ctx fn ss'
        | IntRet vals ss' => IntRet vals ss'
        | Halt ss' => Halt ss'
        | Abort a ss' => Abort a ss'
        | Error e => Error e
End
(* ===== Fragment Step Lemmas ===== *)

(* One step of fragment execution: the current block bb has a pure instruction
   prefix followed by a JMP to target_lbl. Execution produces jump_to target_lbl ss',
   then run_fragment_blocks continues from that state with one less unit of fuel.
   This is the key compositional step: after one block, execution resumes at
   the target label. *)
Theorem fragment_step_ok:
  ∀fuel ctx fn bb ss insts ss' target_lbl jmp_id.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb k = SOME (EL k insts)) ∧
    get_instruction bb (LENGTH insts) =
      SOME (mk_inst jmp_id JMP [Label target_lbl] []) ∧
    ¬ss'.vs_halted ∧
    lookup_block bb.bb_label fn.fn_blocks = SOME bb ∧
    ss.vs_current_bb = bb.bb_label
    ⇒
    run_fragment_blocks (SUC fuel) ctx fn ss =
      run_fragment_blocks fuel ctx fn (jump_to target_lbl ss')
Proof
  rpt strip_tac >>
  simp[Once run_fragment_blocks_def] >>
  assume_tac exec_block_inst_seq_jmp >>
  first_x_assum (qspecl_then [`insts`,`fuel`,`ctx`,`bb`,`0`,`ss`,`ss'`,`target_lbl`,`jmp_id`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (fn th => mp_tac th >> simp[]) >>
  strip_tac >> gvs[jump_to_def]
QED


(* One step of fragment execution: the current block bb has a pure instruction
   prefix followed by a JNZ terminator. Execution produces
   jump_to (if cond_v ≠ 0w then lbl_nz else lbl_z) ss'. *)
Theorem fragment_step_jnz:
  ∀fuel ctx fn bb ss insts ss' cond_op cond_v lbl_nz lbl_z jnz_id idx.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb (idx + k) = SOME (EL k insts)) ∧
    get_instruction bb (idx + LENGTH insts) =
      SOME (mk_inst jnz_id JNZ [cond_op; Label lbl_nz; Label lbl_z] []) ∧
    eval_operand cond_op ss' = SOME cond_v ∧
    ¬ss'.vs_halted ∧
    lookup_block bb.bb_label fn.fn_blocks = SOME bb ∧
    ss.vs_current_bb = bb.bb_label ∧
    ss.vs_inst_idx = idx
    ⇒
    exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
      OK (jump_to (if cond_v ≠ 0w then lbl_nz else lbl_z) ss')
Proof
  rpt strip_tac >> drule_all exec_block_inst_seq_jnz >> fs[]
QED

(* Two steps of fragment execution: the current block bb has a pure instruction
   prefix followed by a JNZ terminator. exec_block produces the jump, then
   run_fragment_blocks continues from the target with one less unit of fuel.
   This is the fragment-level version of fragment_step_jnz. *)
Theorem fragment_step_jnz_ok:
  ∀fuel ctx fn bb ss insts ss' cond_op cond_v lbl_nz lbl_z jnz_id.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb k = SOME (EL k insts)) ∧
    get_instruction bb (LENGTH insts) =
      SOME (mk_inst jnz_id JNZ [cond_op; Label lbl_nz; Label lbl_z] []) ∧
    eval_operand cond_op ss' = SOME cond_v ∧
    ¬ss'.vs_halted ∧
    lookup_block bb.bb_label fn.fn_blocks = SOME bb ∧
    ss.vs_current_bb = bb.bb_label
    ⇒
    run_fragment_blocks (SUC (SUC fuel)) ctx fn ss =
      if cond_v ≠ 0w then run_fragment_blocks (SUC fuel) ctx fn (jump_to lbl_nz ss')
      else run_fragment_blocks (SUC fuel) ctx fn (jump_to lbl_z ss')
Proof
  rpt strip_tac >> simp[Once run_fragment_blocks_def] >>
  qspecl_then [`insts`,`SUC fuel`,`ctx`,`bb`,`0`,`ss`,`ss'`,`cond_op`,`cond_v`,`lbl_nz`,`lbl_z`,`jnz_id`] mp_tac exec_block_inst_seq_jnz >> disch_tac >> simp[jump_to_def] >> IF_CASES_TAC >> simp[jump_to_def]
QED



(* Run a compiled fragment (partial CFG). Like run_compiled_blocks but
   uses run_fragment_blocks: exits with OK when execution reaches a
   label not in the assembled blocks. *)
Definition run_compiled_fragment_def:
  run_compiled_fragment ctx st st' ss fuel =
    let fn = assemble_function st st' in
    let entry_lbl = st.cs_current_bb in
    let entry_idx = LENGTH st.cs_current_insts in
    case lookup_block entry_lbl fn.fn_blocks of
      NONE => Error "entry block not found"
    | SOME bb =>
        case exec_block fuel ctx bb
               (ss with <| vs_current_bb := entry_lbl;
                            vs_inst_idx := entry_idx |>) of
          OK ss' =>
            if ss'.vs_halted then Halt ss'
            else run_fragment_blocks fuel ctx fn ss'
        | IntRet vals ss' => IntRet vals ss'
        | Halt ss' => Halt ss'
        | Abort a ss' => Abort a ss'
        | Error e => Error e
End

Theorem fragment_entry_correct:
  ∀st st' ctx ss bb fuel.
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted
    ⇒
    run_compiled_fragment ctx st st' ss fuel =
      case exec_block fuel ctx bb (ss with <|vs_current_bb := st.cs_current_bb; vs_inst_idx := LENGTH st.cs_current_insts|>) of
        OK ss' => if ss'.vs_halted then Halt ss' else run_fragment_blocks fuel ctx (assemble_function st st') ss'
      | IntRet vals ss' => IntRet vals ss'
      | Halt ss' => Halt ss'
      | Abort a ss' => Abort a ss'
      | Error e => Error e
Proof
  rpt gen_tac >> strip_tac >> simp[run_compiled_fragment_def, assemble_function_def]
QED

Theorem rcf_state_normalize[local]:
  !ctx st st' ss fuel.
    run_compiled_fragment ctx st st' ss fuel =
    run_compiled_fragment ctx st st'
      (ss with <|vs_current_bb := st.cs_current_bb;
                  vs_inst_idx := LENGTH st.cs_current_insts|>) fuel
Proof
  simp[run_compiled_fragment_def]
QED


(* vs_current_bb in ss is irrelevant: run_compiled_fragment overwrites it
   with st.cs_current_bb regardless. *)
Theorem run_compiled_fragment_vs_current_bb_irrel[local]:
  !ctx st st' ss fuel.
    run_compiled_fragment ctx st st' ss fuel =
    run_compiled_fragment ctx st st' (ss with vs_current_bb := st.cs_current_bb) fuel
Proof
  simp[run_compiled_fragment_def]
QED

(* eval_operand, fresh_vars_wrt, observable_equiv are all independent of vs_current_bb *)
Theorem eval_operand_current_bb_irrel[local]:
  !op s lbl. eval_operand op (s with vs_current_bb := lbl) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem fresh_vars_wrt_current_bb_irrel[local]:
  !st s lbl. fresh_vars_wrt st (s with vs_current_bb := lbl) = fresh_vars_wrt st s
Proof
  simp[fresh_vars_wrt_def]
QED

Theorem observable_equiv_current_bb_irrel[local]:
  !s1 s2 lbl.
    observable_equiv s1 (s2 with vs_current_bb := lbl) = observable_equiv s1 s2
Proof
  simp[observable_equiv_def]
QED

Theorem vs_halted_current_bb_irrel[local]:
  !s lbl. (s with vs_current_bb := lbl).vs_halted = s.vs_halted
Proof
  simp[]
QED

Theorem vs_memory_current_bb_irrel[local]:
  !s lbl. (s with vs_current_bb := lbl).vs_memory = s.vs_memory
Proof
  simp[]
QED

Theorem vs_call_ctx_current_bb_irrel[local]:
  !s lbl. (s with vs_current_bb := lbl).vs_call_ctx = s.vs_call_ctx
Proof
  simp[]
QED



(* When entry is from the start of a block (empty current_insts, vs_inst_idx = 0),
   run_fragment_blocks directly matches the first step of run_compiled_fragment. *)
Theorem run_fragment_blocks_eq_compiled_fragment:
  !fuel ctx st st' ss bb.
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb /\
    ss.vs_current_bb = st.cs_current_bb /\
    ss.vs_inst_idx = 0 /\
    st.cs_current_insts = [] /\
    ~ss.vs_halted
    ==>
    run_fragment_blocks (SUC fuel) ctx (assemble_function st st') ss =
      case exec_block fuel ctx bb (ss with <|vs_current_bb := st.cs_current_bb; vs_inst_idx := LENGTH st.cs_current_insts|>) of
        OK ss' => if ss'.vs_halted then Halt ss' else run_fragment_blocks fuel ctx (assemble_function st st') ss'
      | IntRet vals ss' => IntRet vals ss'
      | Halt ss' => Halt ss'
      | Abort a ss' => Abort a ss'
      | Error e => Error e
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once run_fragment_blocks_def, assemble_function_def] >>
  `ss with vs_current_bb := st.cs_current_bb = ss`
    by simp[venom_state_component_equality] >>
  simp[]
QED




(* Local helper: exec_block with a single JMP instruction at index 0.
   Avoids the two-field record update mismatch with exec_block_inst_seq_jmp. *)
Theorem exec_block_jmp_at_zero[local]:
  !fuel ctx bb s target_lbl jmp_id.
    get_instruction bb 0 = SOME (mk_inst jmp_id JMP [Label target_lbl] []) /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted
    ==>
    exec_block (SUC fuel) ctx bb s = OK (jump_to target_lbl s)
Proof
  rpt strip_tac >>
  simp[Once exec_block_def] >>
  simp[step_inst_non_invoke, mk_inst_def, step_jmp_behavior,
       is_terminator_def, jump_to_def]
QED

(* JMP-only fragment exit: emit_inst JMP creates a block whose only
   instruction is JMP to target_lbl. Execution reaches target_lbl and
   exits the fragment since target_lbl is external. *)
Theorem jmp_fragment_exit_correct:
  ∀st st' target_lbl fuel ctx ss bb.
    emit_inst JMP [Label target_lbl] [] st = ((), st') ∧
    compile_state_ok st ∧
    label_external st target_lbl ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted ∧
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    st.cs_current_insts = [] ∧
    bb.bb_instructions = st'.cs_current_insts
    ⇒
    ∃fuel' ss'.
      run_compiled_fragment ctx st st' ss fuel' = OK ss' ∧
      ss'.vs_current_bb = target_lbl ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt strip_tac >>
  `compile_state_ok st' ∧ st'.cs_current_bb = st.cs_current_bb ∧
   st'.cs_blocks = st.cs_blocks ∧ st'.cs_next_label = st.cs_next_label ∧
   bound_labels st' = bound_labels st`
    by (drule compile_state_ok_emit_inst >> simp[]) >>
  `same_blocks st st'` by fs[same_blocks_def] >>
  `inst_extends st st'` by metis_tac[inst_extends_emit_inst] >>
  `st'.cs_next_var = st.cs_next_var`
    by metis_tac[emitted_insts_emit_inst] >>
  `fresh_vars_wrt st' ss` by (drule fresh_vars_wrt_mono >> simp[]) >>
  `st'.cs_current_insts = [mk_inst st.cs_next_id JMP [Label target_lbl] []]`
    by (imp_res_tac emitted_insts_emit_inst >>
        fs[inst_extends_def, emitted_insts_def]) >>
  `lookup_block target_lbl (assemble_blocks st') = NONE`
    by (drule label_external_not_in_assembled >> simp[]) >>
  `get_instruction bb 0 =
     SOME (mk_inst st.cs_next_id JMP [Label target_lbl] [])`
    by gvs[get_instruction_def] >>
  qabbrev_tac `ss0 = ss with <|vs_current_bb := st.cs_current_bb;
                                vs_inst_idx := 0|>` >>
  qabbrev_tac `fn = assemble_function st st'` >>
  `fn.fn_name = st.cs_current_bb` by simp[assemble_function_def, Abbr `fn`] >>
  `fn.fn_blocks = assemble_blocks st'` by simp[assemble_function_def, Abbr `fn`] >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `¬ss0.vs_halted` by simp[Abbr `ss0`] >>
  `ss0.vs_current_bb = st.cs_current_bb` by simp[Abbr `ss0`] >>
  `bb.bb_label = st.cs_current_bb`
    by metis_tac[lookup_block_label] >>
  `ss0.vs_current_bb = bb.bb_label` by simp[] >>
  qexistsl [`SUC fuel`,`jump_to target_lbl ss0`] >>
  reverse conj_tac >- (
    (* Preservation: observable_equiv, memory, call_ctx, halted, fresh_vars, state_ok *)
    fs[jump_to_def,Abbr `ss0`,observable_equiv_def,
       fresh_vars_wrt_def,compile_state_ok_def]) >>
  (* Main: run_compiled_fragment = OK *)
  `exec_block (SUC fuel) ctx bb ss0 = OK (jump_to target_lbl ss0)`
    by (simp[Abbr `ss0`,Once exec_block_def,step_inst_non_invoke,
             mk_inst_def,step_jmp_behavior,is_terminator_def,jump_to_def]) >>
  simp[Abbr `fn`,run_compiled_fragment_def,assemble_function_def] >>
  gvs[AllCaseEqs(),jump_to_def,Abbr `ss0`,exec_block_OK_not_halted] >>
  simp[run_fragment_blocks_def,assemble_function_def]
QED

(* General JMP fragment exit: emit_inst JMP anywhere in the current block.
   The existing instructions are pure/non-terminator, so exec_block processes
   them all, reaches the JMP at LENGTH st.cs_current_insts, jumps to
   target_lbl, and run_fragment_blocks exits OK since target_lbl is external. *)
Theorem jmp_external_exits_fragment:
  ∀st st' target_lbl ctx ss.
    emit_inst JMP [Label target_lbl] [] st = ((), st') ∧
    compile_state_ok st ∧
    label_external st target_lbl ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      ss'.vs_current_bb = target_lbl ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt strip_tac >>
  `compile_state_ok st' ∧ st'.cs_current_bb = st.cs_current_bb ∧
   st'.cs_blocks = st.cs_blocks ∧ st'.cs_next_label = st.cs_next_label ∧
   bound_labels st' = bound_labels st`
    by (drule compile_state_ok_emit_inst >> simp[]) >>
  `same_blocks st st'` by fs[same_blocks_def] >>
  `inst_extends st st'` by metis_tac[inst_extends_emit_inst] >>
  `st'.cs_next_var = st.cs_next_var`
    by metis_tac[emitted_insts_emit_inst] >>
  `fresh_vars_wrt st' ss` by (drule fresh_vars_wrt_mono >> simp[]) >>
  `st'.cs_current_insts = st.cs_current_insts ++ [mk_inst st.cs_next_id JMP [Label target_lbl] []]`
    by (imp_res_tac emitted_insts_emit_inst >>
        fs[inst_extends_def, emitted_insts_def]) >>
  `lookup_block target_lbl (assemble_blocks st') = NONE`
    by (drule label_external_not_in_assembled >> simp[]) >>
  (* Derive the current block via lookup_block_assemble_current *)
  `¬MEM st.cs_current_bb (MAP (λbb. bb.bb_label) st'.cs_blocks)`
    by (imp_res_tac current_bb_not_in_blocks >> fs[listTheory.MEM_MAP] >> metis_tac[]) >>
  qabbrev_tac `bb = <|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>` >>
  `lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb`
    by (drule lookup_block_assemble_current >> simp[Abbr `bb`]) >>
  `bb.bb_instructions = st'.cs_current_insts` by simp[Abbr `bb`] >>
  `bb.bb_label = st.cs_current_bb` by simp[Abbr `bb`] >>
  `get_instruction bb (LENGTH st.cs_current_insts) =
     SOME (mk_inst st.cs_next_id JMP [Label target_lbl] [])`
    by (simp[Abbr `bb`,get_instruction_def,listTheory.LENGTH_APPEND,
             rich_listTheory.EL_APPEND2]) >>
  qabbrev_tac `ss0 = ss with <|vs_current_bb := st.cs_current_bb;
                                vs_inst_idx := LENGTH st.cs_current_insts|>` >>
  qabbrev_tac `fn = assemble_function st st'` >>
  `fn.fn_name = st.cs_current_bb` by simp[assemble_function_def, Abbr `fn`] >>
  `fn.fn_blocks = assemble_blocks st'` by simp[assemble_function_def, Abbr `fn`] >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  `¬ss0.vs_halted` by simp[Abbr `ss0`] >>
  `ss0.vs_current_bb = st.cs_current_bb` by simp[Abbr `ss0`] >>
  `ss0.vs_inst_idx = LENGTH st.cs_current_insts` by simp[Abbr `ss0`] >>
  `ss0.vs_current_bb = bb.bb_label` by simp[] >>
  qexistsl [`SUC fuel`,`jump_to target_lbl ss0`] >>
  reverse conj_tac >- (
    fs[jump_to_def,Abbr `ss0`,observable_equiv_def,
       fresh_vars_wrt_def,compile_state_ok_def]) >>
  (* Main: run_compiled_fragment = OK *)
  `exec_block (SUC fuel) ctx bb ss0 = OK (jump_to target_lbl ss0)`
    by (simp[Abbr `ss0`,Once exec_block_def,step_inst_non_invoke,
             mk_inst_def,step_jmp_behavior,is_terminator_def,jump_to_def]) >>
  simp[Abbr `fn`,run_compiled_fragment_def,assemble_function_def] >>
  gvs[AllCaseEqs(),jump_to_def,Abbr `ss0`,exec_block_OK_not_halted] >>
  simp[run_fragment_blocks_def]
QED

(* If two functions have the same fn_blocks, run_fragment_blocks produces the
   same result — it only accesses fn.fn_blocks, never fn.fn_name. *)
Theorem run_fragment_blocks_fn_blocks_cong[local]:
  !fuel ctx fn1 fn2 ss.
    fn1.fn_blocks = fn2.fn_blocks ==>
    run_fragment_blocks fuel ctx fn1 ss = run_fragment_blocks fuel ctx fn2 ss
Proof
  Induct_on `fuel` >> rpt gen_tac >> strip_tac >>
  simp[run_fragment_blocks_def] >>
  Cases_on `lookup_block ss.vs_current_bb fn2.fn_blocks` >> gvs[] >>
  Cases_on `exec_block fuel ctx x (ss with vs_inst_idx := 0)` >> gvs[] >>
  IF_CASES_TAC >> gvs[]
QED

(* JMP to external label: run_fragment_blocks processes the JMP block,
   then exits OK since the target label is not in fn_blocks. *)
Theorem run_fragment_blocks_jmp_external:
  !fuel ctx fn ss target_lbl jmp_id bb.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = [mk_inst jmp_id JMP [Label target_lbl] []] /\
    ss.vs_inst_idx = 0 /\
    ~ss.vs_halted /\
    lookup_block target_lbl fn.fn_blocks = NONE
    ==>
    run_fragment_blocks (SUC (SUC fuel)) ctx fn ss = OK (jump_to target_lbl ss)
Proof
  rpt strip_tac >> simp[Once run_fragment_blocks_def] >>
  `get_instruction bb 0 = SOME (mk_inst jmp_id JMP [Label target_lbl] [])` by simp[get_instruction_def] >> drule exec_block_jmp_at_zero >> simp[jump_to_def] >> strip_tac >> gvs[] >> Cases_on `exec_block (SUC fuel) ctx bb ss` >> gvs[] >>
  simp[Once run_fragment_blocks_def]
QED


(* Entry block JNZ branch: if the entry block of a compiled fragment contains
   pure instructions starting at offset entry_idx, followed by a JNZ terminator,
   then run_compiled_fragment branches to the appropriate label and continues
   with run_fragment_blocks from there. *)
Theorem fragment_entry_jnz_branch_correct[local]:
  ∀ctx st st' ss fuel bb insts ss1 cond_op cond_v lbl_nz lbl_z jnz_id idx.
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    run_inst_seq insts (ss with <|vs_current_bb := st.cs_current_bb; vs_inst_idx := idx|>) = OK ss1 ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb (idx + k) = SOME (EL k insts)) ∧
    get_instruction bb (idx + LENGTH insts) =
      SOME (mk_inst jnz_id JNZ [cond_op; Label lbl_nz; Label lbl_z] []) ∧
    eval_operand cond_op ss1 = SOME cond_v ∧
    ¬ss1.vs_halted ∧
    idx = LENGTH st.cs_current_insts
    ⇒
    run_compiled_fragment ctx st st' ss fuel =
      if cond_v ≠ 0w then
        run_fragment_blocks fuel ctx (assemble_function st st') (jump_to lbl_nz ss1)
      else run_fragment_blocks fuel ctx (assemble_function st st') (jump_to lbl_z ss1)
Proof
  rpt strip_tac >>
  `run_compiled_fragment ctx st st' ss fuel =
    case exec_block fuel ctx bb
          (ss with <|vs_current_bb := st.cs_current_bb;
                     vs_inst_idx := LENGTH st.cs_current_insts|>) of
      OK ss' => if ss'.vs_halted then Halt ss'
               else run_fragment_blocks fuel ctx (assemble_function st st') ss'
    | Halt ss' => Halt ss'
    | Abort a ss' => Abort a ss'
    | IntRet vals ss' => IntRet vals ss'
    | Error e => Error e`
    by simp[run_compiled_fragment_def, assemble_function_def] >>
  qspecl_then [`insts`,`fuel`,`ctx`,`bb`,`LENGTH st.cs_current_insts`,
               `ss with <|vs_current_bb := st.cs_current_bb;
                           vs_inst_idx := LENGTH st.cs_current_insts|>`,
               `ss1`,`cond_op`,`cond_v`,`lbl_nz`,`lbl_z`,`jnz_id`]
    mp_tac exec_block_inst_seq_jnz >>
  simp[] >> strip_tac >> gvs[jump_to_def] >>
  Cases_on `cond_v ≠ 0w` >> gvs[jump_to_def]
QED

(* Single-instruction specialization of fragment_entry_jnz_branch_correct.
   Eliminates EVERY/LENGTH insts/idx matching noise for the common case
   of one pure instruction followed by JNZ. *)
Theorem fragment_entry_one_eq_jnz_branch_correct[local]:
  ∀ctx st st' ss fuel bb eq_inst ss1 cond_op cond_v lbl_nz lbl_z jnz_id.
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    run_inst_seq [eq_inst]
      (ss with <|vs_current_bb := st.cs_current_bb;
                  vs_inst_idx := LENGTH st.cs_current_insts|>) = OK ss1 ∧
    ¬is_terminator eq_inst.inst_opcode ∧
    eq_inst.inst_opcode ≠ INVOKE ∧
    get_instruction bb (LENGTH st.cs_current_insts) = SOME eq_inst ∧
    get_instruction bb (LENGTH st.cs_current_insts + 1) =
      SOME (mk_inst jnz_id JNZ [cond_op; Label lbl_nz; Label lbl_z] []) ∧
    eval_operand cond_op ss1 = SOME cond_v ∧
    ¬ss1.vs_halted
    ⇒
    run_compiled_fragment ctx st st' ss fuel =
      if cond_v ≠ 0w then
        run_fragment_blocks fuel ctx (assemble_function st st') (jump_to lbl_nz ss1)
      else run_fragment_blocks fuel ctx (assemble_function st st') (jump_to lbl_z ss1)
Proof
  rpt strip_tac >>
  `run_compiled_fragment ctx st st' ss fuel =
    case exec_block fuel ctx bb
          (ss with <|vs_current_bb := st.cs_current_bb;
                     vs_inst_idx := LENGTH st.cs_current_insts|>) of
      OK ss' => if ss'.vs_halted then Halt ss'
               else run_fragment_blocks fuel ctx (assemble_function st st') ss'
    | Halt ss' => Halt ss'
    | Abort a ss' => Abort a ss'
    | IntRet vals ss' => IntRet vals ss'
    | Error e => Error e`
    by simp[run_compiled_fragment_def, assemble_function_def] >>
  qspecl_then [`[eq_inst]`,`fuel`,`ctx`,`bb`,
    `LENGTH st.cs_current_insts`,
    `ss with <|vs_current_bb := st.cs_current_bb;
               vs_inst_idx := LENGTH st.cs_current_insts|>`,
    `ss1`,`cond_op`,`cond_v`,`lbl_nz`,`lbl_z`,`jnz_id`]
    mp_tac exec_block_inst_seq_jnz >>
  impl_tac >- (
    simp[is_terminator_def, listTheory.EVERY_DEF] ) >>
  simp[] >> strip_tac >> gvs[jump_to_def] >>
  Cases_on `cond_v ≠ 0w` >> gvs[jump_to_def]
QED


(* Helper: compile_selector_checks + JMP fallback_lbl.
   Proved by induction on selectors.
   The JMP fallback_lbl is emitted AFTER compile_selector_checks returns,
   which handles the base case (empty selectors → just JMP fallback_lbl). *)
Theorem compile_selector_checks_nil[local]:
  !method_id st. compile_selector_checks method_id [] st = ((), st)
Proof
  simp[compile_selector_checks_def, comp_return_def]
QED




Theorem compile_selector_checks_cons_eqn[local]:
  ∀method_id sel fn_label rest st st_mid.
    compile_selector_checks method_id ((sel,fn_label)::rest) st = ((),st_mid) ⇔
    ∃match_op cs1 match_lbl cs2 next_lbl cs3 cs4 old1 cs5 cs6 old2 cs7.
      emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
      fresh_label "match" cs1 = (match_lbl,cs2) ∧
      fresh_label "next" cs2 = (next_lbl,cs3) ∧
      emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
      new_block match_lbl cs4 = (old1,cs5) ∧
      emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
      new_block next_lbl cs6 = (old2,cs7) ∧
      compile_selector_checks method_id rest cs7 = ((),st_mid)
Proof
  simp[compile_selector_checks_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[])
QED
Theorem step_emit_chain_state_ok[local]:
  ∀method_id sel fn_label rest st st_mid match_op cs1 match_lbl cs2 next_lbl cs3 cs4.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    compile_state_ok st
    ⇒
    compile_state_ok cs4 ∧
    bound_labels cs4 = bound_labels st ∧
    cs4.cs_next_label = st.cs_next_label + 2 ∧
    label_external cs4 match_lbl ∧
    label_external cs4 next_lbl ∧
    next_lbl ≠ match_lbl
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    mp_tac (Q.SPECL [`cs2`,`cs4`,`match_lbl`] label_external_through_compile_ops) >>
    simp[bound_labels_emit_op_fresh_label_inst_subset] >> strip_tac >> simp[]) >>
  conj_tac >- (
    mp_tac (Q.SPECL [`cs3`,`cs4`,`next_lbl`] label_external_through_compile_ops) >>
    simp[bound_labels_emit_op_fresh_label_inst_subset] >> strip_tac >> simp[]) >>
  CCONTR_TAC >> fs[] >>
  drule fresh_label_output_inj >> simp[]
QED

Theorem step_chain_cs7_ok[local]:
  ∀method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3 cs4 old1 cs5 cs6 old2 cs7.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    new_block match_lbl cs4 = (old1,cs5) ∧
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
    new_block next_lbl cs6 = (old2,cs7) ∧
    compile_state_ok st
    ⇒
    compile_state_ok cs7 ∧
    bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st ∧
    cs7.cs_next_label = st.cs_next_label + 2
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_emit_chain_state_ok >> strip_tac >>
  first_x_assum (fn th => STRIP_ASSUME_TAC (SPEC_ALL th)) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  drule_all label_external_new_block_other >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  `label_external cs6 next_lbl` by (simp[label_external_def] >> qpat_x_assum `label_external cs5 next_lbl` mp_tac >> simp[label_external_def] >> rw[]) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  simp[]
QED

Theorem compile_selector_checks_bound_labels_mono[local]:
  !method_id selectors st st_mid.
    compile_selector_checks method_id selectors st = ((), st_mid) ∧
    compile_state_ok st
    ==>
    bound_labels st SUBSET bound_labels st_mid
Proof
  recInduct compile_selector_checks_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_selector_checks_nil])
  >> rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `compile_selector_checks _ (_::_) _ = ((),_)` mp_tac >>
  simp[compile_selector_checks_cons_eqn] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all step_chain_cs7_ok >> disch_tac >>
  pop_assum (STRIP_ASSUME_TAC o SPEC_ALL) >>
  `bound_labels st SUBSET bound_labels cs7`
    by (qpat_x_assum `bound_labels cs7 = _` SUBST1_TAC >>
        simp[pred_setTheory.INSERT_SUBSET, pred_setTheory.SUBSET_DEF,
             pred_setTheory.IN_INSERT]) >>
  first_x_assum (qspecl_then [`cs7`,`st_mid`] mp_tac) >>
  impl_tac >- simp[] >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Theorem step_new_block_chain_state_ok[local]:
  ∀method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3 cs4 old1 cs5 cs6 old2 cs7.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    new_block match_lbl cs4 = (old1,cs5) ∧
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
    new_block next_lbl cs6 = (old2,cs7) ∧
    compile_state_ok st ∧
    label_external st fn_label
    ⇒
    compile_state_ok cs7 ∧
    bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st ∧
    cs7.cs_next_label = st.cs_next_label + 2 ∧
    cs7.cs_current_bb = next_lbl ∧
    label_external cs7 fn_label
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_emit_chain_state_ok >> strip_tac >>
  first_x_assum (fn th => STRIP_ASSUME_TAC (SPEC_ALL th)) >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  `fn_label ≠ match_lbl` by (
    CCONTR_TAC >> fs[label_external_def] >>
    `fresh_label_output "match" st.cs_next_label ∈ compiler_labels_future st.cs_next_label`
      by (irule fresh_label_output_in_compiler_labels_future >> decide_tac) >>
    metis_tac[]) >>
  `fn_label ≠ next_lbl` by (
    CCONTR_TAC >> fs[label_external_def] >>
    `fresh_label_output "next" cs2.cs_next_label ∈ compiler_labels_future st.cs_next_label`
      by (irule fresh_label_output_in_compiler_labels_future >> simp[]) >>
    metis_tac[]) >>
  `label_external cs4 fn_label` by (
    mp_tac (Q.SPECL [`st`,`cs4`,`fn_label`] label_external_through_compile_ops) >>
    simp[bound_labels_emit_op_fresh_label_inst_subset] >> decide_tac) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  `label_external cs5 fn_label` by (
    mp_tac (Q.SPECL [`fn_label`,`match_lbl`,`cs4`,`cs5`,`old1`] label_external_new_block_other) >>
    simp[]) >>
  `label_external cs5 next_lbl` by (
    mp_tac (Q.SPECL [`next_lbl`,`match_lbl`,`cs4`,`cs5`,`old1`] label_external_new_block_other) >>
    simp[]) >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  `label_external cs6 fn_label` by (
    mp_tac (Q.SPECL [`cs5`,`cs6`,`fn_label`] label_external_through_compile_ops) >>
    simp[bound_labels_emit_op_fresh_label_inst_subset] >> decide_tac) >>
  `label_external cs6 next_lbl` by (
    mp_tac (Q.SPECL [`cs5`,`cs6`,`next_lbl`] label_external_through_compile_ops) >>
    simp[bound_labels_emit_op_fresh_label_inst_subset] >> decide_tac) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  `label_external cs7 fn_label` by (
    mp_tac (Q.SPECL [`fn_label`,`next_lbl`,`cs6`,`cs7`,`old2`] label_external_new_block_other) >>
    simp[]) >>
  simp[]
QED

Theorem compile_selector_checks_bound_labels:
  ∀ method_id selectors st st_mid.
  compile_selector_checks method_id selectors st = ((), st_mid) ∧
  compile_state_ok st
  ⇒
  bound_labels st_mid ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
  st_mid.cs_next_label ≥ st.cs_next_label ∧
  compile_state_ok st_mid
Proof
  recInduct compile_selector_checks_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_selector_checks_nil, SUBSET_LEFT_UNION])
  >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`method_id`,`sel`,`fn_label`,`rest`,`st`,`st_mid`] compile_selector_checks_cons_eqn) >>
  simp[] >> strip_tac >>
  drule_all step_chain_cs7_ok >> disch_tac >>
  pop_assum (STRIP_ASSUME_TAC o SPEC_ALL) >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  `match_lbl ∈ compiler_labels_future st.cs_next_label` by (
    simp[] >> irule fresh_label_output_in_compiler_labels_future >> decide_tac) >>
  `next_lbl ∈ compiler_labels_future st.cs_next_label` by (
    simp[] >> irule fresh_label_output_in_compiler_labels_future >> decide_tac) >>
  `bound_labels cs7 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label` by (
    qpat_x_assum `bound_labels cs7 = _` SUBST1_TAC >>
    rewrite_tac [pred_setTheory.INSERT_SUBSET] >>
    conj_tac >- simp[pred_setTheory.IN_UNION] >>
    rewrite_tac [pred_setTheory.INSERT_SUBSET] >>
    conj_tac >- simp[pred_setTheory.IN_UNION] >>
    irule SUBSET_LEFT_UNION >> simp[pred_setTheory.SUBSET_DEF]) >>
  qpat_x_assum `∀st st_mid. compile_selector_checks _ _ st = _ ∧ _ ⇒ _`
    (fn th => mp_tac (SPECL [``cs7:compile_state``, ``st_mid:compile_state``] th)) >>
  simp[] >> strip_tac >>
  irule bound_labels_subset_trans >>
  qexists `cs7` >> simp[]
QED

Theorem compile_selector_checks_blocks_preserved:
  !method_id selectors st st_mid lbl bb.
    compile_selector_checks method_id selectors st = ((), st_mid) /\
    compile_state_ok st /\
    FIND (\b. b.bb_label = lbl) st.cs_blocks = SOME bb /\
    lbl NOTIN compiler_labels_future st.cs_next_label /\
    lbl <> st.cs_current_bb
    ==>
    FIND (\b. b.bb_label = lbl) st_mid.cs_blocks = SOME bb
Proof
  recInduct compile_selector_checks_ind >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_selector_checks_nil])
  >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`method_id`,`sel`,`fn_label`,`rest`,`st`,`st_mid`] compile_selector_checks_cons_eqn) >>
  simp[] >> strip_tac >>
  imp_res_tac step_emit_chain_state_ok >>
  drule_all step_chain_cs7_ok >> disch_tac >>
  pop_assum (STRIP_ASSUME_TAC o SPEC_ALL) >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  imp_res_tac compile_state_ok_emit_inst >>
  `match_lbl IN compiler_labels_future st.cs_next_label` by (
    simp[] >> irule fresh_label_output_in_compiler_labels_future >> decide_tac) >>
  `next_lbl IN compiler_labels_future st.cs_next_label` by (
    simp[] >> irule fresh_label_output_in_compiler_labels_future >> simp[]) >>
  imp_res_tac new_block_props >>
  `compile_state_ok cs5` by metis_tac[compile_state_ok_new_block] >>
  imp_res_tac compile_state_ok_emit_inst >>
  `lbl <> match_lbl /\ lbl <> next_lbl` by metis_tac[label_external_neq_compiler_label,
    label_external_def, compile_state_ok_def] >>
  `cs4.cs_current_bb = st.cs_current_bb` by (fs[] >> decide_tac) >>
  `cs6.cs_current_bb = match_lbl` by fs[] >>
  `FIND (\b. b.bb_label = lbl) cs5.cs_blocks = SOME bb` by (
    gvs[listTheory.FIND_thm]) >>
  `FIND (\b. b.bb_label = lbl) cs6.cs_blocks = SOME bb` by (
    gvs[listTheory.FIND_thm]) >>
  `FIND (\b. b.bb_label = lbl) cs7.cs_blocks = SOME bb` by (
    gvs[listTheory.FIND_thm]) >>
  `compiler_labels_future cs7.cs_next_label SUBSET compiler_labels_future st.cs_next_label` by
    simp[compiler_labels_future_mono] >>
  `lbl NOTIN compiler_labels_future cs7.cs_next_label` by (
    CCONTR_TAC >> fs[pred_setTheory.SUBSET_DEF]) >>
  `lbl <> cs7.cs_current_bb` by metis_tac[label_external_neq_compiler_label,
    label_external_def, compile_state_ok_def] >>
  qpat_x_assum `∀st st_mid lbl bb. compile_selector_checks _ _ st = _ ∧ _ ⇒ _`
    (fn th => mp_tac (SPECL [``cs7:compile_state``, ``st_mid:compile_state``] th)) >>
  strip_tac >> first_x_assum irule >> simp[]
QED

Theorem lookup_block_prepend[local]:
  ∀lbl b l.
    b.bb_label ≠ lbl ⇒
    lookup_block lbl (b :: l) = lookup_block lbl l
Proof
  rw[lookup_block_def, listTheory.FIND_thm]
QED


Theorem bound_labels_not_in_future:
  ∀st lbl. compile_state_ok st ∧ lbl ∈ bound_labels st ⇒ lbl ∉ compiler_labels_future st.cs_next_label
Proof
  rw[compile_state_ok_def, pred_setTheory.DISJOINT_ALT]
QED

Theorem step_emit_chain_current_bb[local]:
  ∀method_id sel st match_op cs1 match_lbl cs2 next_lbl cs3 cs4.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    compile_state_ok st
    ⇒
    cs4.cs_current_bb = st.cs_current_bb ∧ cs4.cs_blocks = st.cs_blocks
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac compile_state_ok_emit_op >>
  imp_res_tac fresh_label_produces_external >>
  imp_res_tac fresh_label_produces_external >>
  imp_res_tac compile_state_ok_emit_inst >>
  simp[]
QED

Theorem selector_step_entry_block_preserved:
  ∀method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3 cs4 old1 cs5 cs6 old2 cs7 st_mid st' fallback_lbl.
  emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
  fresh_label "match" cs1 = (match_lbl,cs2) ∧
  fresh_label "next" cs2 = (next_lbl,cs3) ∧
  emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
  new_block match_lbl cs4 = (old1,cs5) ∧
  emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
  new_block next_lbl cs6 = (old2,cs7) ∧
  compile_selector_checks method_id rest cs7 = ((), st_mid) ∧
  emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') ∧
  compile_state_ok st ∧
  label_external st fn_label ∧
  label_external st fallback_lbl ∧
  EVERY (label_external st) (MAP SND rest)
  ⇒
  FIND (λb. b.bb_label = st.cs_current_bb) st'.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs4.cs_current_insts|>
Proof
  rpt gen_tac >> strip_tac >>
  drule_all step_emit_chain_current_bb >> strip_tac >>
  drule_all step_emit_chain_state_ok >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all step_chain_cs7_ok >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all compile_selector_checks_bound_labels >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  `st.cs_current_bb ∈ bound_labels st` by simp[bound_labels_def] >>
  `st.cs_current_bb ∈ bound_labels cs7` by (
    qpat_x_assum `bound_labels cs7 = _` SUBST1_TAC >> simp[]) >>
  `st.cs_current_bb ∉ compiler_labels_future cs7.cs_next_label` by
    metis_tac[bound_labels_not_in_future] >>
  `cs7.cs_current_bb = next_lbl` by metis_tac[new_block_props] >>
  `next_lbl ∉ bound_labels st` by metis_tac[label_external_def] >>
  `st.cs_current_bb ≠ cs7.cs_current_bb` by metis_tac[] >>
  `compile_state_ok cs5` by metis_tac[compile_state_ok_new_block] >>
  `cs6.cs_blocks = cs5.cs_blocks` by metis_tac[compile_state_ok_emit_inst] >>
  `cs5.cs_current_bb = match_lbl` by metis_tac[new_block_props] >>
  `cs6.cs_current_bb = match_lbl` by metis_tac[compile_state_ok_emit_inst] >>
  `match_lbl ∉ bound_labels cs4` by metis_tac[label_external_def] >>
  `match_lbl ≠ st.cs_current_bb` by metis_tac[] >>
  `FIND (λb. b.bb_label = cs4.cs_current_bb) cs5.cs_blocks =
    SOME <|bb_label := cs4.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by
    metis_tac[new_block_creates_assembled_block] >>
  `cs7.cs_blocks = <|bb_label := cs6.cs_current_bb; bb_instructions := cs6.cs_current_insts|> :: cs6.cs_blocks` by
    metis_tac[new_block_props] >>
  `FIND (λb. b.bb_label = st.cs_current_bb) cs7.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by
    gvs[listTheory.FIND_thm] >>
  metis_tac[compile_selector_checks_blocks_preserved]
QED

Theorem selector_step_match_block_preserved:
  ∀method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3 cs4 old1 cs5 cs6 old2 cs7 st_mid st' fallback_lbl.
  emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
  fresh_label "match" cs1 = (match_lbl,cs2) ∧
  fresh_label "next" cs2 = (next_lbl,cs3) ∧
  emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
  new_block match_lbl cs4 = (old1,cs5) ∧
  emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
  new_block next_lbl cs6 = (old2,cs7) ∧
  compile_selector_checks method_id rest cs7 = ((), st_mid) ∧
  emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') ∧
  compile_state_ok st ∧
  label_external st fn_label ∧
  label_external st fallback_lbl ∧
  EVERY (label_external st) (MAP SND rest)
  ⇒
  FIND (λb. b.bb_label = match_lbl) st'.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>
Proof
  rpt strip_tac >>
  drule_all step_emit_chain_current_bb >> strip_tac >> gvs[] >>
  drule_all step_emit_chain_state_ok >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all step_chain_cs7_ok >> disch_then (strip_assume_tac o SPEC_ALL) >>
  drule_all compile_selector_checks_bound_labels >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  `match_lbl ∈ bound_labels cs7` by (
  qpat_x_assum `bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st`
    (fn th => simp[th])) >>
`match_lbl ∉ compiler_labels_future cs7.cs_next_label` by (
    qspecl_then [`cs7`,`match_lbl`] mp_tac bound_labels_not_in_future >> simp[]) >>
  `cs5.cs_current_bb = match_lbl ∧ cs5.cs_current_insts = []` by metis_tac[new_block_props] >>
  `compile_state_ok cs5` by metis_tac[compile_state_ok_new_block] >>
  `cs6.cs_current_bb = match_lbl` by metis_tac[compile_state_ok_emit_inst] >>
  `cs6.cs_blocks = cs5.cs_blocks` by metis_tac[compile_state_ok_emit_inst] >>
  `cs7.cs_current_bb = next_lbl` by metis_tac[new_block_props] >>
  `match_lbl ≠ cs7.cs_current_bb` by metis_tac[] >>
  `cs7.cs_blocks = <|bb_label := cs6.cs_current_bb; bb_instructions := cs6.cs_current_insts|> :: cs6.cs_blocks` by metis_tac[new_block_props] >>
  `FIND (λb. b.bb_label = match_lbl) cs7.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>` by gvs[listTheory.FIND_thm] >>
  metis_tac[compile_selector_checks_blocks_preserved]
QED

(* HOL4 multi-field record updates <|f1:=v1; f2:=v2|> are a single n-ary op,
   not nested single-field updates. irule/metis can't match single-field
   against multi-field. These decomposition lemmas bridge the gap.
   Two versions for both field orderings that gvs may produce. *)
Theorem venom_state_update_bb_idx_decompose[local]:
  !ss lbl n.
    ss with <|vs_current_bb := lbl; vs_inst_idx := n|> =
    (ss with vs_current_bb := lbl) with vs_inst_idx := n
Proof
  simp[]
QED

Theorem venom_state_update_idx_bb_decompose[local]:
  !ss lbl n.
    ss with <|vs_inst_idx := n; vs_current_bb := lbl|> =
    (ss with vs_current_bb := lbl) with vs_inst_idx := n
Proof
  simp[]
QED

Theorem assemble_function_fn_blocks_irrel[local]:
  ∀st1 st2 st'.
    (assemble_function st1 st').fn_blocks = (assemble_function st2 st').fn_blocks
Proof
  simp[assemble_function_def]
QED

(* Specialized version of exec_block_inst_seq_prefix starting at idx=0.
   Avoids the 0+LENGTH vs LENGTH mismatch that first-order unification
   can't handle. *)
Theorem exec_block_inst_seq_prefix_0[local]:
  ∀insts fuel ctx bb ss ss'.
    run_inst_seq insts ss = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb k = SOME (EL k insts))
    ⇒ exec_block fuel ctx bb (ss with vs_inst_idx := 0) =
        exec_block fuel ctx bb (ss' with vs_inst_idx := LENGTH insts)
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb (ss with vs_inst_idx := 0) =
    exec_block fuel ctx bb (ss' with vs_inst_idx := 0 + LENGTH insts)`
    by (irule exec_block_inst_seq_prefix >> simp[]) >>
  simp[]
QED

(* When ss.vs_current_bb = lbl, the update is idempotent. *)
Theorem vs_current_bb_update_eq[local]:
  ∀ss lbl. ss.vs_current_bb = lbl ⇒ ss with vs_current_bb := lbl = ss
Proof
  simp[venom_state_component_equality]
QED

(* When ss.vs_inst_idx = n, the update is idempotent. *)
Theorem vs_inst_idx_update_eq[local]:
  ∀ss n. ss.vs_inst_idx = n ⇒ ss with vs_inst_idx := n = ss
Proof
  simp[venom_state_component_equality]
QED

(* Introducing a redundant vs_inst_idx := 0 on a state where vs_inst_idx = 0 *)
Theorem vs_inst_idx_redundant_0[local]:
  ∀ss. ss.vs_inst_idx = 0 ⇒ ss = ss with vs_inst_idx := 0
Proof
  simp[venom_state_component_equality]
QED

(* exec_block prefix lemma: if we run instructions starting from
   vs_inst_idx = 0 on a state with vs_current_bb set, the result equals
   running exec_block from the post-execution state at index LENGTH insts.
   Forward reasoning approach: instantiate exec_block_inst_seq_prefix with
   ss := ss with vs_current_bb := lbl, idx := 0, then simplify using
   venom_state_component_equality to normalize record updates. *)
Theorem exec_block_prefix_from_bb_update[local]:
  ∀insts fuel ctx bb ss ss' lbl.
    run_inst_seq insts (ss with vs_current_bb := lbl) = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb k = SOME (EL k insts)) ∧
    ss.vs_inst_idx = 0 ∧
    ss'.vs_current_bb = lbl
    ⇒ exec_block fuel ctx bb (ss with vs_current_bb := lbl) =
        exec_block fuel ctx bb
          (ss' with <|vs_current_bb := lbl; vs_inst_idx := LENGTH insts|>)
Proof
  rpt strip_tac >>
  qabbrev_tac `ss0 = ss with vs_current_bb := lbl` >>
  qabbrev_tac `ss1 = ss' with <|vs_current_bb := lbl; vs_inst_idx := LENGTH insts|>` >>
  `ss0.vs_inst_idx = 0` by simp[Abbr `ss0`] >>
  `ss1.vs_inst_idx = LENGTH insts` by simp[Abbr `ss1`] >>
  `ss1.vs_current_bb = lbl` by simp[Abbr `ss1`] >>
  `run_inst_seq insts ss0 = OK ss'` by (
    simp[Abbr `ss0`, venom_state_component_equality]) >>
  `ss0 = ss0 with vs_inst_idx := 0` by simp[Abbr `ss0`, venom_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `exec_block fuel ctx bb (ss0 with vs_inst_idx := 0) =
    exec_block fuel ctx bb (ss' with vs_inst_idx := 0 + LENGTH insts)`
    by (irule exec_block_inst_seq_prefix >> simp[]) >>
  `ss' with vs_inst_idx := LENGTH insts = ss1`
    by (simp[Abbr `ss1`, venom_state_component_equality]) >>
  simp[]
QED

(* Generalized version: works at arbitrary instruction offset, not just idx=0.
   This is the key lemma for fragment_prefix_chain_gen. *)
Theorem exec_block_prefix_from_bb_update_gen[local]:
  ∀insts fuel ctx bb idx ss ss' lbl.
    run_inst_seq insts (ss with vs_current_bb := lbl) = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb (idx + k) = SOME (EL k insts)) ∧
    ss'.vs_current_bb = lbl
    ⇒ exec_block fuel ctx bb
        (ss with <|vs_current_bb := lbl; vs_inst_idx := idx|>) =
       exec_block fuel ctx bb
        (ss' with <|vs_current_bb := lbl; vs_inst_idx := idx + LENGTH insts|>)
Proof
  rpt strip_tac >>
  qabbrev_tac `ss0 = ss with vs_current_bb := lbl` >>
  `run_inst_seq insts ss0 = OK ss'`
    by simp[Abbr `ss0`, venom_state_component_equality] >>
  `exec_block fuel ctx bb (ss0 with vs_inst_idx := idx) =
    exec_block fuel ctx bb (ss' with vs_inst_idx := idx + LENGTH insts)`
    by (irule exec_block_inst_seq_prefix >> simp[]) >>
  `ss0 with vs_inst_idx := idx = ss with <|vs_current_bb := lbl; vs_inst_idx := idx|>`
    by simp[Abbr `ss0`, venom_state_component_equality] >>
  `ss' with vs_inst_idx := idx + LENGTH insts =
    ss' with <|vs_current_bb := lbl; vs_inst_idx := idx + LENGTH insts|>`
    by simp[venom_state_component_equality] >>
  metis_tac[]
QED

(* Fragment prefix chain: if cs_pre has empty current_insts and cs_post has
   insts as current_insts (both in the same block), then rcf with cs_pre
   starting from ss0 equals rcf with cs_post starting from the state reached
   after executing the prefix instructions.

   Proof strategy:
   1. simp[run_compiled_fragment_def] — expand both rcf sides to exec_result_CASE
   2. Cases_on lookup_block — eliminate NONE case
   3. pure_once_rewrite_tac[venom_state_update_bb_idx_decompose] — convert
      multi-field record updates to nested single-field form
   4. irule exec_result_case_cong >> simp[] — reduce to scrutinee equality
   5. irule exec_block_inst_seq_prefix_0 >> simp[vs_current_bb_update_eq] *)
Theorem fragment_prefix_chain[local]:
  ∀ctx cs_pre cs_post st' ss0 ss_inner fuel bb insts.
    cs_pre.cs_current_bb = cs_post.cs_current_bb ∧
    cs_pre.cs_current_insts = [] ∧
    cs_post.cs_current_insts = insts ∧
    same_blocks cs_pre cs_post ∧
    compile_state_ok cs_pre ∧
    fresh_vars_wrt cs_pre ss0 ∧
    fresh_vars_wrt cs_post ss_inner ∧
    lookup_block cs_pre.cs_current_bb (assemble_blocks st') = SOME bb ∧
    ss0.vs_inst_idx = 0 ∧
    run_inst_seq insts (ss0 with vs_current_bb := cs_pre.cs_current_bb) = OK ss_inner ∧
    ss_inner.vs_current_bb = cs_pre.cs_current_bb ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb k = SOME (EL k insts)) ∧
    ¬ss0.vs_halted ∧
    ¬ss_inner.vs_halted
    ⇒
    run_compiled_fragment ctx cs_pre st' ss0 fuel =
    run_compiled_fragment ctx cs_post st' ss_inner fuel
Proof
  rpt strip_tac >>
  `assemble_function cs_pre st' = assemble_function cs_post st'`
    by simp[assemble_function_def] >>
  pure_once_rewrite_tac[rcf_state_normalize] >>
  simp[run_compiled_fragment_def, assemble_function_def] >>
  Cases_on `lookup_block cs_post.cs_current_bb (assemble_blocks st')` >> gvs[] >>
  irule exec_result_case_cong >> simp[] >>
  irule exec_block_prefix_from_bb_update >> simp[]
QED
(* ===== Selector Dispatch ===== *)
(* Linear dispatch creates blocks that jump to fallback_lbl or fn_labels
   from the selector list. These are external labels (fn bodies, fallback
   handler) assembled separately. The fragment exits to one of them.

   HYPOTHESES (added 2026-04-17 after counterexample):
   - compile_state_ok st: pre-state has well-formed label bindings
   - label_external st fallback_lbl: fallback label is not already bound
     in st and wasn't allocated by a future fresh_label (so
     compile_selector_dispatch_linear cannot reuse it for an internal
     @dispatch_/@match_/@next_ label)
   - EVERY (label_external st) (MAP SND selectors): same for per-fn labels
   - ALL_DISTINCT (fallback_lbl :: MAP SND selectors): no two external
     labels collide (so JNZ to one doesn't accidentally equal another) *)

Theorem bound_labels_fresh_label[local]:
  ∀st suffix lbl st'.
    fresh_label suffix st = (lbl, st') ⇒ bound_labels st' = bound_labels st
Proof
  rpt strip_tac >>
  gvs[fresh_label_def, bound_labels_def, compile_state_component_equality]
QED

Theorem compile_state_ok_fresh_label[local]:
  ∀st suffix lbl st'.
    fresh_label suffix st = (lbl, st') ∧ compile_state_ok st
    ⇒ compile_state_ok st' ∧ bound_labels st' = bound_labels st ∧
      st'.cs_blocks = st.cs_blocks ∧ st'.cs_current_bb = st.cs_current_bb ∧
      st'.cs_next_id = st.cs_next_id ∧ st'.cs_next_var = st.cs_next_var ∧
      st'.cs_current_insts = st.cs_current_insts
Proof
  rpt strip_tac >>
  (* Derive bound_labels equality BEFORE gvs destroys the fresh_label equation *)
  drule bound_labels_fresh_label >> strip_tac >>
  gvs[compile_state_ok_def, fresh_label_def, compile_state_component_equality] >>
  irule pred_setTheory.DISJOINT_SUBSET >>
  qexists_tac `compiler_labels_future st.cs_next_label` >>
  simp[compiler_labels_future_mono]
QED

(* Boundary lemma: inst_extends through the emit_op → fresh_label → fresh_label → emit_inst
   chain in selector step. Proved as a standalone lemma so the consumer
   (selector_step_dispatch_block) can use a single irule in large context. *)
Theorem step_emit_chain_inst_extends[local]:
  ∀method_id sel st match_op cs1 match_lbl cs2 next_lbl cs3 cs4.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    compile_state_ok st
    ⇒ inst_extends st cs4
Proof
  rpt gen_tac >> strip_tac >>
  `compile_state_ok cs1` by metis_tac[compile_state_ok_emit_op] >>
  `compile_state_ok cs2` by metis_tac[compile_state_ok_fresh_label] >>
  `inst_extends st cs1` by metis_tac[inst_extends_emit_op] >>
  `inst_extends cs1 cs2` by metis_tac[inst_extends_fresh_label] >>
  `inst_extends cs2 cs3` by metis_tac[inst_extends_fresh_label] >>
  `inst_extends cs3 cs4` by metis_tac[inst_extends_emit_inst] >>
  metis_tac[inst_extends_trans]
QED

(* emit_inst and emit_op preserve label_external because they don't change
   cs_blocks, cs_current_bb, or cs_next_label. *)
Theorem label_external_emit_inst[local]:
  ∀opc ops outs st st' lbl.
    emit_inst opc ops outs st = ((),st') ∧ label_external st lbl
    ⇒ label_external st' lbl
Proof
  rpt strip_tac >> drule emit_inst_extends >> strip_tac >>
  gvs[label_external_def, bound_labels_def]
QED

(* emit_op preserves label_external because it doesn't change cs_blocks,
   cs_current_bb, or cs_next_label (per compile_state_ok_emit_op). *)
Theorem label_external_emit_op[local]:
  ∀opc ops st v st' lbl.
    emit_op opc ops st = (v,st') ∧ compile_state_ok st ∧ label_external st lbl
    ⇒ label_external st' lbl
Proof
  rpt strip_tac >> drule compile_state_ok_emit_op >> strip_tac >>
  gvs[label_external_def, bound_labels_def]
QED

(* Standalone helper: label_external is preserved when same_blocks holds and
   cs_next_label is monotone. Avoids irule label_external_mono + simp[bound_labels_def,
   label_external_def, same_blocks_def] which LOOPS in 20+ assumption context. *)
Theorem label_external_same_blocks[local]:
  ∀st st' lbl.
    label_external st lbl ∧ same_blocks st st' ∧ st.cs_next_label ≤ st'.cs_next_label
    ⇒ label_external st' lbl
Proof
  rpt strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb` by metis_tac[same_blocks_def] >>
  `st'.cs_blocks = st.cs_blocks` by metis_tac[same_blocks_def] >>
  `bound_labels st' = bound_labels st` by simp[bound_labels_def] >>
  `lbl ∉ bound_labels st'` by metis_tac[label_external_def, bound_labels_def] >>
  `lbl ∉ compiler_labels_future st'.cs_next_label` by (
    qpat_x_assum `label_external _ _` mp_tac >>
    simp[label_external_def, compiler_labels_future_def] >>
    rpt strip_tac >> CCONTR_TAC >>
    fs[pred_setTheory.IN_GSPEC_IFF] >> metis_tac[arithmeticTheory.LE_TRANS]) >>
  simp[label_external_def]
QED
(* bound_labels_emit_op/inst are REDUNDANT — already covered by
   compile_state_ok_emit_op/inst from emitHelperProps. *)



(* Batch invariant lemma for linear dispatch entry prefix.
   Proves the compile_state_ok and key structural facts, but delegates
   the subset chain for bound_labels/label_external to simpler lemmas. *)
Theorem SUBSET_INSERT_self[local]:
  ∀x s. s ⊆ x INSERT s
Proof
  simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_INSERT]
QED
Theorem linear_dispatch_prefix_next_var_mono[local]:
  ∀st fallback_lbl cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5
    old_lbl cs6 raw cs7 method_id cs8.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
    emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
    new_block dispatch_lbl cs5 = (old_lbl,cs6) ∧
    emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
    emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8)
    ⇒
    cs8.cs_next_var ≥ st.cs_next_var
Proof
  rpt gen_tac >> strip_tac >>
  dxrule emitted_insts_emit_op >> strip_tac >>
  dxrule emitted_insts_emit_op >> strip_tac >>
  dxrule emitted_insts_emit_op >> strip_tac >>
  dxrule fresh_label_props >> strip_tac >>
  dxrule emitted_insts_emit_inst >> strip_tac >>
  dxrule new_block_props >> strip_tac >>
  dxrule emitted_insts_emit_op >> strip_tac >>
  dxrule emitted_insts_emit_op >> strip_tac >>
  decide_tac
QED

Theorem linear_dispatch_prefix_invariants[local]:
  ∀st fallback_lbl cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5
    old_lbl cs6 raw cs7 method_id cs8.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
    emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
    new_block dispatch_lbl cs5 = (old_lbl,cs6) ∧
    emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
    emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
    compile_state_ok st ∧ label_external st fallback_lbl
  ⇒
    compile_state_ok cs8 ∧ compile_state_ok cs6 ∧ compile_state_ok cs3 ∧
    bound_labels st ⊆ bound_labels cs8 ∧
    bound_labels cs8 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    cs8.cs_next_label ≥ st.cs_next_label ∧
    cs8.cs_current_bb = dispatch_lbl ∧
    cs6.cs_current_bb = dispatch_lbl ∧
    cs6.cs_current_insts = [] ∧
    same_blocks cs6 cs8 ∧
    old_lbl = st.cs_current_bb ∧
    cs3.cs_blocks = st.cs_blocks ∧
    cs3.cs_current_bb = st.cs_current_bb ∧
    dispatch_lbl ≠ st.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all compile_state_ok_fresh_label >> strip_tac >>
  drule bound_labels_fresh_label >> strip_tac >>
  drule fresh_label_props >> strip_tac >>
  drule fresh_label_produces_external >> strip_tac >>
  `dispatch_lbl ≠ st.cs_current_bb` by (
    fs[label_external_def, bound_labels_def] >>
    metis_tac[pred_setTheory.IN_INSERT]) >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  `label_external cs5 dispatch_lbl` by (
    mp_tac (Q.SPECL [`cs4`,`cs5`,`dispatch_lbl`] label_external_through_compile_ops) >>
    simp[bound_labels_emit_op_fresh_label_inst_subset]) >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  imp_res_tac new_block_props >>
  asm_simp_tac (srw_ss()) [SUBSET_INSERT_self] >>
  conj_tac >- (disj2_tac >>
    irule fresh_label_output_in_compiler_labels_future >>
    decide_tac) >>
  (* same_blocks cs6 cs8: emit_ops preserve cs_blocks and cs_current_bb *)
  simp[same_blocks_def] >>
  decide_tac
QED




Theorem selector_step_preserves_next_var[local]:
  !method_id sel st match_op cs1 match_lbl cs2 next_lbl cs3 cs4
    old1 cs5 cs6 old2 cs7 fn_label.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) /\
    fresh_label "match" cs1 = (match_lbl,cs2) /\
    fresh_label "next" cs2 = (next_lbl,cs3) /\
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) /\
    new_block match_lbl cs4 = (old1,cs5) /\
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) /\
    new_block next_lbl cs6 = (old2,cs7)
    ==> cs7.cs_next_var = cs1.cs_next_var
Proof
  rpt strip_tac >>
  imp_res_tac fresh_label_props >>
  imp_res_tac emit_inst_extends >>
  imp_res_tac new_block_props >>
  fs[]
QED

Theorem compile_selector_checks_next_var_mono[local]:
  !method_id selectors st st_mid.
    compile_selector_checks method_id selectors st = ((), st_mid)
    ==> st_mid.cs_next_var >= st.cs_next_var
Proof
  recInduct compile_selector_checks_ind >> conj_tac
  >- (
    rpt strip_tac >>
    qpat_x_assum `compile_selector_checks _ [] _ = _` mp_tac >>
    simp[compile_selector_checks_def, comp_return_def]) >>
  rpt strip_tac >>
  qpat_x_assum `compile_selector_checks _ (_::_) _ = _` mp_tac >>
  simp[compile_selector_checks_cons_eqn] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  drule_all selector_step_preserves_next_var >> strip_tac >>
  first_x_assum (qspecl_then [`cs7`,`st_mid`] mp_tac) >> simp[] >>
  decide_tac
QED

(* compile_selector_dispatch_linear_correct: proved after compile_selector_checks_with_fallback_correct *)

(* Unfold compile_selector_dispatch_sparse when bucket_count ≤ 1.
   This reduces to linear-style selector checks + JMP fallback.
   Structurally identical to compile_selector_dispatch_linear_eqns
   but with 3-tuple selectors projected to 2-tuples. *)
Theorem compile_selector_dispatch_sparse_le1_eqns[local]:
  ∀selectors bucket_count fallback_lbl st st'.
    bucket_count ≤ 1 ⇒
    (compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st = ((),st') ⇔
    ∃cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5 old_lbl cs6
       raw cs7 method_id cs8 cs9.
      emit_op CALLDATASIZE [] st = (cds,cs1) ∧
      emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
      emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
      fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
      emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
      new_block dispatch_lbl cs5 = (old_lbl,cs6) ∧
      emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
      emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
      compile_selector_checks method_id (MAP (λ(sel,lbl,_). (sel,lbl)) selectors) cs8 = ((),cs9) ∧
      emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st'))
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compile_selector_dispatch_sparse_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  eq_tac >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[])
QED

(* compile_selector_dispatch_sparse_correct: proof deferred to after
   linear_dispatch infrastructure — see compile_selector_dispatch_sparse_correct_real below *)



(* ===== Kwargs Entry Point ===== *)
(* Compilation-equation lemma (forward direction only) for empty kwargs:
   When kwarg_vars = [], compile_init_kwargs is just return (),
   so the whole compilation reduces to CALLDATASIZE then JMP. *)
Theorem compile_entry_point_kwargs_nil_compile[local]:
  ∀ cenv calldata_offset kwargs_from_calldata common_label st st'.
    compile_entry_point_kwargs cenv [] calldata_offset
      kwargs_from_calldata common_label st = ((), st') ⇒
    ∃ hi_op st1. emit_op CALLDATASIZE [] st = (hi_op, st1) ∧
                 emit_inst JMP [Label common_label] [] st1 = ((), st')
Proof
  simp[compile_entry_point_kwargs_def, compile_init_kwargs_def,
       comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op CALLDATASIZE [] st` >> gvs[]
QED

(* Generalized fragment prefix chain: pure instructions added to a fragment's
   prefix shift the starting instruction pointer without changing the final
   result. This generalizes fragment_prefix_chain by removing the
   cs_current_insts = [] requirement: it works at an arbitrary offset
   within the current block.

   The key insight: run_compiled_fragment normalizes the starting state to
   (ss with <|vs_current_bb := entry_lbl; vs_inst_idx := entry_idx|>).
   Adding prefix_insts to cs_current_insts shifts entry_idx by their length.
   After executing the prefix, exec_block_inst_seq_prefix shows the block
   execution from (ss0 at idx) equals (ss_inner at idx+LENGTH prefix_insts). *)
Theorem fragment_prefix_chain_gen[local]:
  ∀ctx cs_pre cs_post st' ss0 ss_inner fuel bb prefix_insts.
    cs_pre.cs_current_bb = cs_post.cs_current_bb ∧
    cs_post.cs_current_insts = cs_pre.cs_current_insts ++ prefix_insts ∧
    same_blocks cs_pre cs_post ∧
    compile_state_ok cs_pre ∧
    fresh_vars_wrt cs_pre ss0 ∧
    fresh_vars_wrt cs_post ss_inner ∧
    lookup_block cs_pre.cs_current_bb (assemble_blocks st') = SOME bb ∧
    run_inst_seq prefix_insts
      (ss0 with vs_current_bb := cs_pre.cs_current_bb) = OK ss_inner ∧
    ss_inner.vs_current_bb = cs_pre.cs_current_bb ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) prefix_insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) prefix_insts ∧
    (∀k. k < LENGTH prefix_insts ⇒
          get_instruction bb (LENGTH cs_pre.cs_current_insts + k) =
            SOME (EL k prefix_insts)) ∧
    ¬ss0.vs_halted ∧
    ¬ss_inner.vs_halted
    ⇒
    run_compiled_fragment ctx cs_pre st' ss0 fuel =
    run_compiled_fragment ctx cs_post st' ss_inner fuel
Proof
  rpt strip_tac >>
  `assemble_function cs_pre st' = assemble_function cs_post st'`
    by simp[assemble_function_def] >>
  pure_once_rewrite_tac[rcf_state_normalize] >>
  simp[run_compiled_fragment_def, assemble_function_def] >>
  Cases_on `lookup_block cs_post.cs_current_bb (assemble_blocks st')` >> gvs[] >>
  irule exec_result_case_cong >> simp[] >>
  (* Rewrite ADD order to match lemma conclusion: idx + LENGTH insts *)
  qmatch_goalsub_abbrev_tac `LENGTH p + LENGTH c` >>
  `(LENGTH p:num) + (LENGTH c) = LENGTH c + LENGTH p`
    by decide_tac >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  irule exec_block_prefix_from_bb_update_gen >> simp[]
QED


(* ===== Argument Decoding (helpers only) ===== *)

Theorem compile_decode_args_nil:
  ∀ cenv offset load_opc hi_op base_adj st.
    compile_decode_args cenv [] offset load_opc hi_op base_adj st = ((), st)
Proof
  simp[compile_decode_args_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem compile_init_kwargs_nil:
  ∀ cenv offset from_cd hi_op st.
    compile_init_kwargs cenv [] offset from_cd hi_op st = ((), st)
Proof
  simp[compile_init_kwargs_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* ===== Entry Checks ===== *)

(* Helper: the calldatasize sub-check (4 instructions: CDS, LT, ISZERO, ASSERT)
   Either succeeds (OK) or reverts. Used in both entry_checks_correct cases. *)
Theorem compile_cds_check_ok_or_revert:
  ∀ min_cds st0 st1 st2 st3 st4 cds_v lt_v ok_v ss0.
    emit_op CALLDATASIZE [] st0 = (cds_v, st1) ∧
    emit_op LT [cds_v; Lit (n2w min_cds)] st1 = (lt_v, st2) ∧
    emit_op ISZERO [lt_v] st2 = (ok_v, st3) ∧
    emit_void ASSERT [ok_v] st3 = ((), st4) ∧
    fresh_vars_wrt st0 ss0
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st0 st4) ss0 = OK ss') ∨
      (run_inst_seq (emitted_insts st0 st4) ss0 = Abort Revert_abort ss')
Proof
  rpt strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  (* Step 1: CALLDATASIZE → OK ss1 *)
  drule_all emit_op_CALLDATASIZE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1` >>
  (* Step 2: LT → OK ss2 *)
  drule emit_op_LT_correct >> disch_then drule >>
  disch_then (qspec_then `n2w min_cds` mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  (* Extend: st0→st2 *)
  `run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 3: ISZERO → OK ss3 *)
  drule emit_op_ISZERO_correct >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st2 st3) ss2 = OK ss3` >>
  (* Extend: st0→st3 *)
  `run_inst_seq (emitted_insts st0 st3) ss0 = OK ss3`
    by (`inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
        imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  (* Step 4: ASSERT → OK or Abort *)
  drule emit_void_ASSERT_ok_or_revert >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[]
  (* OK case *)
  >- (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[] >> metis_tac[])
  (* Abort case *)
  >> (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[])
QED

(* Helper: the payable sub-check (3 instructions: CALLVALUE, ISZERO, ASSERT).
   OK branch: callvalue = 0w, fresh_vars preserved.
   Abort branch: callvalue ≠ 0w. *)
Theorem compile_payable_check_ok_or_revert:
  ∀ st0 st1 st2 st3 cv_v nv_v ss0.
    emit_op CALLVALUE [] st0 = (cv_v, st1) ∧
    emit_op ISZERO [cv_v] st1 = (nv_v, st2) ∧
    emit_void ASSERT [nv_v] st2 = ((), st3) ∧
    fresh_vars_wrt st0 ss0
    ⇒
    (∃ ss'. run_inst_seq (emitted_insts st0 st3) ss0 = OK ss' ∧
     fresh_vars_wrt st3 ss' ∧ same_blocks st0 st3 ∧
     ss0.vs_call_ctx.cc_callvalue = 0w) ∨
    (∃ ss'.
       run_inst_seq (emitted_insts st0 st3) ss0 = Abort Revert_abort ss' ∧
       ss0.vs_call_ctx.cc_callvalue ≠ 0w)
Proof
  rpt strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  (* Step 1: CALLVALUE → OK ss1 *)
  drule_all emit_op_CALLVALUE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st0 st1) ss0 = OK ss1` >>
  (* Step 2: ISZERO → OK ss2 *)
  drule emit_op_ISZERO_correct >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st1 st2) ss1 = OK ss2` >>
  (* Extend: st0→st2 *)
  `run_inst_seq (emitted_insts st0 st2) ss0 = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st0 st2` by metis_tac[inst_extends_trans] >>
  (* Step 3: ASSERT → OK or Abort *)
  drule emit_void_ASSERT_ok_or_revert >> disch_then drule >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[]
  (* OK case: bool_to_word(cc=0w) ≠ 0w, so cc = 0w *)
  >- (`inst_extends st0 st3` by metis_tac[inst_extends_trans] >>
      imp_res_tac run_inst_seq_emit_extend >> gvs[] >>
      conj_tac >- metis_tac[same_blocks_trans] >>
      gvs[bool_to_word_neq_0w])
  (* Abort case: bool_to_word(cc=0w) = 0w, so cc ≠ 0w *)
  >> (DISJ2_TAC >>
      qexists `revert_state (set_returndata [] ss2)` >>
      conj_tac
      >- (mp_tac (Q.SPECL [`st0`,`st2`,`st3`,`ss0`,`ss2`] run_inst_seq_emit_extend) >>
          impl_tac >- simp[] >> strip_tac >> gvs[])
      >> gvs[bool_to_word_eq_0w])
QED

Theorem compile_entry_checks_correct:
  ∀ min_cds is_payable ss st st'.
    compile_entry_checks min_cds is_payable st = ((), st') ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       (is_payable ∨ ss.vs_call_ctx.cc_callvalue = 0w)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, LET_THM] >>
  Cases_on `is_payable` >> gvs[] >>
  rpt (pairarg_tac >> gvs[])
  >- suspend "payable_case"
  >> suspend "nonpayable_case"
QED

Resume compile_entry_checks_correct[payable_case]:
  gvs[comp_return_def] >>
  Cases_on `min_cds > 4` >> gvs[comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM]
  >- (
    rpt (pairarg_tac >> gvs[]) >>
    drule_all compile_cds_check_ok_or_revert >>
    strip_tac >> metis_tac[]
  ) >>
  qexists `ss` >> DISJ1_TAC >>
  simp[emitted_insts_def, run_inst_seq_def]
QED

Resume compile_entry_checks_correct[nonpayable_case]:
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      LET_THM, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_payable_check_ok_or_revert >> strip_tac
  >- suspend "nonpayable_ok"
  >> suspend "nonpayable_abort"
QED

(* Payable OK: callvalue = 0w, payable prefix gives OK ss' *)
Resume compile_entry_checks_correct[nonpayable_ok]:
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  qpat_x_assum `emit_op CALLVALUE _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` kall_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _` kall_tac >>
  Cases_on `min_cds > 4` >> gvs[comp_return_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, LET_THM, pairTheory.PAIR] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all compile_cds_check_ok_or_revert >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  irule run_inst_seq_compose_ok_or_abort >>
  qexistsl [`ss'`, `cs'`] >> gvs[] >>
  metis_tac[inst_extends_trans]
QED

(* Payable Abort: callvalue ≠ 0w *)
Resume compile_entry_checks_correct[nonpayable_abort]:
  qexists `ss'` >> disj2_tac >>
  irule run_inst_seq_abort_extends >>
  qexists `cs'` >> rpt conj_tac
  (* abort assumption *)
  >- first_assum ACCEPT_TAC
  (* inst_extends st cs' from payable emit chain *)
  >- metis_tac[inst_extends_emit_op, inst_extends_emit_void,
               inst_extends_trans]
  (* inst_extends cs' st' from CDS conditional *)
  >> (qpat_x_assum `emit_op CALLVALUE _ _ = _` kall_tac >>
      qpat_x_assum `emit_op ISZERO [cv] _ = _` kall_tac >>
      qpat_x_assum `emit_void ASSERT [no_value] _ = _` kall_tac >>
      Cases_on `min_cds > 4` >> gvs[comp_return_def, inst_extends_refl] >>
      gvs[comp_bind_def, comp_ignore_bind_def, LET_THM, pairTheory.PAIR] >>
      rpt (pairarg_tac >> gvs[]) >>
      imp_res_tac inst_extends_emit_op >>
      imp_res_tac inst_extends_emit_void >>
      metis_tac[inst_extends_trans])
QED

Finalise compile_entry_checks_correct

(* Derive nonpayable revert from the general theorem *)
Theorem compile_entry_checks_nonpayable_revert:
  ∀ min_cds ss st st'.
    compile_entry_checks min_cds F st = ((), st') ∧
    fresh_vars_wrt st ss ∧
    ss.vs_call_ctx.cc_callvalue ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  drule_all compile_entry_checks_correct >> strip_tac >> gvs[]
QED

(* ===== Constructor Epilogue ===== *)

(* Both branches use Label "runtime_begin" via OFFSET, needing vs_labels.
   The immutables_len > 0 branch also uses immutables_buf in MCOPY.
   fresh_vars_wrt only constrains vs_vars, not vs_labels. *)
Theorem compile_constructor_epilogue_correct:
  ∀ runtime_size immutables_len immutables_buf ss st st'.
    compile_constructor_epilogue runtime_size immutables_len immutables_buf st =
      ((), st') ∧
    fresh_vars_wrt st ss ∧
    (∃ v. FLOOKUP ss.vs_labels "runtime_begin" = SOME v) ∧
    (immutables_len > 0 ⇒ ∃ v. eval_operand immutables_buf ss = SOME v)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt ss'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_constructor_epilogue _ _ _ _ = _` mp_tac >>
  simp[compile_constructor_epilogue_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, LET_THM] >>
  Cases_on `immutables_len > 0` >> gvs[]
  (* immutables_len > 0 branch *)
  >- suspend "imm_pos"
  (* immutables_len = 0 branch *)
  >> suspend "imm_zero"
QED

Resume compile_constructor_epilogue_correct[imm_pos]:
  strip_tac >> gvs[comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: ALLOCA *)
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  (* Step 2: ADD — deploy_buf evaluable in ss1, Lit always evaluable *)
  drule emit_op_ADD_correct >>
  disch_then drule >>
  disch_then (qspec_then `n2w runtime_size` mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  (* Step 3: MCOPY — imm_dst from ADD, immutables_buf from hypothesis (preserved), Lit *)
  drule emit_void_MCOPY_correct >>
  disch_then drule >>
  disch_then (qspecl_then [`v'`, `n2w immutables_len`] mp_tac) >>
  (impl_tac >- gvs[eval_operand_lit]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs3) ss2 = OK ss3` >>
  (* Step 4: OFFSET — Lit 0w always evaluable, Label "runtime_begin" preserved *)
  `eval_operand (Label "runtime_begin") ss3 = SOME v`
    by (gvs[eval_operand_def] >>
        `FLOOKUP ss1.vs_labels "runtime_begin" = SOME v`
          by gvs[] >>
        `FLOOKUP ss2.vs_labels "runtime_begin" = SOME v`
          by (Cases_on `Label "runtime_begin"` >>
              gvs[eval_operand_def] >>
              first_x_assum (qspecl_then [`Label "runtime_begin"`, `v`] mp_tac) >>
              simp[eval_operand_def]) >>
        gvs[mcopy_def, write_memory_with_expansion_def, LET_THM]) >>
  `eval_operand (Lit 0w) ss3 = SOME 0w` by simp[eval_operand_def] >>
  drule_all emit_op_OFFSET_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs3 cs4) ss3 = OK ss4` >>
  (* Step 5: CODECOPY — deploy_buf preserved, rt_begin from OFFSET, Lit *)
  `eval_operand deploy_buf ss4 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand rt_begin ss4 = SOME (0w + v)` by first_assum ACCEPT_TAC >>
  `eval_operand (Lit (n2w runtime_size)) ss4 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_void_CODECOPY_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs4 cs5) ss4 = OK ss5` >>
  (* Step 6: RETURN → Halt *)
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_inst >>
  (* Compose all OK segments: st→cs1→cs2→cs3→cs4→cs5 *)
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss3`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs3` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs4) ss = OK ss4`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs4` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs5) ss = OK ss5`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs5` by metis_tac[inst_extends_trans] >>
  (* Final: RETURN → Halt *)
  `eval_operand deploy_buf ss5 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w (immutables_len + runtime_size))) ss5 =
     SOME (n2w (immutables_len + runtime_size))`
    by simp[eval_operand_def] >>
  drule_all emit_inst_RETURN_halt >> strip_tac >>
  `inst_extends cs5 st'` by metis_tac[inst_extends_emit_inst] >>
  drule_all run_inst_seq_emit_extend >> gvs[]
QED

Resume compile_constructor_epilogue_correct[imm_zero]:
  strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: ALLOCA *)
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK ss1` >>
  (* Step 2: OFFSET — Label "runtime_begin" evaluable in ss1 *)
  `eval_operand (Label "runtime_begin") ss1 = SOME v`
    by (gvs[eval_operand_def]) >>
  `eval_operand (Lit 0w) ss1 = SOME 0w` by simp[eval_operand_def] >>
  drule_all emit_op_OFFSET_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss2` >>
  (* Step 3: CODECOPY *)
  `eval_operand op ss2 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand rt_begin ss2 = SOME (0w + v)` by first_assum ACCEPT_TAC >>
  `eval_operand (Lit (n2w runtime_size)) ss2 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_void_CODECOPY_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs2 cs3) ss2 = OK ss3` >>
  (* Step 4: RETURN → Halt *)
  `eval_operand op ss3 = SOME (n2w offset)` by metis_tac[] >>
  `eval_operand (Lit (n2w runtime_size)) ss3 = SOME (n2w runtime_size)`
    by simp[eval_operand_def] >>
  drule_all emit_inst_RETURN_halt >> strip_tac >>
  (* Compose *)
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  imp_res_tac inst_extends_emit_inst >>
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss3`
    by (imp_res_tac run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st cs3` by metis_tac[inst_extends_trans] >>
  `inst_extends cs3 st'` by metis_tac[inst_extends_emit_inst] >>
  drule_all run_inst_seq_emit_extend >> gvs[]
QED

Finalise compile_constructor_epilogue_correct

Theorem run_inst_seq_ok_not_halted:
  ∀ is ss ss'.
    run_inst_seq is ss = OK ss' ∧
    (∀i ss1 ss2. MEM i is ∧ step_inst_base i ss1 = OK ss2 ⇒ (ss2.vs_halted ⇔ ss1.vs_halted)) ∧
    ¬ss.vs_halted
    ⇒
    ¬ss'.vs_halted
Proof
  rpt strip_tac >>
  drule_at (Pos hd) (Q.ISPEC `\s. s.vs_halted` run_inst_seq_preserves_field) >>
  (impl_tac >- (rpt strip_tac >> res_tac >> fs[])) >>
  simp[]
QED

Theorem run_inst_seq_ok_implies_not_halted[local]:
  ∀is ss ss'.
    run_inst_seq is ss = OK ss' ∧ ¬ss.vs_halted
    ⇒
    ¬ss'.vs_halted
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h ss` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h ss = OK mid` >>
  `(mid.vs_halted ⇔ ss.vs_halted)` by metis_tac[step_inst_base_OK_preserves_halted] >>
  first_x_assum drule >> simp[]
QED


(* ===== Top-Level Module Correctness ===== *)

(* Labels the caller must supply as external: selector fn targets,
   external entry labels, internal fn labels. These must be pairwise
   distinct and external to st (not already bound, not in future
   fresh_label co-domain). In practice the frontend allocates these
   via fresh_label before calling compile_generate_runtime, and
   cs_next_label is advanced past all of them. *)
Definition runtime_input_labels_def:
  runtime_input_labels selectors external_fns internal_fns =
    MAP (λ(sel,lbl,has_tz). lbl) selectors ++
    MAP (λ(entry_lbl, cenv, pos_args, min_cds, is_payable,
            is_nr, nkey, use_trans, is_view, body, ret_type).
           entry_lbl) external_fns ++
    MAP (λ(fn_lbl, cenv, params, has_ret_buf, is_nr, nkey, use_trans,
            is_view, is_ctor, imm_len, body, ret_type).
           fn_lbl) internal_fns
End

(* Selector-declared function labels must match up with external_fn
   entry labels so that a JMP from dispatch lands on an emitted block. *)
Definition dispatch_labels_covered_def:
  dispatch_labels_covered selectors external_fns ⇔
    set (MAP (λ(sel,lbl,_). lbl) selectors) ⊆
      set (MAP (λ(entry_lbl,_,_,_,_,_,_,_,_,_,_). entry_lbl) external_fns)
End

Definition runtime_inputs_ok_def:
  runtime_inputs_ok selectors external_fns internal_fns st ⇔
    compile_state_ok st ∧
    EVERY (label_external st)
          (runtime_input_labels selectors external_fns internal_fns) ∧
    ALL_DISTINCT (runtime_input_labels selectors external_fns internal_fns) ∧
    dispatch_labels_covered selectors external_fns
End

(* Top-level correctness of compile_generate_runtime.
   Under well-formed inputs (frontend-allocated labels are fresh wrt st,
   pairwise distinct, selector labels match external_fn labels), the
   assembled runtime function executes to one of:
   - Halt ss'              (normal RETURN/STOP from a function body)
   - Abort a ss'           (entry-check failure, REVERT, or INVALID)
   - IntRet vals ss'       (unusual: an internal function returned to
                             top level; shouldn't happen for well-typed
                             modules, but is a legal exec_result shape
                             given the semantics we have)
   - Error e               (e.g., INVOKE when ctx does not contain the
                             callee function — see below)

   Explicitly excludes Error "out of fuel" (we quantify ∃fuel).

   NOTE [Error case]: Compiled function bodies may contain INVOKE
   instructions (for internal function calls). INVOKE looks up the callee
   in ctx.ctx_functions. If ctx does not contain all compiled internal
   functions, step_inst returns Error "invoke: function not found". This
   is NOT an exec fault but a context-incompleteness issue. Confirmed
   via EVAL: step_inst 1 <|ctx_functions := []; ctx_entry := NONE|>
   (mk_inst 0 INVOKE [Label "callee"] []) ARB = Error "invoke: function not found".
   To eliminate the Error case, add a hypothesis that ctx contains all
   compiled internal functions, or wait for function-body correctness
   theorems that guarantee well-formed INVOKE targets.

   NOTE: This is the module-level stitching theorem. It consumes the
   three fragment-level correctness theorems for dispatch/kwargs plus
   correctness theorems for external/internal function bodies (stated
   separately; several are still cheated upstream). *)
Theorem compile_generate_runtime_correct:
  ∀ selectors external_fns internal_fns fallback_fn dispatch_strategy
    bucket_count fn_metadata_bytes dense_buckets entry_info
    st st' ss ctx.
    compile_generate_runtime selectors external_fns internal_fns
        fallback_fn dispatch_strategy bucket_count fn_metadata_bytes
        dense_buckets entry_info st = ((), st') ∧
    runtime_inputs_ok selectors external_fns internal_fns st ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel result.
      run_blocks fuel ctx (assemble_function st st')
        (ss with <| vs_current_bb := st.cs_current_bb;
                     vs_inst_idx := LENGTH st.cs_current_insts |>) = result ∧
      ((∃ ss'. result = Halt ss') ∨
       (∃ a ss'. result = Abort a ss') ∨
       (∃ vals ss'. result = IntRet vals ss') ∨
       (∃ e. result = Error e))
Proof
  cheat
QED

(* ===== Pure/Read Instruction Preservation ===== *)

(* update_var only modifies vs_vars, so all observable fields + memory + ctx are preserved *)
Theorem update_var_preserves_observable[local]:
  ∀x v s. observable_equiv s (update_var x v s) ∧
          (update_var x v s).vs_memory = s.vs_memory ∧
          (update_var x v s).vs_call_ctx = s.vs_call_ctx ∧
          ((update_var x v s).vs_halted ⇔ s.vs_halted)
Proof
  simp[observable_equiv_def, update_var_def]
QED

(* jump_to only modifies vs_prev_bb, vs_current_bb, vs_inst_idx *)
Theorem jump_to_preserves_observable[local]:
  ∀lbl ss.
    observable_equiv ss (jump_to lbl ss) ∧
    (jump_to lbl ss).vs_memory = ss.vs_memory ∧
    (jump_to lbl ss).vs_call_ctx = ss.vs_call_ctx ∧
    ((jump_to lbl ss).vs_halted ⇔ ss.vs_halted)
Proof
  simp[jump_to_def, observable_equiv_def]
QED

Theorem fresh_vars_wrt_jump_to:
  ∀st ss lbl.
    fresh_vars_wrt st ss ⇒ fresh_vars_wrt st (jump_to lbl ss)
Proof
  simp[jump_to_def, fresh_vars_wrt_def]
QED

(* For opcodes that only use exec_pure1/2/3 or exec_read0/1,
   step_inst_base returns OK (update_var ...) which preserves
   all fields except vs_vars. *)
Theorem step_inst_base_pure_read_preserves[local]:
  ∀i s1 s2.
    step_inst_base i s1 = OK s2 ∧
    i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                       SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                       ISZERO; AND; OR; XOR; NOT;
                       CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                       GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                       NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                       MLOAD; SLOAD; TLOAD; OFFSET; PARAM}
    ⇒
    observable_equiv s1 s2 ∧
    s2.vs_memory = s1.vs_memory ∧
    s2.vs_call_ctx = s1.vs_call_ctx ∧
    s2.vs_data_section = s1.vs_data_section ∧
    s2.vs_tx_ctx = s1.vs_tx_ctx ∧
    s2.vs_block_ctx = s1.vs_block_ctx ∧
    (s2.vs_halted ⇔ s1.vs_halted)
Proof
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, observable_equiv_def]
QED

Theorem run_inst_seq_preserves_observable_and_memory:
  ∀is ss ss'.
    run_inst_seq is ss = OK ss' ∧
    EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM}) is ∧
    ¬ss.vs_halted
    ⇒
    observable_equiv ss ss' ∧
    ss'.vs_memory = ss.vs_memory ∧
    ss'.vs_call_ctx = ss.vs_call_ctx ∧
    ss'.vs_data_section = ss.vs_data_section ∧
    ss'.vs_tx_ctx = ss.vs_tx_ctx ∧
    ss'.vs_block_ctx = ss.vs_block_ctx ∧
    ¬ss'.vs_halted
Proof
  Induct_on `is` >> simp[run_inst_seq_def]
  >- (rpt strip_tac >> simp[observable_equiv_def])
  >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h ss` >> gvs[] >>
  `h.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                     SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                     ISZERO; AND; OR; XOR; NOT;
                     CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                     GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                     NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                     MLOAD; SLOAD; TLOAD; OFFSET; PARAM}`
    by (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule step_inst_base_pure_read_preserves >> strip_tac >>
  first_x_assum (qspecl_then [`v`, `ss'`] mp_tac) >>
  impl_tac >- (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  strip_tac >> gvs[observable_equiv_def]
QED

(* Boundary lemma: CALLDATASIZE is in the pure_read opcode set used by
   run_inst_seq_preserves_observable_and_memory. Proved once here to
   avoid unfolding the huge IN-set in consumer proofs. *)
Theorem CALLDATASIZE_in_pure_reads[local]:
  CALLDATASIZE ∈ {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                  ISZERO; AND; OR; XOR; NOT;
                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM}
Proof
  simp[pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]
QED

(* Boundary lemma: running a single CALLDATASIZE instruction preserves
   observable equivalence, memory, call context, and non-halted.
   Wraps run_inst_seq_preserves_observable_and_memory so consumers
   don't need to unfold the opcode IN-set. *)
Theorem CALLDATASIZE_run_observable[local]:
  ∀st cs1 v ss ss1.
    emit_op CALLDATASIZE [] st = (v, cs1) ∧
    run_inst_seq (emitted_insts st cs1) ss = OK ss1 ∧
    ¬ss.vs_halted
    ⇒
    observable_equiv ss ss1 ∧ ss1.vs_memory = ss.vs_memory ∧
    ss1.vs_call_ctx = ss.vs_call_ctx ∧
    ss1.vs_data_section = ss.vs_data_section ∧
    ss1.vs_tx_ctx = ss.vs_tx_ctx ∧
    ss1.vs_block_ctx = ss.vs_block_ctx ∧
    ¬ss1.vs_halted
Proof
  rpt strip_tac >>
  drule emit_op_CALLDATASIZE_everything_pure >> strip_tac >>
  drule run_inst_seq_preserves_observable_and_memory >> simp[]
QED

(* Boundary lemma: running a single CALLDATASIZE instruction preserves
   vs_current_bb. Wraps run_inst_seq_preserves_current_bb so consumers
   don't need to unfold the EVERY conditions. *)
Theorem CALLDATASIZE_run_preserves_current_bb[local]:
  ∀st cs1 v ss ss1.
    emit_op CALLDATASIZE [] st = (v, cs1) ∧
    run_inst_seq (emitted_insts st cs1) ss = OK ss1 ∧
    ¬ss.vs_halted
    ⇒
    ss1.vs_current_bb = ss.vs_current_bb
Proof
  rpt strip_tac >>
  drule emit_op_CALLDATASIZE_everything_pure >> strip_tac >>
  drule pure_every_imp_not_terminator >> strip_tac >>
  drule pure_every_imp_not_invoke >> strip_tac >>
  drule run_inst_seq_preserves_current_bb >> simp[]
QED

(* Helper: get_instruction for a prefix of instructions within a
   concatenated list. Purely list-based reasoning — no compile state
   needed. *)
Theorem get_instruction_append[local]:
  ∀bb prefix insts suffix n.
    bb.bb_instructions = prefix ++ insts ++ suffix ∧
    n < LENGTH insts
    ⇒
    get_instruction bb (LENGTH prefix + n) = SOME (EL n insts)
Proof
  rpt strip_tac >>
  simp[get_instruction_def] >>
  `LENGTH prefix + n < LENGTH bb.bb_instructions`
    by (fs[] >> decide_tac) >>
  fs[rich_listTheory.EL_APPEND2, rich_listTheory.EL_APPEND1]
QED
(* Boundary lemma: after CALLDATASIZE prefix + JMP emit,
   the rcf shifts from (st,ss) to (cs1,ss1).
   Takes ss with arbitrary vs_current_bb. The run_inst_seq hypothesis
   uses the overridden state; fragment_prefix_chain_gen already handles
   this mismatch (ss0 in conclusion, ss0 with vs_current_bb := ... in run_inst_seq). *)
Theorem nil_kwargs_prefix_chain[local]:
  ∀ctx st cs1 st' ss ss1 fuel bb.
    st.cs_current_bb = cs1.cs_current_bb ∧
    cs1.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs1 ∧
    same_blocks st cs1 ∧
    compile_state_ok st ∧
    fresh_vars_wrt st ss ∧
    fresh_vars_wrt cs1 ss1 ∧
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    run_inst_seq (emitted_insts st cs1)
      (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
    ss1.vs_current_bb = st.cs_current_bb ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs1) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs1) ∧
    (∀k. k < LENGTH (emitted_insts st cs1) ⇒
          get_instruction bb (LENGTH st.cs_current_insts + k) =
            SOME (EL k (emitted_insts st cs1))) ∧
    ¬ss.vs_halted ∧
    ¬ss1.vs_halted
    ⇒
    run_compiled_fragment ctx st st' ss fuel =
    run_compiled_fragment ctx cs1 st' ss1 fuel
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `st`, `cs1`, `st'`, `ss`, `ss1`,
                     `fuel`, `bb`, `emitted_insts st cs1`]
           fragment_prefix_chain_gen) >>
  simp[fresh_vars_wrt_current_bb_irrel, vs_halted_current_bb_irrel,
       venom_state_component_equality]
QED


(* Standalone bridge for applying nil_kwargs_prefix_chain.
   Extracted because applying irule/ho_match_mp_tac inside a by block
   with 24+ assumptions causes simp to time out.  The standalone theorem
   has its own clean context where simp works.  Follows the pattern of
   linear_dispatch_prefix_bridge. *)
Theorem nil_kwargs_prefix_bridge[local]:
  ∀ctx st cs1 st' ss ss1 fuel bb.
    compile_state_ok st ∧
    same_blocks st cs1 ∧
    fresh_vars_wrt st ss ∧
    fresh_vars_wrt cs1 ss1 ∧
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    run_inst_seq (emitted_insts st cs1)
      (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
    ss1.vs_current_bb = st.cs_current_bb ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs1) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs1) ∧
    cs1.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs1 ∧
    (∀k. k < LENGTH (emitted_insts st cs1) ⇒
          get_instruction bb (LENGTH st.cs_current_insts + k) =
            SOME (EL k (emitted_insts st cs1))) ∧
    ¬ss.vs_halted ∧ ¬ss1.vs_halted ∧
    st.cs_current_bb = cs1.cs_current_bb
    ⇒
    run_compiled_fragment ctx st st' ss fuel =
    run_compiled_fragment ctx cs1 st' ss1 fuel
Proof
  rpt strip_tac >>
  irule nil_kwargs_prefix_chain >>
  simp[same_blocks_def] >>
  (* irule normalizes (LENGTH n + k) to (k + LENGTH n); bridge uses natural form *)
  metis_tac[arithmeticTheory.ADD_COMM]
QED



Theorem observable_equiv_through_bb_override[local]:
  ∀ss lbl ss1 ss2.
    observable_equiv (ss with vs_current_bb := lbl) ss1 ∧
    observable_equiv ss1 ss2
    ⇒ observable_equiv ss ss2
Proof
  rpt strip_tac >>
  irule observable_equiv_trans >>
  qexists `(ss with vs_current_bb := lbl)` >>
  conj_tac >- simp[observable_equiv_current_bb_irrel, observable_equiv_def] >>
  irule observable_equiv_trans >>
  qexists `ss1` >> simp[]
QED

(* ===== Abort-Lifting Infrastructure ===== *)

(* Single-instruction abort: if step_inst_base h ss = Abort, then exec_block
   at that instruction also produces Abort with the idx restored. *)
Theorem exec_block_single_abort[local]:
  ∀ fuel ctx bb idx h ss a ss_abort.
    step_inst_base h ss = Abort a ss_abort ∧
    ¬is_terminator h.inst_opcode ∧
    h.inst_opcode ≠ INVOKE ∧
    get_instruction bb idx = SOME h
  ⇒
    exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
      Abort a (ss_abort with vs_inst_idx := idx)
Proof
  rpt strip_tac >>
  simp[Once exec_block_def] >>
  gvs[] >>
  (* Reduce step_inst to step_inst_base since h ≠ INVOKE *)
  qspecl_then [`fuel`, `ctx`, `h`, `ss with vs_inst_idx := idx`]
    assume_tac step_inst_non_invoke >>
  first_x_assum mp_tac >> simp[] >> strip_tac >>
  (* Apply step_inst_inst_idx_indep to commute vs_inst_idx *)
  assume_tac (Q.SPECL [`h`, `ss`, `idx`] step_inst_inst_idx_indep) >>
  first_x_assum mp_tac >> simp[] >> strip_tac >>
  (* Simplify: step_inst_base h (ss with vs_inst_idx := idx) = exec_result_map ... (Abort a ss_abort) *)
  `step_inst_base h (ss with vs_inst_idx := idx) =
    exec_result_map (λs'. s' with vs_inst_idx := idx) (Abort a ss_abort)`
    by simp[] >>
  simp[exec_result_map_def]
QED

(* Helper: if step_inst_base h ss = OK v and the tail aborts with a split,
   then h::insts aborts with h prepended to the prefix. *)
Theorem run_inst_seq_split_abort_cons[local]:
  ∀h insts ss v a ss_abort prefix h0 suffix ss_mid.
    step_inst_base h ss = OK v ∧
    insts = prefix ++ [h0] ++ suffix ∧
    run_inst_seq prefix v = OK ss_mid ∧
    step_inst_base h0 ss_mid = Abort a ss_abort
  ⇒
    ∃prefix' h' suffix' ss_mid'.
      h::insts = prefix' ++ [h'] ++ suffix' ∧
      run_inst_seq prefix' ss = OK ss_mid' ∧
      step_inst_base h' ss_mid' = Abort a ss_abort
Proof
  rpt strip_tac >>
  qexistsl [`h::prefix`, `h0`, `suffix`, `ss_mid`] >>
  simp[run_inst_seq_def]
QED

(* Split an aborting run_inst_seq into a successful prefix followed by
   a single aborting instruction. *)
Theorem run_inst_seq_split_abort[local]:
  ∀ insts ss a ss_abort.
    run_inst_seq insts ss = Abort a ss_abort
  ⇒
    ∃ prefix h suffix ss_mid.
      insts = prefix ++ [h] ++ suffix ∧
      run_inst_seq prefix ss = OK ss_mid ∧
      step_inst_base h ss_mid = Abort a ss_abort
Proof
  Induct_on `insts` >- simp[run_inst_seq_def] >>
  qx_gen_tac `h0` >>
  qx_gen_tac `s0` >> qx_gen_tac `a0` >> qx_gen_tac `sa0` >> strip_tac >>
  simp[Once run_inst_seq_def] >>
  Cases_on `step_inst_base h0 s0` >> gvs[run_inst_seq_def]
  >- (
    (* OK case: apply IH to tail, get split for insts, then prepend h0 *)
    first_x_assum (qspecl_then [`v`, `a0`, `sa0`] mp_tac) >>
    simp[] >> strip_tac >>
    qexistsl [`h0::prefix`, `h`, `suffix`, `ss_mid`] >>
    gvs[run_inst_seq_def, run_inst_seq_cons_ok]
  )
  >- (
    (* Abort case: h0 aborts directly *)
    qexistsl [`[]`, `h0`, `insts`, `s0`] >> simp[run_inst_seq_def]
  )
QED

(* If run_inst_seq aborts on a prefix of a block's instructions (all
   non-terminator, non-INVOKE), exec_block also aborts. This is the
   Abort counterpart of exec_block_inst_seq_prefix from emitHelperProps. *)
Theorem exec_block_inst_seq_abort[local]:
  ∀ insts fuel ctx bb ss idx a ss_abort.
    run_inst_seq insts ss = Abort a ss_abort ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts ∧
    (∀k. k < LENGTH insts ⇒ get_instruction bb (idx + k) = SOME (EL k insts))
  ⇒
    ∃ss'. exec_block fuel ctx bb (ss with vs_inst_idx := idx) = Abort a ss'
Proof
  rpt strip_tac >>
  drule run_inst_seq_split_abort >> rw[] >>
  (* Derive EVERY for prefix and h from EVERY for insts *)
  `EVERY (λi. ¬is_terminator i.inst_opcode) prefix`
    by (fs[listTheory.EVERY_APPEND]) >>
  `¬is_terminator h.inst_opcode`
    by (fs[listTheory.EVERY_APPEND]) >>
  `EVERY (λi. i.inst_opcode ≠ INVOKE) prefix`
    by (fs[listTheory.EVERY_APPEND]) >>
  `h.inst_opcode ≠ INVOKE`
    by (fs[listTheory.EVERY_APPEND]) >>
  (* Derive get_instruction for prefix and h *)
  `∀k. k < LENGTH prefix ⇒ get_instruction bb (idx + k) = SOME (EL k prefix)`
    by (rpt strip_tac >>
        qpat_x_assum `∀k. k < LENGTH (prefix ⧺ [h] ⧺ suffix) ⇒ _`
          (qspecl_then [`k`] mp_tac) >>
        simp[rich_listTheory.EL_APPEND1]) >>
  `get_instruction bb (idx + LENGTH prefix) = SOME h`
    by (qpat_x_assum `∀k. k < LENGTH (prefix ⧺ [h] ⧺ suffix) ⇒ _`
          (qspecl_then [`LENGTH prefix`] mp_tac) >>
        simp[rich_listTheory.EL_APPEND1, listTheory.el_append3]) >>
  (* Execute prefix via exec_block_inst_seq_prefix *)
  `exec_block fuel ctx bb (ss with vs_inst_idx := idx) =
    exec_block fuel ctx bb (ss_mid with vs_inst_idx := idx + LENGTH prefix)`
    by (irule exec_block_inst_seq_prefix >> simp[]) >>
  (* Then h via exec_block_single_abort *)
  `exec_block fuel ctx bb (ss_mid with vs_inst_idx := idx + LENGTH prefix) =
    Abort a (ss_abort with vs_inst_idx := idx + LENGTH prefix)`
    by (irule exec_block_single_abort >> simp[]) >>
  simp[] >>
  qexists `ss_abort with vs_inst_idx := idx + LENGTH prefix` >>
  simp[]
QED

(* Bridge: run_inst_seq abort on emitted_insts implies exec_block aborts.
   exec_block doesn't depend on vs_current_bb (only vs_inst_idx). *)
Theorem exec_block_emitted_insts_abort[local]:
  ∀st st' ss0 a ss_abort fuel ctx bb.
    run_inst_seq (emitted_insts st st') ss0 = Abort a ss_abort ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st st') ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st st') ∧
    same_blocks st st' ∧ compile_state_ok st ∧
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb
  ⇒
    ∃ss'. exec_block fuel ctx bb
      (ss0 with vs_inst_idx := LENGTH st.cs_current_insts) = Abort a ss'
Proof
  rpt strip_tac >>
  `∀k. k < LENGTH (emitted_insts st st') ⇒
    get_instruction bb (LENGTH st.cs_current_insts + k) =
    SOME (EL k (emitted_insts st st'))`
    by metis_tac[emitted_insts_get_instruction] >>
  drule_all exec_block_inst_seq_abort >> simp[]
QED

(* Corollary: if the emitted-instruction prefix of the current block
   aborts via run_inst_seq, run_compiled_fragment also produces Abort.
   Requires ss.vs_current_bb = st.cs_current_bb so that fragment_entry_correct's
   state override (vs_current_bb := st.cs_current_bb) is a no-op. *)
Theorem rcf_abort_from_prefix_abort[local]:
  ∀ st st' ss a ss_abort fuel ctx.
    run_inst_seq (emitted_insts st st') ss = Abort a ss_abort ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st st') ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st st') ∧
    same_blocks st st' ∧
    compile_state_ok st ∧
    ss.vs_current_bb = st.cs_current_bb ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted
  ⇒
    ∃ss'. run_compiled_fragment ctx st st' ss fuel = Abort a ss'
Proof
  rpt strip_tac >>
  `st.cs_current_bb ∉ set (MAP (λbb. bb.bb_label) st'.cs_blocks)`
    by (fs[same_blocks_def, listTheory.MEM_MAP] >>
        metis_tac[current_bb_not_in_blocks]) >>
  `lookup_block st.cs_current_bb (assemble_blocks st') =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>`
    by (irule lookup_block_assemble_current >> fs[same_blocks_def]) >>
  (* Key: the double-update collapses because ss.vs_current_bb = st.cs_current_bb *)
  `ss with <|vs_current_bb := st.cs_current_bb; vs_inst_idx := LENGTH st.cs_current_insts|> =
    ss with vs_inst_idx := LENGTH st.cs_current_insts`
    by simp[venom_state_component_equality] >>
  (* Expand rcf via fragment_entry_correct *)
  drule_all fragment_entry_correct >> strip_tac >>
  gvs[] >>
  (* Apply bridge: after drule resolves first antecedent, 3 ∀-vars remain: fuel, ctx, bb *)
  drule exec_block_emitted_insts_abort >>
  disch_then (qspecl_then [`fuel`, `ctx`,
      `<|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>`]
      mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  (* exec_block = Abort, so the case expression in rcf reduces to Abort *)
  qexists `ss'` >> simp[]
QED

(* Variant of rcf_abort_from_prefix_abort where the aborting prefix is a
   SUB-prefix of the full emitted instructions. The full compilation goes
   st→cs2→st', where cs2→st' emits a terminator (JMP). The abort happens
   in the prefix st→cs2. Since exec_block aborts before reaching the
   terminator, the full instruction list (which includes the terminator
   after cs2) doesn't affect the result. *)
Theorem rcf_abort_from_subprefix_abort[local]:
  ∀ st cs2 st' ss a ss_abort fuel ctx.
    run_inst_seq (emitted_insts st cs2) ss = Abort a ss_abort ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2) ∧
    same_blocks st cs2 ∧ same_blocks cs2 st' ∧
    compile_state_ok st ∧
    ss.vs_current_bb = st.cs_current_bb ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    (* The full instruction list extends the aborting prefix *)
    st'.cs_current_insts = st.cs_current_insts ⧺ emitted_insts st cs2 ⧺ emitted_insts cs2 st'
  ⇒
    ∃ss'. run_compiled_fragment ctx st st' ss fuel = Abort a ss'
Proof
  rpt strip_tac >>
  `st.cs_current_bb ∉ set (MAP (λbb. bb.bb_label) st'.cs_blocks)`
    by (fs[same_blocks_def, listTheory.MEM_MAP] >>
        metis_tac[current_bb_not_in_blocks]) >>
  `lookup_block st.cs_current_bb (assemble_blocks st') =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>`
    by (irule lookup_block_assemble_current >> fs[same_blocks_def]) >>
  `ss with <|vs_current_bb := st.cs_current_bb; vs_inst_idx := LENGTH st.cs_current_insts|> =
    ss with vs_inst_idx := LENGTH st.cs_current_insts`
    by simp[venom_state_component_equality] >>
  qabbrev_tac `bb = <|bb_label := st.cs_current_bb;
                       bb_instructions := st'.cs_current_insts|>` >>
  `lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb`
    by simp[Abbr `bb`] >>
  drule_all fragment_entry_correct >> strip_tac >>
  gvs[] >>
  (* Key: the get_instruction constraint for emitted_insts st cs2
     holds against st'.cs_current_insts because the first part matches.
     Use mp_tac + Q.SPECL instead of irule to avoid ADD_COMM normalization
     (irule normalizes LENGTH n + k to k + LENGTH n, creating unsolvable subgoals). *)
  `∀k. k < LENGTH (emitted_insts st cs2) ⇒
       get_instruction bb (LENGTH st.cs_current_insts + k) =
         SOME (EL k (emitted_insts st cs2))`
    by (rpt strip_tac >>
        mp_tac (Q.SPECL [`bb`, `st.cs_current_insts`, `emitted_insts st cs2`,
                          `emitted_insts cs2 st'`, `k`] get_instruction_append) >>
        simp[Abbr `bb`]) >>
  (* Now apply exec_block_inst_seq_abort with the sub-prefix.
     After drule matches the first antecedent (run_inst_seq), insts/ss/a/ss_abort
     are instantiated. Remaining ∀-vars: fuel, ctx, bb, idx. *)
  drule exec_block_inst_seq_abort >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `LENGTH st.cs_current_insts`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  (* exec_block = Abort a ss', so rcf case expression reduces to Abort *)
  qexists `ss'` >> simp[]
QED



(* ===== Cheated Kwargs Initialization Helper ===== *)
(* Correctness of compile_init_kwargs: either all kwargs are initialized
   successfully (producing same_blocks, fresh_vars, non-terminator,
   non-INVOKE prefix) or the execution aborts (clamp/decode failure or
   INVALID from unresolved Name reference in default expressions).

   CHEATED: full proof requires compile_abi_decode_to_buf_correct and
   compile_expr_correct (both cheated upstream) plus induction matching
   compile_init_kwargs_ind. *)
Theorem compile_init_kwargs_correct[local]:
  ∀ cenv kwarg_vars calldata_offset kwargs_from_calldata hi_op w
    ss st st'.
    compile_init_kwargs cenv kwarg_vars calldata_offset
                        kwargs_from_calldata hi_op st = ((), st') ∧
    compile_state_ok st ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted ∧
    eval_operand hi_op ss = SOME w
    ⇒
    same_blocks st st' ∧
    compile_state_ok st' ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    st.cs_next_label ≤ st'.cs_next_label ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st st') ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st st') ∧
    ((∃ss1. run_inst_seq (emitted_insts st st') ss = OK ss1 ∧
            fresh_vars_wrt st' ss1 ∧
            observable_equiv ss ss1 ∧
            ss1.vs_call_ctx = ss.vs_call_ctx ∧
            ¬ss1.vs_halted)
    ∨
    (∃ss1. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss1))
Proof
  cheat
QED


(* Empty kwargs correctness: CALLDATASIZE (pure read) + JMP to external label.
   Proof strategy: compose two boundary lemmas at the interface level.
   1. nil_kwargs_prefix_chain: the CALLDATASIZE prefix shifts the rcf
      from (st, ss) to (cs1, ss1) without changing the result
   2. jmp_external_exits_fragment: the JMP exit gives OK with the
      desired properties from (cs1, ss1) *)
Theorem compile_entry_point_kwargs_nil_correct[local]:
  ∀ cenv calldata_offset kwargs_from_calldata common_label
    ss st st' ctx.
    compile_entry_point_kwargs cenv [] calldata_offset
      kwargs_from_calldata common_label st = ((), st') ∧
    compile_state_ok st ∧
    label_external st common_label ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      ss'.vs_current_bb = common_label ∧
      observable_equiv ss ss' ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_entry_point_kwargs_nil_compile >> strip_tac >>
  rename1 `emit_op CALLDATASIZE [] st = (cds_v, cs1)` >>
  `inst_extends st cs1` by metis_tac[inst_extends_emit_op] >>
  `compile_state_ok cs1` by metis_tac[compile_state_ok_emit_op] >>
  `label_external cs1 common_label`
    by metis_tac[label_external_emit_op] >>
  `same_blocks st cs1` by metis_tac[emit_op_same_blocks] >>
  (* Derive overridden state facts for CALLDATASIZE application *)
  `fresh_vars_wrt st (ss with vs_current_bb := st.cs_current_bb)`
    by metis_tac[fresh_vars_wrt_current_bb_irrel] >>
  `¬(ss with vs_current_bb := st.cs_current_bb).vs_halted`
    by metis_tac[vs_halted_current_bb_irrel] >>
  (* Apply CALLDATASIZE correctness to the overridden state *)
  `∃ss1. run_inst_seq (emitted_insts st cs1)
           (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
         eval_operand cds_v ss1 =
           SOME (n2w (LENGTH (ss with vs_current_bb := st.cs_current_bb).vs_call_ctx.cc_calldata)) ∧
         same_blocks st cs1 ∧ fresh_vars_wrt cs1 ss1 ∧
         (∀op w. eval_operand op (ss with vs_current_bb := st.cs_current_bb) = SOME w ⇒
                 eval_operand op ss1 = SOME w) ∧
         ss1.vs_call_ctx = (ss with vs_current_bb := st.cs_current_bb).vs_call_ctx ∧
         ss1.vs_memory = (ss with vs_current_bb := st.cs_current_bb).vs_memory`
    by (drule emit_op_CALLDATASIZE_correct >>
        disch_then (qspec_then `ss with vs_current_bb := st.cs_current_bb` mp_tac) >>
        simp[]) >>
  (* Derive instruction layout from inst_extends *)
  `cs1.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs1`
    by fs[inst_extends_def] >>
  (* CALLDATASIZE preserves observable equivalence and current_bb *)
  `observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss1 ∧
   ss1.vs_memory = ss.vs_memory ∧
   ss1.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss1.vs_halted`
    by (mp_tac (Q.SPECL [`st`, `cs1`, `cds_v`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss1`]
                CALLDATASIZE_run_observable) >>
        simp[vs_halted_current_bb_irrel]) >>
  `ss1.vs_current_bb = st.cs_current_bb`
    by (mp_tac (Q.SPECL [`st`, `cs1`, `cds_v`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss1`]
                CALLDATASIZE_run_preserves_current_bb) >>
        simp[vs_halted_current_bb_irrel]) >>
  (* CALLDATASIZE is pure: not terminator, not INVOKE *)
  `EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs1) ∧
   EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs1)`
    by metis_tac[emit_op_CALLDATASIZE_everything_pure,
                 pure_everyy_imp_not_terminator,
                 pure_everyy_imp_not_invoke] >>
  (* JMP step — derive lookup_block for prefix chain *)
  imp_res_tac emit_inst_extends >>
  `¬MEM st.cs_current_bb (MAP (λbb. bb.bb_label) st'.cs_blocks)`
    by (fs[same_blocks_def, listTheory.MEM_MAP] >>
        metis_tac[current_bb_not_in_blocks]) >>
  `lookup_block st.cs_current_bb (assemble_blocks st') =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>`
    by (irule lookup_block_assemble_current >>
        conj_tac >- fs[same_blocks_def] >>
        fs[same_blocks_def]) >>
  qabbrev_tac `bb = <|bb_label := st.cs_current_bb;
                       bb_instructions := st'.cs_current_insts|>` >>
  `lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb`
    by fs[Abbr `bb`] >>
  `bb.bb_instructions = st'.cs_current_insts` by simp[Abbr `bb`] >>
  (* get_instruction via boundary lemma — natural (n + k) form from
     get_instruction_append, matching nil_kwargs_prefix_bridge *)
  `∀k. k < LENGTH (emitted_insts st cs1) ⇒
       get_instruction bb (LENGTH st.cs_current_insts + k) =
         SOME (EL k (emitted_insts st cs1))`
    by (rpt strip_tac >>
        irule get_instruction_append >>
        conj_tac >- simp[Abbr `bb`] >>
        qexists `[mk_inst cs1.cs_next_id JMP [Label common_label] []]` >>
        simp[listTheory.APPEND_ASSOC]) >>
  qpat_x_assum `∀op w. eval_operand _ _ = SOME w ⇒ _` kall_tac >>
  qpat_x_assum `eval_operand cds_v ss1 = SOME _` kall_tac >>
  qpat_x_assum `¬MEM st.cs_current_bb (MAP _ st'.cs_blocks)` kall_tac >>
  qpat_x_assum `inst_extends st cs1` kall_tac >>
  qpat_x_assum `bb.bb_instructions = st'.cs_current_insts` kall_tac >>
  (* keep observable_equiv for the final transitivity chain *)
  qpat_x_assum `ss1.vs_memory = (ss with vs_current_bb := st.cs_current_bb).vs_memory` kall_tac >>
  qpat_x_assum `ss1.vs_call_ctx = (ss with vs_current_bb := st.cs_current_bb).vs_call_ctx` kall_tac >>
  qpat_x_assum `¬(ss with vs_current_bb := st.cs_current_bb).vs_halted` kall_tac >>
  qpat_x_assum `fresh_vars_wrt st (ss with vs_current_bb := st.cs_current_bb)` kall_tac >>
  qpat_x_assum `st'.cs_next_id = _` kall_tac >>
  qpat_x_assum `st'.cs_current_bb = _` kall_tac >>
  qpat_x_assum `st'.cs_blocks = _` kall_tac >>
  qpat_x_assum `st'.cs_next_label = _` kall_tac >>
  qpat_x_assum `st'.cs_next_var = _` kall_tac >>
  (* Derive same_blocks current_bb fact *)
  `st.cs_current_bb = cs1.cs_current_bb` by fs[same_blocks_def] >>
  (* JMP exit from (cs1, ss1) *)
  drule jmp_external_exits_fragment >>
  disch_then (qspecl_then [`ctx`, `ss1`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_compiled_fragment _ _ _ _ fuel' = OK ss2` >>
  rename1 `ss2.vs_current_bb = _` >>
  qexistsl [`fuel'`, `ss2`] >> simp[] >>
  (* Bridge: rcf from (st, ss) equals rcf from (cs1, ss1) *)
  `run_compiled_fragment ctx st st' ss fuel' =
    run_compiled_fragment ctx cs1 st' ss1 fuel'`
    by (drule_all nil_kwargs_prefix_bridge >>
        simp[same_blocks_def] >>
        strip_tac >> simp[]) >>
  (* Close observable_equiv ss ss2 via transitivity through ss1 *)
  `observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss2`
    by metis_tac[observable_equiv_trans] >>
  drule_all observable_equiv_through_bb_override >> simp[]
QED

Theorem vars_rel_current_bb_irrel[local]:
  ∀cenv scopes ss bb.
    vars_rel cenv scopes ss ⇒ vars_rel cenv scopes (ss with vs_current_bb := bb)
Proof
  rpt strip_tac >> pop_assum mp_tac >> simp[vars_rel_def]
QED

Theorem storage_rel_current_bb_irrel[local]:
  ∀addr vs ss bb.
    storage_rel addr vs ss ⇒ storage_rel addr vs (ss with vs_current_bb := bb)
Proof
  rpt strip_tac >> pop_assum mp_tac >> simp[storage_rel_def, contract_storage_def]
QED

Theorem transient_rel_current_bb_irrel[local]:
  ∀addr vs ss bb.
    transient_rel addr vs ss ⇒ transient_rel addr vs (ss with vs_current_bb := bb)
Proof
  rpt strip_tac >> pop_assum mp_tac >> simp[transient_rel_def, contract_transient_def]
QED

Theorem immutables_rel_current_bb_irrel[local]:
  ∀cenv addr src_id_opt is_ctor vs ss bb.
    immutables_rel cenv addr src_id_opt is_ctor vs ss ⇒
    immutables_rel cenv addr src_id_opt is_ctor vs (ss with vs_current_bb := bb)
Proof
  rpt strip_tac >> pop_assum mp_tac >> simp[immutables_rel_def]
QED

Theorem logs_rel_current_bb_irrel[local]:
  ∀cenv addr vs ss bb.
    logs_rel cenv addr vs ss ⇒ logs_rel cenv addr vs (ss with vs_current_bb := bb)
Proof
  rpt strip_tac >> pop_assum mp_tac >> simp[logs_rel_def]
QED

Theorem state_rel_vars_irrel[local]:
  ∀cenv cx es ss vars'.
    state_rel cenv cx es ss ⇒ state_rel cenv cx es (ss with vs_vars := vars')
Proof
  rw[state_rel_def, vars_rel_def, storage_rel_def, contract_storage_def,
     transient_rel_def, contract_transient_def, immutables_rel_def,
     logs_rel_def, call_ctx_rel_def]
QED

Theorem state_rel_current_bb_irrel[local]:
  ∀cenv cx es ss bb.
    state_rel cenv cx es ss ⇒ state_rel cenv cx es (ss with vs_current_bb := bb)
Proof
  rw[state_rel_def, vars_rel_current_bb_irrel, storage_rel_current_bb_irrel,
     transient_rel_current_bb_irrel, immutables_rel_current_bb_irrel,
     logs_rel_current_bb_irrel]
QED

(* Compilation-equation lemma for general kwargs case:
   Unfolds the do-notation into three sequential steps. *)
Theorem compile_entry_point_kwargs_compile[local]:
  ∀ cenv kwarg_vars calldata_offset kwargs_from_calldata common_label st st'.
    compile_entry_point_kwargs cenv kwarg_vars calldata_offset
      kwargs_from_calldata common_label st = ((), st') ⇒
    ∃ hi_op cs1 cs2.
      emit_op CALLDATASIZE [] st = (hi_op, cs1) ∧
      compile_init_kwargs cenv kwarg_vars calldata_offset
        kwargs_from_calldata hi_op cs1 = ((), cs2) ∧
      emit_inst JMP [Label common_label] [] cs2 = ((), st')
Proof
  simp[compile_entry_point_kwargs_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op CALLDATASIZE [] st` >> gvs[] >>
  Cases_on `compile_init_kwargs cenv kwarg_vars calldata_offset
              kwargs_from_calldata q r` >> gvs[] >>
  Cases_on `q'` >> gvs[]
QED

(* Bridge lemma: state_rel preserved through a pure-read instruction step.
   exec_read0 (used by CALLDATASIZE, CALLDATALOAD, CALLVALUE, etc.) only
   modifies vs_vars. state_rel does not depend on vs_vars, vs_current_bb,
   vs_inst_idx, or vs_prev_bb. So if observable fields and call_ctx/memory
   are preserved, state_rel holds for the post-step state. *)
Theorem state_rel_after_pure_read[local]:
  ∀cenv cx es ss ss'.
    state_rel cenv cx es ss ∧
    ss'.vs_memory = ss.vs_memory ∧
    ss'.vs_accounts = ss.vs_accounts ∧
    ss'.vs_call_ctx = ss.vs_call_ctx ∧
    ss'.vs_transient = ss.vs_transient ∧
    ss'.vs_immutables = ss.vs_immutables ∧
    ss'.vs_data_section = ss.vs_data_section ∧
    ss'.vs_logs = ss.vs_logs ∧
    ss'.vs_tx_ctx = ss.vs_tx_ctx ∧
    ss'.vs_block_ctx = ss.vs_block_ctx
    ⇒ state_rel cenv cx es ss'
Proof
  rw[state_rel_def, vars_rel_def, storage_rel_def, contract_storage_def,
     transient_rel_def, contract_transient_def, immutables_rel_def,
     logs_rel_def, call_ctx_rel_def]
QED

(* Boundary lemma: CALLDATASIZE preserves state_rel.
   CALLDATASIZE only writes to vs_vars (via exec_read0/update_var).
   state_rel does not depend on vs_vars, and all other fields are
   preserved by pure reads. Proved once here so consumers never need
   to enumerate 9 field equalities in a large context. *)
Theorem CALLDATASIZE_preserves_state_rel[local]:
  ∀cenv cx es st cs1 v ss ss1.
    emit_op CALLDATASIZE [] st = (v, cs1) ∧
    run_inst_seq (emitted_insts st cs1) ss = OK ss1 ∧
    ¬ss.vs_halted ∧ state_rel cenv cx es ss
    ⇒ state_rel cenv cx es ss1
Proof
  rpt strip_tac >>
  drule CALLDATASIZE_run_observable >> disch_then drule >> strip_tac >>
  irule state_rel_after_pure_read >> qexists `ss` >>
  simp[observable_equiv_def] >>
  metis_tac[observable_equiv_def]
QED

(* Bridge lemma: after emit_inst JMP on cs2 producing st', derive all
   structural facts needed for the kwargs correctness proof.
   Small context so drule+simp works in consumers.
   Follows the linear_dispatch_st_prime_facts pattern. *)
Theorem kwargs_jmp_bridge[local]:
  ∀st cs1 cs2 st' common_label.
    emit_inst JMP [Label common_label] [] cs2 = ((), st') ∧
    same_blocks st cs1 ∧ same_blocks cs1 cs2 ∧
    cs1.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs1 ∧
    cs2.cs_current_insts = cs1.cs_current_insts ++ emitted_insts cs1 cs2 ∧
    inst_extends st cs1 ∧ st.cs_next_label ≤ cs2.cs_next_label ∧
    compile_state_ok st ∧ compile_state_ok cs2 ∧ label_external st common_label ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs1) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs1) ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts cs1 cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts cs1 cs2)
  ⇒
    compile_state_ok st' ∧ inst_extends cs2 st' ∧
    same_blocks cs2 st' ∧ same_blocks st cs2 ∧ same_blocks st st' ∧
    cs2.cs_current_bb = st.cs_current_bb ∧
    label_external cs2 common_label ∧ inst_extends st cs2 ∧
    emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2 ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2) ∧
    st'.cs_current_insts =
      st.cs_current_insts ++ emitted_insts st cs2 ++ emitted_insts cs2 st'
Proof
  rpt strip_tac >-
  (* 1. compile_state_ok st' *)
  metis_tac[compile_state_ok_emit_inst] >-
  (* 2. inst_extends cs2 st' *)
  metis_tac[inst_extends_emit_inst] >-
  (* 3. same_blocks cs2 st' *)
  metis_tac[emit_inst_extends, exprLoweringPropsTheory.same_blocks_def] >-
  (* 4. same_blocks st cs2 *)
  metis_tac[emitHelperPropsTheory.same_blocks_trans] >-
  (* 5. same_blocks st st': st→cs1→cs2, cs2→st' from emit_inst *)
  (irule emitHelperPropsTheory.same_blocks_trans >>
   qexists `cs2` >> conj_tac >-
   (irule emitHelperPropsTheory.same_blocks_trans >>
    qexists `cs1` >>
    metis_tac[exprLoweringPropsTheory.same_blocks_def]) >>
   metis_tac[emit_inst_extends, exprLoweringPropsTheory.same_blocks_def]) >-
  (* 6. cs2.cs_current_bb = st.cs_current_bb: from same_blocks st cs2 via trans *)
  metis_tac[emitHelperPropsTheory.same_blocks_trans,
            exprLoweringPropsTheory.same_blocks_def] >-
  (* 7. label_external cs2 common_label *)
  metis_tac[label_external_same_blocks,
            emitHelperPropsTheory.same_blocks_trans] >-
  (* 8. inst_extends st cs2: trans st→cs1→cs2 *)
  (irule inst_extends_trans >>
   qexists `cs1` >> simp[inst_extends_def]) >-
  (* 9. emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2 *)
  metis_tac[emitted_insts_append] >-
  (* 10. EVERY (¬is_terminator) (emitted_insts st cs2) *)
  metis_tac[emitted_insts_append, listTheory.EVERY_APPEND] >-
  (* 11. EVERY (≠INVOKE) (emitted_insts st cs2) *)
  metis_tac[emitted_insts_append, listTheory.EVERY_APPEND] >>
  (* 12. st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2 ++ emitted_insts cs2 st'
     From emit_inst_extends: st'.cs_current_insts = cs2.cs_current_insts ++ [JMP inst]
     From emitted_insts_emit_inst: emitted_insts cs2 st' = [JMP inst]
     From emitted_insts_append + assumptions: emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2
     Then APPEND_ASSOC rearrangement *)
  metis_tac[emit_inst_extends, emitted_insts_emit_inst,
            emitted_insts_append, listTheory.APPEND_ASSOC]
QED

(* Boundary lemma: packages all CALLDATASIZE-derived execution facts.
   Small context (4 antecedents) so tactics work reliably.
   Consumers use mp_tac + impl_keep_tac + strip_tac to get all facts. *)
Theorem CDS_phase_ok[local]:
  ∀st cs1 v ss cenv cx es.
    emit_op CALLDATASIZE [] st = (v, cs1) ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    state_rel cenv cx es ss
    ⇒
    ∃ss1.
      run_inst_seq (emitted_insts st cs1)
        (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
      eval_operand v ss1 = SOME (n2w (LENGTH ss.vs_call_ctx.cc_calldata)) ∧
      same_blocks st cs1 ∧ fresh_vars_wrt cs1 ss1 ∧
      ss1.vs_call_ctx = ss.vs_call_ctx ∧
      ss1.vs_memory = ss.vs_memory ∧
      observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss1 ∧
      ss1.vs_current_bb = st.cs_current_bb ∧
      ¬ss1.vs_halted ∧
      state_rel cenv cx es ss1
Proof
  rpt strip_tac >>
  `fresh_vars_wrt st (ss with vs_current_bb := st.cs_current_bb)`
    by metis_tac[fresh_vars_wrt_current_bb_irrel] >>
  `¬(ss with vs_current_bb := st.cs_current_bb).vs_halted`
    by metis_tac[vs_halted_current_bb_irrel] >>
  drule emit_op_CALLDATASIZE_correct >>
  disch_then (qspec_then `ss with vs_current_bb := st.cs_current_bb` assume_tac) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  conj_tac >- (
    mp_tac (Q.SPECL [`st`, `cs1`, `v`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
                CALLDATASIZE_run_observable) >>
    impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
    simp[vs_halted_current_bb_irrel]) >>
  conj_tac >- (
    mp_tac (Q.SPECL [`st`, `cs1`, `v`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
                CALLDATASIZE_run_preserves_current_bb) >>
    impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
    simp[vs_halted_current_bb_irrel]) >>
  conj_tac >- (
    mp_tac (Q.SPECL [`emitted_insts st cs1`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
                run_inst_seq_ok_implies_not_halted) >>
    impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
    simp[vs_halted_current_bb_irrel]) >>
  `state_rel cenv cx es (ss with vs_current_bb := st.cs_current_bb)`
    by metis_tac[state_rel_current_bb_irrel] >>
  mp_tac (Q.SPECL [`cenv`, `cx`, `es`, `st`, `cs1`, `v`,
              `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
              CALLDATASIZE_preserves_state_rel) >>
  impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
  simp[vs_halted_current_bb_irrel]
QED

(* CDS phase without state_rel — matches the spec theorem's hypotheses. *)
Theorem CDS_phase_ok_simple[local]:
  ∀st cs1 v ss.
    emit_op CALLDATASIZE [] st = (v, cs1) ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted
    ⇒
    ∃ss1.
      run_inst_seq (emitted_insts st cs1)
        (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
      eval_operand v ss1 = SOME (n2w (LENGTH ss.vs_call_ctx.cc_calldata)) ∧
      fresh_vars_wrt cs1 ss1 ∧
      ss1.vs_call_ctx = ss.vs_call_ctx ∧
      ss1.vs_memory = ss.vs_memory ∧
      observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss1 ∧
      ss1.vs_current_bb = st.cs_current_bb ∧
      ¬ss1.vs_halted
Proof
  rpt strip_tac >>
  `fresh_vars_wrt st (ss with vs_current_bb := st.cs_current_bb)`
    by metis_tac[fresh_vars_wrt_current_bb_irrel] >>
  `¬(ss with vs_current_bb := st.cs_current_bb).vs_halted`
    by metis_tac[vs_halted_current_bb_irrel] >>
  drule emit_op_CALLDATASIZE_correct >>
  disch_then (qspec_then `ss with vs_current_bb := st.cs_current_bb` assume_tac) >>
  first_x_assum drule >> strip_tac >>
  qexists_tac `ss'` >> simp[] >>
  conj_tac >- (
    mp_tac (Q.SPECL [`st`, `cs1`, `v`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
                CALLDATASIZE_run_observable) >>
    impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
    simp[vs_halted_current_bb_irrel]) >>
  conj_tac >- (
    mp_tac (Q.SPECL [`st`, `cs1`, `v`,
                `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
                CALLDATASIZE_run_preserves_current_bb) >>
    impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
    simp[vs_halted_current_bb_irrel]) >>
  mp_tac (Q.SPECL [`emitted_insts st cs1`,
              `ss with vs_current_bb := st.cs_current_bb`, `ss'`]
              run_inst_seq_ok_implies_not_halted) >>
  impl_keep_tac >- simp[vs_halted_current_bb_irrel] >>
  simp[vs_halted_current_bb_irrel]
QED

(* ===== Boundary lemmas for compile_entry_point_kwargs_correct Phase 5 ===== *)

(* OK exit: Combined CDS+init_kwargs prefix completes, then JMP exits
   to the external common_label. Mirrors compile_entry_point_kwargs_nil_correct
   but with the combined prefix (emitted_insts st cs2) instead of just CDS. *)
Theorem kwargs_ok_exit[local]:
  ∀st st' cs2 ss ss1' common_label ctx.
    run_inst_seq (emitted_insts st cs2) (ss with vs_current_bb := st.cs_current_bb) = OK ss1' ∧
    ss1'.vs_current_bb = st.cs_current_bb ∧
    same_blocks st st' ∧ same_blocks cs2 st' ∧ same_blocks st cs2 ∧
    compile_state_ok st' ∧ compile_state_ok st ∧ compile_state_ok cs2 ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2 ++ emitted_insts cs2 st' ∧
    cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2 ∧
    label_external cs2 common_label ∧
    cs2.cs_current_bb = st.cs_current_bb ∧
    emit_inst JMP [Label common_label] [] cs2 = ((), st') ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2) ∧
    fresh_vars_wrt st ss ∧ fresh_vars_wrt cs2 ss1' ∧
    ¬ss.vs_halted ∧ ¬ss1'.vs_halted ∧
    observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss1' ∧
    ss1'.vs_call_ctx = ss.vs_call_ctx
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      ss'.vs_current_bb = common_label ∧
      observable_equiv ss ss' ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt strip_tac >>
  (* Lookup current block *)
  `st'.cs_current_bb = st.cs_current_bb ∧ st'.cs_blocks = st.cs_blocks`
    by fs[exprLoweringPropsTheory.same_blocks_def] >>
  `¬MEM st.cs_current_bb (MAP (λb. b.bb_label) st'.cs_blocks)`
    by metis_tac[current_bb_not_in_blocks_MAP] >>
  `lookup_block st.cs_current_bb (assemble_blocks st') =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>`
    by (irule lookup_block_assemble_current >> simp[]) >>
  qabbrev_tac `bb = <|bb_label := st.cs_current_bb;
                       bb_instructions := st'.cs_current_insts|>` >>
  (* Derive bb.bb_instructions for get_instruction_append *)
  `bb.bb_instructions = st'.cs_current_insts` by simp[Abbr `bb`] >>
  (* get_instruction for the prefix *)
  `∀k. k < LENGTH (emitted_insts st cs2) ⇒
       get_instruction bb (LENGTH st.cs_current_insts + k) =
         SOME (EL k (emitted_insts st cs2))`
    by metis_tac[get_instruction_append] >>
  (* jmp_external_exits_fragment from (cs2, ss1') *)
  drule jmp_external_exits_fragment >>
  disch_then (qspecl_then [`ctx`, `ss1'`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_compiled_fragment _ _ _ _ fuel' = OK ss2` >>
  qexistsl [`fuel'`, `ss2`] >> simp[] >>
  (* Bridge: rcf(st,ss,fuel') = rcf(cs2,ss1',fuel') = OK ss2 *)
  `run_compiled_fragment ctx st st' ss fuel' =
    run_compiled_fragment ctx cs2 st' ss1' fuel'`
    by (irule nil_kwargs_prefix_bridge >>
        simp[Abbr `bb`] >>
        fs[exprLoweringPropsTheory.same_blocks_def] >>
        metis_tac[arithmeticTheory.ADD_COMM]) >>
  simp[] >>
  (* observable_equiv: from (ss with bb) ≡ ss2, derive ss ≡ ss2 *)
  `observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss2`
    by (irule observable_equiv_trans >>
        qexists `ss1'` >> simp[]) >>
  irule observable_equiv_trans >>
  qexists `ss with vs_current_bb := st.cs_current_bb` >>
  conj_tac >- simp[observable_equiv_current_bb_irrel, observable_equiv_def] >>
  simp[]
QED

(* Abort exit: Combined CDS+init_kwargs prefix aborts, so the fragment aborts.
   Proof mirrors rcf_abort_from_subprefix_abort but specialized: no messy
   lemma application with drule, just direct block lookup + exec_block abort. *)
Theorem kwargs_abort_exit[local]:
  ∀st st' cs2 ss ss1' a ctx fuel.
    run_inst_seq (emitted_insts st cs2) (ss with vs_current_bb := st.cs_current_bb) =
      Abort a ss1' ∧
    same_blocks st st' ∧ same_blocks cs2 st' ∧
    compile_state_ok st' ∧ compile_state_ok st ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2 ++ emitted_insts cs2 st' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2) ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted
    ⇒
    ∃ss''.
      run_compiled_fragment ctx st st' ss fuel = Abort a ss''
Proof
  rpt strip_tac >>
  `same_blocks st cs2`
    by metis_tac[emitHelperPropsTheory.same_blocks_trans,
                 exprLoweringPropsTheory.same_blocks_def] >>
  `fresh_vars_wrt st (ss with vs_current_bb := st.cs_current_bb)`
    by metis_tac[fresh_vars_wrt_current_bb_irrel] >>
  `(ss with vs_current_bb := st.cs_current_bb).vs_current_bb = st.cs_current_bb`
    by simp[venom_state_component_equality] >>
  `¬(ss with vs_current_bb := st.cs_current_bb).vs_halted`
    by metis_tac[vs_halted_current_bb_irrel] >>
  drule_all rcf_abort_from_subprefix_abort >>
  strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  metis_tac[run_compiled_fragment_vs_current_bb_irrel]
QED

(* Compose two-phase execution: CDS prefix then init_kwargs *)

Theorem run_inst_seq_append_ok[local]:
  !is1 is2 ss ss1 ss2.
    run_inst_seq is1 ss = OK ss1 ==>
    run_inst_seq is2 ss1 = OK ss2 ==>
    run_inst_seq (is1 ++ is2) ss = OK ss2
Proof
  metis_tac[exprLoweringPropsTheory.run_inst_seq_append]
QED

Theorem run_inst_seq_append_abort[local]:
  !is1 is2 ss ss1 a ss2.
    run_inst_seq is1 ss = OK ss1 ==>
    run_inst_seq is2 ss1 = Abort a ss2 ==>
    run_inst_seq (is1 ++ is2) ss = Abort a ss2
Proof
  metis_tac[exprLoweringPropsTheory.run_inst_seq_append]
QED

(* ===== Abstraction predicates for kwargs prefix phase ===== *)

Definition kwargs_prefix_layout_def:
  kwargs_prefix_layout st cs2 common_label ⇔
    compile_state_ok cs2 ∧
    same_blocks st cs2 ∧
    label_external cs2 common_label ∧
    cs2.cs_current_bb = st.cs_current_bb ∧
    cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2 ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2)
End

Definition kwargs_prefix_ok_def:
  kwargs_prefix_ok st cs2 ss ss2 ⇔
    run_inst_seq (emitted_insts st cs2)
      (ss with vs_current_bb := st.cs_current_bb) = OK ss2 ∧
    ss2.vs_current_bb = st.cs_current_bb ∧
    fresh_vars_wrt cs2 ss2 ∧
    observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss2 ∧
    ss2.vs_call_ctx = ss.vs_call_ctx ∧
    ¬ss2.vs_halted
End

Definition kwargs_prefix_abort_def:
  kwargs_prefix_abort st cs2 ss ss2 ⇔
    run_inst_seq (emitted_insts st cs2)
      (ss with vs_current_bb := st.cs_current_bb) = Abort Revert_abort ss2
End

(* Standalone composition lemmas: clean proofs with small contexts.
   Avoids fn-th closures and by-blocks in the main proof. *)

Theorem kwargs_compose_ok[local]:
  ∀st cs1 cs2 ss ss1 ss1'.
    emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2 ∧
    run_inst_seq (emitted_insts st cs1) (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
    run_inst_seq (emitted_insts cs1 cs2) ss1 = OK ss1'
    ⇒
    run_inst_seq (emitted_insts st cs2) (ss with vs_current_bb := st.cs_current_bb) = OK ss1'
Proof
  rpt strip_tac >>
  qpat_x_assum `emitted_insts st cs2 = _ ++ _`
    (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_append_ok >>
  qexists `ss1` >> simp[]
QED

Theorem kwargs_compose_abort[local]:
  ∀st cs1 cs2 ss ss1 ss1'.
    emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2 ∧
    run_inst_seq (emitted_insts st cs1) (ss with vs_current_bb := st.cs_current_bb) = OK ss1 ∧
    run_inst_seq (emitted_insts cs1 cs2) ss1 = Abort Revert_abort ss1'
    ⇒
    run_inst_seq (emitted_insts st cs2) (ss with vs_current_bb := st.cs_current_bb) =
      Abort Revert_abort ss1'
Proof
  rpt strip_tac >>
  qpat_x_assum `emitted_insts st cs2 = _ ++ _`
    (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_append_abort >>
  qexists `ss1` >> simp[]
QED

(* Packages CDS + init_kwargs into one lemma with compact interface.
   Uses strip_tac to naturally split ∨ from init_kwargs result. *)
Theorem kwargs_prefix_phase_correct[local]:
  ∀cenv kwarg_vars calldata_offset kwargs_from_calldata common_label
    hi_op st cs1 cs2 ss.
    emit_op CALLDATASIZE [] st = (hi_op, cs1) ∧
    compile_init_kwargs cenv kwarg_vars calldata_offset
      kwargs_from_calldata hi_op cs1 = ((), cs2) ∧
    compile_state_ok st ∧
    label_external st common_label ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    kwargs_prefix_layout st cs2 common_label ∧
    ((∃ss2. kwargs_prefix_ok st cs2 ss ss2) ∨
     (∃ss2. kwargs_prefix_abort st cs2 ss ss2))
Proof
  rpt gen_tac >> strip_tac >>
  (* Phase 1: CDS structural facts *)
  `inst_extends st cs1` by metis_tac[inst_extends_emit_op] >>
  `compile_state_ok cs1` by metis_tac[compile_state_ok_emit_op] >>
  `same_blocks st cs1` by metis_tac[emit_op_same_blocks] >>
  `label_external cs1 common_label` by metis_tac[label_external_emit_op] >>
  `cs1.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs1`
    by fs[inst_extends_def] >>
  `EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs1) ∧
   EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs1)`
    by metis_tac[emit_op_CALLDATASIZE_everything_pure,
                 pure_every_imp_not_terminator,
                 pure_every_imp_not_invoke] >>
  (* Phase 2: CDS execution *)
  drule CDS_phase_ok_simple >>
  disch_then (qspec_then `ss` mp_tac) >>
  (impl_tac >- simp[vs_halted_current_bb_irrel]) >>
  strip_tac >>
  rename1 `OK ss_cds` >>
  (* Phase 3: drule_all matches all antecedents from assumptions.
     strip_tac splits the conclusion's ∧ into assumptions and ∨ into subgoals. *)
  drule_all compile_init_kwargs_correct >>
  strip_tac >-
  (* OK subgoal from init_kwargs *)
  (rename1 `OK ss_kw` >>
   (* Phase 4: derive layout facts *)
   `same_blocks st cs2`
     by metis_tac[emitHelperPropsTheory.same_blocks_trans] >>
   `st.cs_next_label ≤ cs2.cs_next_label`
     by metis_tac[compile_state_ok_emit_op] >>
   `label_external cs2 common_label`
     by metis_tac[label_external_same_blocks,
                  emitHelperPropsTheory.same_blocks_trans] >>
   `cs2.cs_current_bb = st.cs_current_bb`
     by fs[exprLoweringPropsTheory.same_blocks_def] >>
   `emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2`
     by metis_tac[emitted_insts_append] >>
   `cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2`
     by simp[listTheory.APPEND_ASSOC] >>
   `EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2)`
     by metis_tac[listTheory.EVERY_APPEND] >>
   conj_tac >- simp[kwargs_prefix_layout_def] >>
   (* Prove combined execution result before expanding kwargs_prefix_ok *)
   `run_inst_seq (emitted_insts st cs2)
     (ss with vs_current_bb := st.cs_current_bb) = OK ss_kw`
     by (qpat_x_assum `emitted_insts st cs2 = _ ++ _`
           (fn th => once_rewrite_tac [th]) >>
         irule run_inst_seq_append_ok >>
         qexists_tac `ss_cds` >> simp[]) >>
   disj1_tac >>
   qexists_tac `ss_kw` >>
   simp[kwargs_prefix_ok_def] >>
   (* Remaining from kwargs_prefix_ok_def after simp auto-closes some:
      vs_current_bb, observable_equiv *)
   `(ss with vs_current_bb := st.cs_current_bb).vs_current_bb = st.cs_current_bb`
     by simp[] >>
   `ss_kw.vs_current_bb = (ss with vs_current_bb := st.cs_current_bb).vs_current_bb`
     by metis_tac[run_inst_seq_preserves_current_bb] >>
   simp[] >>
   irule observable_equiv_trans >>
   qexists_tac `ss_cds` >> simp[]) >>
  (* Abort subgoal from init_kwargs *)
  rename1 `Abort Revert_abort ss_kw` >>
  (* Phase 4: derive layout facts *)
  `same_blocks st cs2`
    by metis_tac[emitHelperPropsTheory.same_blocks_trans] >>
  `st.cs_next_label ≤ cs2.cs_next_label`
    by metis_tac[compile_state_ok_emit_op] >>
  `label_external cs2 common_label`
    by metis_tac[label_external_same_blocks,
                 emitHelperPropsTheory.same_blocks_trans] >>
  `cs2.cs_current_bb = st.cs_current_bb`
    by fs[exprLoweringPropsTheory.same_blocks_def] >>
  `emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2`
    by metis_tac[emitted_insts_append] >>
  `cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2`
    by simp[listTheory.APPEND_ASSOC] >>
  `EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs2) ∧
   EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs2)`
    by metis_tac[listTheory.EVERY_APPEND] >>
  conj_tac >- simp[kwargs_prefix_layout_def] >>
  (* Abort disjunct *)
  disj2_tac >>
  qexists_tac `ss_kw` >>
  simp[kwargs_prefix_abort_def] >>
  qpat_x_assum `emitted_insts st cs2 = _ ++ _`
    (fn th => once_rewrite_tac [th]) >>
  irule run_inst_seq_append_abort >>
  qexists_tac `ss_cds` >> simp[]
QED

(* OK exit: unpack predicates and inline kwargs_ok_exit proof:
   jmp_external_exits_fragment on (cs2,ss2) + nil_kwargs_prefix_bridge *)
Theorem kwargs_ok_exit_compact[local]:
  ∀st cs2 st' ss ss2 common_label ctx.
    emit_inst JMP [Label common_label] [] cs2 = ((), st') ∧
    compile_state_ok st ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted ∧
    kwargs_prefix_layout st cs2 common_label ∧
    kwargs_prefix_ok st cs2 ss ss2
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      ss'.vs_current_bb = common_label ∧
      observable_equiv ss ss' ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  (* Unpack definition predicates *)
  qpat_x_assum `kwargs_prefix_layout _ _ _`
    (STRIP_ASSUME_TAC o REWRITE_RULE[kwargs_prefix_layout_def]) >>
  qpat_x_assum `kwargs_prefix_ok _ _ _ _`
    (STRIP_ASSUME_TAC o REWRITE_RULE[kwargs_prefix_ok_def]) >>
  (* Block lookup: need same_blocks st st' from same_blocks st cs2 + emit_inst *)
  `same_blocks cs2 st'`
    by metis_tac[emit_inst_extends, exprLoweringPropsTheory.same_blocks_def] >>
  `same_blocks st st'`
    by metis_tac[emitHelperPropsTheory.same_blocks_trans] >>
  `st'.cs_current_bb = st.cs_current_bb ∧ st'.cs_blocks = st.cs_blocks`
    by fs[exprLoweringPropsTheory.same_blocks_def] >>
  `¬MEM st.cs_current_bb (MAP (λb. b.bb_label) st'.cs_blocks)`
    by metis_tac[current_bb_not_in_blocks_MAP] >>
  `lookup_block st.cs_current_bb (assemble_blocks st') =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := st'.cs_current_insts|>`
    by (irule lookup_block_assemble_current >> simp[]) >>
  qabbrev_tac `bb = <|bb_label := st.cs_current_bb;
                       bb_instructions := st'.cs_current_insts|>` >>
  `bb.bb_instructions = st'.cs_current_insts` by simp[Abbr `bb`] >>
  (* Derive three-way instruction decomposition from emit_inst_extends *)
  `st'.cs_current_insts =
    st.cs_current_insts ++ emitted_insts st cs2 ++
    [mk_inst cs2.cs_next_id JMP [Label common_label] []]`
    by (imp_res_tac emit_inst_extends >>
        imp_res_tac emitted_insts_emit_inst >>
        fs[listTheory.APPEND_ASSOC]) >>
  (* get_instruction via boundary lemma — matching nil_kwargs pattern *)
  `∀k. k < LENGTH (emitted_insts st cs2) ⇒
       get_instruction bb (LENGTH st.cs_current_insts + k) =
         SOME (EL k (emitted_insts st cs2))`
    by (rpt strip_tac >>
        irule get_instruction_append >>
        simp[Abbr `bb`] >>
        qexists `[mk_inst cs2.cs_next_id JMP [Label common_label] []]` >>
        simp[listTheory.APPEND_ASSOC]) >>
  (* Derive same_blocks current_bb fact *)
  `st.cs_current_bb = cs2.cs_current_bb` by fs[exprLoweringPropsTheory.same_blocks_def] >>
  (* JMP exit from (cs2, ss2) *)
  drule jmp_external_exits_fragment >>
  disch_then (qspecl_then [`ctx`, `ss2`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_compiled_fragment _ _ _ _ fuel' = OK ss2'` >>
  (* Bridge: rcf from (st, ss) equals rcf from (cs2, ss2) *)
  `run_compiled_fragment ctx st st' ss fuel' =
    run_compiled_fragment ctx cs2 st' ss2 fuel'`
    by (drule_all nil_kwargs_prefix_bridge >>
        simp[exprLoweringPropsTheory.same_blocks_def] >>
        strip_tac >> simp[]) >>
  (* Assemble final result *)
  qexistsl [`fuel'`, `ss2'`] >> simp[] >>
  (* Close observable_equiv ss ss2' via transitivity through ss2 *)
  `observable_equiv (ss with vs_current_bb := st.cs_current_bb) ss2'`
    by metis_tac[observable_equiv_trans] >>
  drule_all observable_equiv_through_bb_override >> simp[]
QED

(* Abort exit: unpack predicates and inline kwargs_abort_exit proof:
   rcf_abort_from_subprefix_abort on the prefix abort *)
Theorem kwargs_abort_exit_compact[local]:
  ∀st cs2 st' ss ss2 common_label ctx fuel.
    emit_inst JMP [Label common_label] [] cs2 = ((), st') ∧
    compile_state_ok st ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted ∧
    kwargs_prefix_layout st cs2 common_label ∧
    kwargs_prefix_abort st cs2 ss ss2
    ⇒
    ∃ss'.
      run_compiled_fragment ctx st st' ss fuel = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  (* Unpack definition predicates *)
  qpat_x_assum `kwargs_prefix_layout _ _ _`
    (STRIP_ASSUME_TAC o REWRITE_RULE[kwargs_prefix_layout_def]) >>
  qpat_x_assum `kwargs_prefix_abort _ _ _ _`
    (STRIP_ASSUME_TAC o REWRITE_RULE[kwargs_prefix_abort_def]) >>
  (* Derive JMP bridge facts *)
  `compile_state_ok st'` by metis_tac[compile_state_ok_emit_inst] >>
  `same_blocks cs2 st'`
    by metis_tac[emit_inst_extends, exprLoweringPropsTheory.same_blocks_def] >>
  `same_blocks st st'`
    by metis_tac[emitHelperPropsTheory.same_blocks_trans] >>
  `st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2 ++ emitted_insts cs2 st'`
    by metis_tac[emit_inst_extends, emitted_insts_emit_inst,
                 emitted_insts_append, listTheory.APPEND_ASSOC] >>
  (* Bridge: via rcf_abort_from_subprefix_abort *)
  `fresh_vars_wrt st (ss with vs_current_bb := st.cs_current_bb)`
    by metis_tac[fresh_vars_wrt_current_bb_irrel] >>
  `(ss with vs_current_bb := st.cs_current_bb).vs_current_bb = st.cs_current_bb`
    by simp[venom_state_component_equality] >>
  `¬(ss with vs_current_bb := st.cs_current_bb).vs_halted`
    by metis_tac[vs_halted_current_bb_irrel] >>
  drule_all rcf_abort_from_subprefix_abort >>
  strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  metis_tac[run_compiled_fragment_vs_current_bb_irrel]
QED

Theorem compile_entry_point_kwargs_correct:
  ∀ cenv kwarg_vars calldata_offset kwargs_from_calldata common_label
    ss st st' ctx.
    compile_entry_point_kwargs cenv kwarg_vars calldata_offset
                               kwargs_from_calldata common_label st = ((), st') ∧
    compile_state_ok st ∧
    label_external st common_label ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel ss'.
      (run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
       ss'.vs_current_bb = common_label ∧
       observable_equiv ss ss' ∧
       ss'.vs_call_ctx = ss.vs_call_ctx ∧
       ¬ss'.vs_halted ∧
       fresh_vars_wrt st' ss' ∧
       compile_state_ok st')
      ∨
      (run_compiled_fragment ctx st st' ss fuel = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_entry_point_kwargs_compile >> strip_tac >>
  (* strip_tac on kwargs_prefix_phase_correct splits the ∨ conclusion
     into 2 subgoals: OK branch gets kwargs_prefix_ok, Abort branch
     gets kwargs_prefix_abort. See LEARNINGS: STRIP_TAC-SPLITS-DISJUNCTION. *)
  drule_all kwargs_prefix_phase_correct >> strip_tac
  >- (* OK branch: kwargs_prefix_layout + kwargs_prefix_ok in assumptions *)
   (`emit_inst JMP [Label common_label] [] cs2 = ((), st')` by simp[] >>
    drule_all kwargs_ok_exit_compact >>
    disch_then (qspec_then `ctx` strip_assume_tac) >>
    qexistsl [`fuel`, `ss'`] >> disj1_tac >> simp[])
  >- (* Abort branch: kwargs_prefix_layout + kwargs_prefix_abort in assumptions *)
   (`emit_inst JMP [Label common_label] [] cs2 = ((), st')` by simp[] >>
    drule_all kwargs_abort_exit_compact >>
    strip_tac >>
    qexists `0` >> metis_tac[])
QED

(* Record update does not affect fields not mentioned in the update.
   Proved via EVAL which handles the HOL4 record desugaring. *)
Theorem venom_state_with_bb_idx[local]:
  ∀ss bb idx.
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_vars = ss.vs_vars ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_memory = ss.vs_memory ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_accounts = ss.vs_accounts ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_call_ctx = ss.vs_call_ctx ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_labels = ss.vs_labels ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_returndata = ss.vs_returndata ∧
    ((ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_halted ⇔ ss.vs_halted) ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_logs = ss.vs_logs ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_transient = ss.vs_transient ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_immutables = ss.vs_immutables ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_current_bb = bb ∧
    (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>).vs_inst_idx = idx
Proof
  rpt gen_tac >> simp[venom_state_component_equality]
QED


Theorem observable_equiv_with_bb_idx[local]:
  ∀ss bb idx.
    observable_equiv ss (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>)
Proof
  simp[observable_equiv_def, venom_state_with_bb_idx]
QED

Theorem fresh_vars_wrt_with_bb_idx[local]:
  ∀st ss bb idx.
    fresh_vars_wrt st ss ⇒ fresh_vars_wrt st (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>)
Proof
  simp[fresh_vars_wrt_def, venom_state_with_bb_idx]
QED

(* The EVERY condition for run_inst_seq_preserves_observable_and_memory
   when the instruction list comes from emit_op EQ.
   Proved in isolation to avoid simp issues in the large selector_step proof. *)

Theorem emit_op_EQ_everything_pure[local]:
  !op1 op2 st v st'.
    emit_op EQ [op1; op2] st = (v,st') ==>
    EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                                  SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                                  ISZERO; AND; OR; XOR; NOT;
                                  CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                                  GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                                  NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                                  MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st st')
Proof
  rpt strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  simp[mk_inst_opcode]
QED

(* Combined lemma: emit_op_EQ correctness + observable/memory/call_ctx/halted preservation.
   Proved in a small context to avoid simp timeouts in the large selector_step proof. *)
Theorem emit_op_EQ_correct_with_preserves[local]:
  !op1 op2 v1 v2 st v st' ss.
    emit_op EQ [op1; op2] st = (v,st') /\
    eval_operand op1 ss = SOME v1 /\ eval_operand op2 ss = SOME v2 /\
    fresh_vars_wrt st ss /\ ~ss.vs_halted
    ==>
    ?ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand v ss' = SOME (bool_to_word (v1 = v2)) /\
      same_blocks st st' /\ fresh_vars_wrt st' ss' /\
      observable_equiv ss ss' /\ ss'.vs_memory = ss.vs_memory /\
      ss'.vs_call_ctx = ss.vs_call_ctx /\ ~ss'.vs_halted /\
      (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  qexists `ss'` >> simp[] >>
  (* Apply run_inst_seq_preserves_observable_and_memory.
     Use drule on the EVERY-pure helper to avoid the qspecl_then/irule issue. *)
  qspecl_then [`emitted_insts st st'`, `ss`, `ss'`] mp_tac
    run_inst_seq_preserves_observable_and_memory >>
  impl_tac >-
    (conj_tac >- simp[] >>
     conj_tac >- metis_tac[emit_op_EQ_everything_pure] >>
     simp[]) >>
  simp[]
QED

(* ===== Bridge lemma for shifting state under update_var ===== *)

Theorem update_var_shift_commutes[local]:
  !x v s bb idx.
    update_var x v (s with <|vs_current_bb := bb; vs_inst_idx := idx|>) =
    (update_var x v s) with <|vs_current_bb := bb; vs_inst_idx := idx|>
Proof
  simp[update_var_def, venom_state_component_equality]
QED

Theorem eval_op_double_update[local]:
  ∀op ss bb idx.
    eval_operand op (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>) =
    eval_operand op ss
Proof
  Cases >> simp[eval_operand_def, lookup_var_def, venom_state_component_equality]
QED

(* For a specific mk_inst with known EQ opcode, step_inst_base on the
   shifted state produces the shifted update_var result.
   Proved using exec_pure2_ok directly — no need to unfold step_inst_base_def
   across all opcode cases since the opcode is a constant EQ. *)
Theorem step_inst_base_mk_inst_EQ_shift[local]:
  !id op1 op2 out ss bb idx v1 v2.
    eval_operand op1 ss = SOME v1 /\ eval_operand op2 ss = SOME v2
    ==>
    step_inst_base (mk_inst id EQ [op1; op2] [out])
      (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>) =
    OK ((update_var out (bool_to_word (v1 = v2)) ss) with
         <|vs_current_bb := bb; vs_inst_idx := idx|>)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, mk_inst_opcode] >>
  (* Establish eval_operand facts on shifted state for exec_pure2_ok *)
  `eval_operand op1 (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>) = SOME v1`
    by metis_tac[eval_op_double_update] >>
  `eval_operand op2 (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>) = SOME v2`
    by metis_tac[eval_op_double_update] >>
  simp[exec_pure2_def, update_var_shift_commutes]
QED

(* Selector step: one EQ/JNZ pair.
   Apply emit_op_EQ_correct on bare ss, get ss_result, then bridge
   to shifted state using step_inst_base_mk_inst_EQ_shift.
   Uses irule instead of drule_all to avoid large-context matching issues. *)
(* Helper: fresh_vars_wrt_advance with no variable clash.
   Wraps emitHelperPropsTheory.fresh_vars_wrt_advance but
   avoids the st' variable naming issue when st' is already bound. *)
Theorem fresh_vars_wrt_advance_cs[local]:
  !st0 cs1_0 ss0 name0 n0 w0.
    fresh_vars_wrt st0 ss0 /\ name0 = STRING #"%" (toString n0) /\
    n0 = st0.cs_next_var /\ cs1_0.cs_next_var > st0.cs_next_var ==>
    fresh_vars_wrt cs1_0 (update_var name0 w0 ss0)
Proof
  metis_tac[fresh_vars_wrt_advance]
QED

(* eval_operand preserved through update_var of the fresh output variable.
   Bakes in the name = STRING #"%" (toString st.cs_next_var) pattern
   so no name/number existentials remain after match_mp_tac. *)
Theorem eval_operand_preserved_by_fresh_update[local]:
  !op v st ss w.
    eval_operand op ss = SOME v /\ fresh_vars_wrt st ss
    ==> eval_operand op (update_var (STRING #"%" (toString st.cs_next_var)) w ss) = SOME v
Proof
  rpt strip_tac >>
  qspecl_then [`op`,`v`,`w`,`STRING #"%" (toString st.cs_next_var)`,
                `st.cs_next_var`,`ss`,`st`] mp_tac eval_operand_update_fresh >>
  simp[] >> decide_tac
QED
Theorem selector_jnz_rcf_eqn_renamed[local]:
  !c s1 s2 s3 n blk ei ji sr mo cv ml nl ji2 ix.
    lookup_block s1.cs_current_bb (assemble_blocks s2) = SOME blk /\
    fresh_vars_wrt s1 s3 /\ ~s3.vs_halted /\
    run_inst_seq [ei] (s3 with <|vs_current_bb := s1.cs_current_bb;
                                  vs_inst_idx := ix|>) = OK sr /\
    EVERY (\i. ~is_terminator i.inst_opcode) [ei] /\
    EVERY (\i. i.inst_opcode <> INVOKE) [ei] /\
    (!k. k < 1 ==> get_instruction blk (ix + k) = SOME (EL k [ei])) /\
    get_instruction blk (ix + 1) = SOME (mk_inst ji2 JNZ [mo; Label ml; Label nl] []) /\
    eval_operand mo sr = SOME cv /\ ~sr.vs_halted /\ ix = LENGTH s1.cs_current_insts
    ==> run_compiled_fragment c s1 s2 s3 n =
          if cv <> 0w then run_fragment_blocks n c (assemble_function s1 s2) (jump_to ml sr)
          else run_fragment_blocks n c (assemble_function s1 s2) (jump_to nl sr)
Proof
  cheat
QED


Theorem jump_to_ignores_current_bb_idx[local]:
  !lbl ss bb idx.
    ss.vs_current_bb = bb ==>
    jump_to lbl (ss with <|vs_current_bb := bb; vs_inst_idx := idx|>) =
    jump_to lbl ss
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem selector_step_jnz_split[local]:
  !method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3 cs4
    old1 cs5 cs6 old2 cs7 st_mid st' fallback_lbl ctx ss val.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) /\
    fresh_label "match" cs1 = (match_lbl,cs2) /\
    fresh_label "next" cs2 = (next_lbl,cs3) /\
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) /\
    new_block match_lbl cs4 = (old1,cs5) /\
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) /\
    new_block next_lbl cs6 = (old2,cs7) /\
    compile_selector_checks method_id rest cs7 = ((), st_mid) /\
    emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') /\
    compile_state_ok st /\
    label_external st fn_label /\
    label_external st fallback_lbl /\
    EVERY (label_external st) (MAP SND rest) /\
    fresh_vars_wrt st ss /\ ~ss.vs_halted /\
    ss.vs_current_bb = st.cs_current_bb /\
    eval_operand method_id ss = SOME val
    ==>
    ?ss1.
      (!fuel.
        run_compiled_fragment ctx st st' ss fuel =
        if val = n2w sel then
          run_fragment_blocks fuel ctx (assemble_function st st') (jump_to match_lbl ss1)
        else
          run_fragment_blocks fuel ctx (assemble_function st st') (jump_to next_lbl ss1)) /\
      eval_operand match_op ss1 = SOME (bool_to_word (val = n2w sel)) /\
      ~ss1.vs_halted /\
      fresh_vars_wrt cs1 ss1 /\
      observable_equiv ss ss1 /\
      ss1.vs_memory = ss.vs_memory /\
      ss1.vs_call_ctx = ss.vs_call_ctx /\
      (!op w. eval_operand op ss = SOME w ==> eval_operand op ss1 = SOME w)
Proof
  cheat
QED

Theorem run_compiled_fragment_eq_run_fragment_blocks:
  !ctx st st' ss fuel.
    lookup_block st.cs_current_bb (assemble_blocks st') <> NONE /\
    ss.vs_current_bb = st.cs_current_bb /\
    ss.vs_inst_idx = 0 /\
    st.cs_current_insts = [] /\
    ~ss.vs_halted
    ==>
    run_compiled_fragment ctx st st' ss fuel =
      run_fragment_blocks (SUC fuel) ctx (assemble_function st st') ss
Proof
  rpt strip_tac >> simp[Once run_compiled_fragment_def] >>
  Cases_on `lookup_block st.cs_current_bb (assemble_blocks st')` >> gvs[] >>
  drule run_fragment_blocks_eq_compiled_fragment >> simp[assemble_function_def]
QED
Theorem selector_checks_step_preserves_match_block[local]:
  !method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3 cs4
   old1 cs5 cs6 old2 cs7 st_mid.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) /\
    fresh_label "match" cs1 = (match_lbl,cs2) /\
    fresh_label "next" cs2 = (next_lbl,cs3) /\
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) /\
    new_block match_lbl cs4 = (old1,cs5) /\
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) /\
    new_block next_lbl cs6 = (old2,cs7) /\
    compile_selector_checks method_id rest cs7 = ((),st_mid) /\
    compile_state_ok st
    ==>
    FIND (\b. b.bb_label = match_lbl) st_mid.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>
Proof
  rpt strip_tac >>
  `compile_state_ok cs4 /\
   bound_labels cs4 = bound_labels st /\
   cs4.cs_next_label = st.cs_next_label + 2 /\
   label_external cs4 match_lbl /\
   label_external cs4 next_lbl /\
   next_lbl <> match_lbl`
    by metis_tac[step_emit_chain_state_ok] >>
  `cs5.cs_current_bb = match_lbl /\ cs5.cs_current_insts = []`
    by metis_tac[new_block_props] >>
  `compile_state_ok cs5` by metis_tac[compile_state_ok_new_block] >>
  `compile_state_ok cs6 /\
   bound_labels cs6 = bound_labels cs5 /\
   cs6.cs_blocks = cs5.cs_blocks /\
   cs6.cs_current_bb = cs5.cs_current_bb`
    by metis_tac[compile_state_ok_emit_inst] >>
  `compile_state_ok cs7 /\
   bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st /\
   cs7.cs_next_label = st.cs_next_label + 2`
    by metis_tac[step_chain_cs7_ok] >>
  `match_lbl IN bound_labels cs7` by simp[] >>
  `match_lbl NOTIN compiler_labels_future cs7.cs_next_label`
    by metis_tac[bound_labels_not_in_future] >>
  `cs7.cs_current_bb = next_lbl` by metis_tac[new_block_props] >>
  `match_lbl <> cs7.cs_current_bb` by simp[] >>
  `cs7.cs_blocks = <|bb_label := cs6.cs_current_bb; bb_instructions := cs6.cs_current_insts|> :: cs6.cs_blocks`
    by metis_tac[new_block_props] >>
  `FIND (\b. b.bb_label = match_lbl) cs7.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>`
    by simp[listTheory.FIND_thm] >>
  irule compile_selector_checks_blocks_preserved >>
  qexistsl [`method_id`, `rest`, `cs7`] >>
  metis_tac[]
QED

Theorem selector_checks_match_find[local]:
  ∀method_id sel fn_label rest st st_mid match_op cs1 match_lbl cs2
    next_lbl cs3 cs4 old1 cs5 cs6 old2 cs7.
    compile_selector_checks method_id rest cs7 = ((),st_mid) ∧
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    new_block match_lbl cs4 = (old1,cs5) ∧
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
    new_block next_lbl cs6 = (old2,cs7) ∧
    compile_state_ok st
    ⇒
    FIND (\b. b.bb_label = match_lbl) st_mid.cs_blocks =
      SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL
    [`method_id`,`sel`,`fn_label`,`rest`,`st`,`match_op`,`cs1`,
     `match_lbl`,`cs2`,`next_lbl`,`cs3`,`cs4`,`old1`,`cs5`,
     `cs6`,`old2`,`cs7`,`st_mid`]
    selector_checks_step_preserves_match_block) >>
  simp[]
QED

Theorem selector_checks_step_preserves_match_block_easy[local]:
  !method_id sel fn_label rest st st_mid.
    compile_selector_checks method_id ((sel,fn_label)::rest) st = ((),st_mid) /\
    compile_state_ok st
    ==>
    ?match_lbl insts.
      match_lbl = fresh_label_output "match" st.cs_next_label /\
      FIND (\b. b.bb_label = match_lbl) st_mid.cs_blocks =
        SOME <|bb_label := match_lbl; bb_instructions := insts|>
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`method_id`,`sel`,`fn_label`,`rest`,`st`,`st_mid`]
            compile_selector_checks_cons_eqn) >>
  simp[] >> strip_tac >>
  `cs1.cs_next_label = st.cs_next_label`
    by metis_tac[compile_state_ok_emit_op] >>
  `FIND (\b. b.bb_label = match_lbl) st_mid.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>`
    by metis_tac[selector_checks_step_preserves_match_block] >>
  fs[fresh_label_def] >> metis_tac[]
QED

(* Helper: bound_labels of st_mid relative to the ORIGINAL st, not cs7.
   compile_selector_checks_bound_labels gives bounds relative to cs7,
   but we need bounds relative to st. This chains through step_chain_cs7_ok
   and bound_labels_new_block_insert_subset. *)
Theorem compile_selector_checks_step_bound_labels[local]:
  !method_id sel fn_label rest st st_mid.
    compile_selector_checks method_id ((sel,fn_label)::rest) st = ((),st_mid) /\
    compile_state_ok st
    ==>
    bound_labels st_mid SUBSET bound_labels st UNION compiler_labels_future st.cs_next_label /\
    compile_state_ok st_mid /\
    st_mid.cs_next_label >= st.cs_next_label
Proof
  rpt strip_tac >> metis_tac[compile_selector_checks_bound_labels, step_chain_cs7_ok, bound_labels_subset_trans, bound_labels_new_block_insert_subset, compiler_labels_future_mono, SUBSET_LEFT_UNION, SUBSET_RIGHT_UNION]
QED

(* Standalone lemma: if two fresh labels at offsets 0 and 1 from st.cs_next_label
   are inserted into bound_labels, the result is a subset of
   bound_labels st ∪ compiler_labels_future st.cs_next_label.
   Proved outside the massive assumption context of selector_step_facts. *)
Theorem bound_labels_two_fresh_inserts[local]:
  !st st' next_lbl match_lbl.
    compile_state_ok st /\
    bound_labels st' = next_lbl INSERT match_lbl INSERT bound_labels st /\
    st'.cs_next_label = st.cs_next_label + 2 /\
    match_lbl = fresh_label_output "match" st.cs_next_label /\
    next_lbl = fresh_label_output "next" (st.cs_next_label + 1) /\
    compile_state_ok st'
    ==> bound_labels st' SUBSET bound_labels st UNION compiler_labels_future st.cs_next_label
Proof
  rpt strip_tac >>
  match_mp_tac bound_labels_double_insert_subset >>
  qexistsl [`fresh_label_output "next" (st.cs_next_label + 1)`,
           `fresh_label_output "match" st.cs_next_label`] >>
  simp[] >>
  (* lbl1 = "next" at offset +1: chain through mono *)
  `fresh_label_output "next" (st.cs_next_label + 1) IN
   compiler_labels_future (st.cs_next_label + 1)`
    by simp[fresh_label_output_in_compiler_labels_future] >>
  `compiler_labels_future (st.cs_next_label + 1) SUBSET
   compiler_labels_future st.cs_next_label`
    by (irule compiler_labels_future_mono >> decide_tac) >>
  simp[] >>
  (* lbl2 = "match" at offset 0: directly in compiler_labels_future *)
  simp[fresh_label_output_in_compiler_labels_future]
QED

(* When bound_labels st' = bound_labels st (no INSERT), label_external is preserved *)
Theorem label_external_preserved_equal_bounds[local]:
  !st st' lbl.
    label_external st lbl /\ compile_state_ok st /\
    bound_labels st' = bound_labels st /\
    st'.cs_next_label >= st.cs_next_label /\ compile_state_ok st'
    ==> label_external st' lbl
Proof
  rpt strip_tac >>
  fs[label_external_def] >>
  metis_tac[compiler_labels_future_mono, pred_setTheory.SUBSET_DEF]
QED

(* Clean-context forward-chaining lemmas for the selector step chain.
   These are proved in a context with ONE new_block / emit_inst / fresh_label
   assumption, avoiding the imp_res_tac pollution and metis_tac timeouts
   that plague the full selector_step_facts context. *)

Theorem new_block_jmp_chain_facts[local]:
  ∀match_lbl cs4 old1 cs5 fn_label cs6.
    new_block match_lbl cs4 = (old1,cs5) ∧
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
    compile_state_ok cs4 ∧
    label_external cs4 match_lbl
    ⇒
    old1 = cs4.cs_current_bb ∧ cs5.cs_current_bb = match_lbl ∧
    cs5.cs_current_insts = [] ∧ compile_state_ok cs5 ∧
    bound_labels cs5 = match_lbl INSERT bound_labels cs4 ∧
    cs5.cs_next_label = cs4.cs_next_label ∧
    cs6.cs_current_insts = [mk_inst cs5.cs_next_id JMP [Label fn_label] []] ∧
    cs6.cs_current_bb = match_lbl ∧ cs6.cs_blocks = cs5.cs_blocks ∧
    compile_state_ok cs6 ∧ bound_labels cs6 = bound_labels cs5 ∧
    cs6.cs_next_label = cs5.cs_next_label ∧
    cs6.cs_current_bb = cs5.cs_current_bb
Proof
  rpt strip_tac >>
  drule_all new_block_props >> strip_tac >>
  drule_all compile_state_ok_new_block >> strip_tac >>
  drule_all emit_inst_extends >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >>
  simp[]
QED

Theorem fresh_label_in_future_of_orig[local]:
  ∀suffix st lbl st' orig_n.
    fresh_label suffix st = (lbl,st') ∧ compile_state_ok st ∧
    st.cs_next_label ≥ orig_n
    ⇒ lbl ∈ compiler_labels_future orig_n
Proof
  rpt strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  fs[fresh_label_output_in_compiler_labels_future]
QED

Theorem cs7_current_insts_nil[local]:
  ∀next_lbl cs6 old2 cs7.
    new_block next_lbl cs6 = (old2,cs7)
    ⇒ cs7.cs_current_insts = []
Proof
  rpt strip_tac >> drule_all new_block_props >> simp[]
QED

(* Clean-context lemma: st_mid and st' facts from cs7.
   Avoids emit_inst ambiguity in the main proof where multiple
   emit_inst assumptions exist. *)
Theorem step_tail_facts[local]:
  ∀method_id rest cs7 st_mid fallback_lbl st'.
    compile_selector_checks method_id rest cs7 = ((),st_mid) ∧
    emit_inst JMP [Label fallback_lbl] [] st_mid = ((),st') ∧
    compile_state_ok cs7
    ⇒
    compile_state_ok st_mid ∧
    bound_labels st_mid ⊆ bound_labels cs7 ∪ compiler_labels_future cs7.cs_next_label ∧
    st_mid.cs_next_label ≥ cs7.cs_next_label ∧
    compile_state_ok st' ∧ bound_labels st' = bound_labels st_mid ∧
    st'.cs_blocks = st_mid.cs_blocks ∧
    st'.cs_next_label = st_mid.cs_next_label ∧
    st'.cs_current_bb = st_mid.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_selector_checks_bound_labels >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >> simp[]
QED

(* Clean-context lemma: EVERY label_external preserved through the step
   (emit_op + 2×fresh_label + emit_inst + 2×new_block).
   Avoids drule_all ambiguity and irule antecedent-only-var issues
   in the polluted selector_step_facts context. *)
Theorem selector_step_every_label_preserved[local]:
  ∀st st' lbls match_lbl next_lbl.
    EVERY (label_external st) lbls ∧
    compile_state_ok st ∧ compile_state_ok st' ∧
    bound_labels st' = next_lbl INSERT match_lbl INSERT bound_labels st ∧
    st'.cs_next_label = st.cs_next_label + 2 ∧
    match_lbl ∈ compiler_labels_future st.cs_next_label ∧
    next_lbl ∈ compiler_labels_future st.cs_next_label
    ⇒ EVERY (label_external st') lbls
Proof
  rpt gen_tac >> strip_tac >>
  `bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label`
    by (simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
             pred_setTheory.IN_INSERT] >>
        metis_tac[]) >>
  drule EVERY_label_external_preserved >> simp[] >> decide_tac
QED

(* Clean-context wrapper for step_tail_facts:
   avoids drule_all ambiguity from multiple compile_state_ok assumptions.
   cs7 is bound uniquely from first antecedent match, so ambiguity is resolved. *)
Theorem selector_step_tail_preserved[local]:
  ∀method_id rest cs7 st_mid fallback_lbl st'.
    compile_selector_checks method_id rest cs7 = ((), st_mid) ∧
    emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') ∧
    compile_state_ok cs7
    ⇒ compile_state_ok st_mid ∧
       bound_labels st_mid ⊆ bound_labels cs7 ∪ compiler_labels_future cs7.cs_next_label ∧
       st_mid.cs_next_label ≥ cs7.cs_next_label ∧
       compile_state_ok st' ∧ bound_labels st' = bound_labels st_mid ∧
       st'.cs_blocks = st_mid.cs_blocks ∧
       st'.cs_next_label = st_mid.cs_next_label ∧
       st'.cs_current_bb = st_mid.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_selector_checks_bound_labels >> strip_tac >>
  drule_all compile_state_ok_emit_inst >> strip_tac >> simp[]
QED

(* Clean-context wrapper for bound_labels transitivity through step.
   Avoids drule ambiguity from multiple SUBSET assumptions. *)


(* Clean-context lemma: all label-space facts from emit_op + 2×fresh_label.
   Avoids drule_all ambiguity in the polluted selector_step_facts context. *)
Theorem step_label_facts[local]:
  !method_id sel st match_op cs1 match_lbl cs2 next_lbl cs3.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) /\
    fresh_label "match" cs1 = (match_lbl,cs2) /\
    fresh_label "next" cs2 = (next_lbl,cs3) /\
    compile_state_ok st
    ==>
    cs1.cs_next_label = st.cs_next_label /\ compile_state_ok cs1 /\
    match_lbl IN compiler_labels_future st.cs_next_label /\
    cs2.cs_next_label = st.cs_next_label + 1 /\ compile_state_ok cs2 /\
    cs2.cs_next_label >= st.cs_next_label /\
    next_lbl IN compiler_labels_future st.cs_next_label
Proof
  rpt gen_tac >> DISCH_THEN STRIP_ASSUME_TAC >>
  drule_all compile_state_ok_emit_op >> strip_tac >>
  drule_all fresh_label_produces_external >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[fresh_label_output_in_compiler_labels_future] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- decide_tac >>
  fs[fresh_label_def] >>
  qpat_x_assum `fresh_label_output "next" _ = next_lbl` (fn th =>
    once_rewrite_tac[GSYM th]) >>
  simp[fresh_label_output_in_compiler_labels_future]
QED

Theorem selector_step_facts[local]:
  !method_id sel fn_label rest st match_op cs1 match_lbl cs2 next_lbl cs3
     cs4 old1 cs5 cs6 old2 cs7 st_mid st' fallback_lbl.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) /\
    fresh_label "match" cs1 = (match_lbl,cs2) /\
    fresh_label "next" cs2 = (next_lbl,cs3) /\
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) /\
    new_block match_lbl cs4 = (old1,cs5) /\
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) /\
    new_block next_lbl cs6 = (old2,cs7) /\
    compile_selector_checks method_id rest cs7 = ((), st_mid) /\
    emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') /\
    compile_state_ok st /\
    label_external st fn_label /\
    label_external st fallback_lbl /\
    EVERY (label_external st) (MAP SND rest)
    ==>
    (* cs5 facts *)
    cs5.cs_current_bb = match_lbl /\ cs5.cs_current_insts = [] /\
    compile_state_ok cs5 /\
    (* cs6 facts *)
    cs6.cs_current_insts = [mk_inst cs5.cs_next_id JMP [Label fn_label] []] /\
    cs6.cs_current_bb = match_lbl /\ cs6.cs_blocks = cs5.cs_blocks /\
    compile_state_ok cs6 /\
    (* cs7 facts *)
    compile_state_ok cs7 /\ cs7.cs_current_bb = next_lbl /\ cs7.cs_current_insts = [] /\
    bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st /\
    cs7.cs_next_label = st.cs_next_label + 2 /\
    label_external cs7 fn_label /\ label_external cs7 fallback_lbl /\
    EVERY (label_external cs7) (MAP SND rest) /\
    (* st_mid facts *)
    compile_state_ok st_mid /\
    (* st' facts *)
    compile_state_ok st' /\ bound_labels st' = bound_labels st_mid /\ st'.cs_blocks = st_mid.cs_blocks /\
    (* bound_labels subset chain *)
    bound_labels st' SUBSET bound_labels st UNION compiler_labels_future st.cs_next_label /\
    (* label external implies not in assembled *)
    lookup_block fn_label (assemble_blocks st') = NONE
Proof
  rpt gen_tac >> DISCH_THEN STRIP_ASSUME_TAC >>
  (* Phase 1: cs4 facts *)
  `compile_state_ok cs4 ∧ bound_labels cs4 = bound_labels st ∧
   cs4.cs_next_label = st.cs_next_label + 2 ∧
   label_external cs4 match_lbl ∧ label_external cs4 next_lbl ∧
   next_lbl ≠ match_lbl` by
    (drule_all step_emit_chain_state_ok >> simp[]) >>
  (* Phase 2: cs7 facts *)
  `compile_state_ok cs7 ∧
   bound_labels cs7 = next_lbl INSERT match_lbl INSERT bound_labels st ∧
   cs7.cs_next_label = st.cs_next_label + 2 ∧ cs7.cs_current_bb = next_lbl ∧
   label_external cs7 fn_label` by
    (drule_all step_new_block_chain_state_ok >> simp[]) >>
  (* Phase 3: cs5 + cs6 facts *)
  `old1 = cs4.cs_current_bb ∧ cs5.cs_current_bb = match_lbl ∧
   cs5.cs_current_insts = [] ∧ compile_state_ok cs5 ∧
   bound_labels cs5 = match_lbl INSERT bound_labels cs4 ∧
   cs5.cs_next_label = cs4.cs_next_label ∧
   cs6.cs_current_insts = [mk_inst cs5.cs_next_id JMP [Label fn_label] []] ∧
   cs6.cs_current_bb = match_lbl ∧ cs6.cs_blocks = cs5.cs_blocks ∧
   compile_state_ok cs6 ∧ bound_labels cs6 = bound_labels cs5 ∧
   cs6.cs_next_label = cs5.cs_next_label ∧
   cs6.cs_current_bb = cs5.cs_current_bb` by
    (drule_all new_block_jmp_chain_facts >> simp[]) >>
  (* Phase 4: cs7 current_insts *)
  `cs7.cs_current_insts = []` by
    (drule_all cs7_current_insts_nil >> simp[]) >>
  (* Phase 5: label-space facts via clean-context lemma *)
  `cs1.cs_next_label = st.cs_next_label ∧ compile_state_ok cs1 ∧
   match_lbl IN compiler_labels_future st.cs_next_label ∧
   cs2.cs_next_label = st.cs_next_label + 1 ∧ compile_state_ok cs2 ∧
   cs2.cs_next_label ≥ st.cs_next_label ∧
   next_lbl IN compiler_labels_future st.cs_next_label` by
    (drule_all step_label_facts >> simp[]) >>
  (* Phase 5b: bound_labels subset — needed for label_external propagation *)
  `bound_labels cs7 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label`
    by (simp[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_UNION,
             pred_setTheory.IN_INSERT] >>
        metis_tac[]) >>
  (* Phase 6: label_external propagation — qspecl_then avoids drule_all ambiguity *)
  `label_external cs7 fallback_lbl` by
    (qspecl_then [`st`,`cs7`,`match_lbl`,`next_lbl`,`fallback_lbl`]
       MATCH_MP_TAC label_external_preserved_through_step >>
     simp[] >> decide_tac) >>
  `EVERY (label_external cs7) (MAP SND rest)` by
    (drule_all selector_step_every_label_preserved >> simp[] >> decide_tac) >>
  (* Phase 7: st_mid and st' via clean-context lemma *)
  `compile_state_ok st_mid ∧
   bound_labels st_mid ⊆ bound_labels cs7 ∪ compiler_labels_future cs7.cs_next_label ∧
   st_mid.cs_next_label ≥ cs7.cs_next_label ∧
   compile_state_ok st' ∧ bound_labels st' = bound_labels st_mid ∧
   st'.cs_blocks = st_mid.cs_blocks ∧
   st'.cs_next_label = st_mid.cs_next_label ∧
   st'.cs_current_bb = st_mid.cs_current_bb` by
    (drule_all selector_step_tail_preserved >> simp[]) >>
  (* Phase 8: bound_labels subset chain — qspecl_then avoids drule ambiguity *)
  `bound_labels st_mid ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label`
    by (qspecl_then [`st`,`cs7`,`st_mid`] mp_tac bound_labels_subset_trans >>
        simp[] >> decide_tac) >>
  `bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label`
    by simp[] >>
  (* Phase 9: lookup_block NONE via label_external — qspecl_then avoids ambiguity *)
  `lookup_block fn_label (assemble_blocks st') = NONE` by
    (qspecl_then [`st`,`st'`,`fn_label`] mp_tac label_external_not_in_assembled >> simp[]) >>
  rpt conj_tac >> simp[]
QED

(* FIND finds any element satisfying the predicate *)
Theorem find_mem_imp[local]:
  !P l x. MEM x l /\ P x ==> FIND P l <> NONE
Proof
  Induct_on `l` >> rw[listTheory.FIND_thm] >> Cases_on `h = x` >> fs[] >> metis_tac[]
QED

(* If lbl is in bound_labels, then lookup_block finds it in assembled blocks.
   Proved by case split on lbl = st'.cs_current_bb:
   - If equal: current_bb block is last in assemble_blocks. Use lookup_block_assemble_current.
   - If not: lbl comes from some MEM b st'.cs_blocks. Use find_mem_imp for FIND witness,
     then lookup_block_assemble_in_blocks. *)
Theorem lookup_block_MEM[local]:
  !l lbl bb. MEM bb l /\ bb.bb_label = lbl ==> lookup_block lbl l <> NONE
Proof
  Induct_on `l` >> rpt gen_tac >> strip_tac
  >- fs[]
  >- (fs[lookup_block_def] >>
      Cases_on `h.bb_label = lbl` >> simp[listTheory.FIND_thm]
      >- (Cases_on `h = bb` >> fs[])
      >- (`MEM bb l` by fs[] >>
          first_x_assum drule >>
          pop_assum (fn th => REWRITE_TAC[th]) >>
          simp[listTheory.FIND_thm]))
QED

Theorem bound_labels_imp_lookup[local]:
  !st' lbl. lbl IN bound_labels st' ==> lookup_block lbl (assemble_blocks st') <> NONE
Proof
  rpt strip_tac >>
  `?bb. MEM bb (assemble_blocks st') /\ bb.bb_label = lbl` by (
    simp[assemble_blocks_def] >>
    Cases_on `lbl = st'.cs_current_bb` >-
    (qexists `<|bb_label := st'.cs_current_bb; bb_instructions := st'.cs_current_insts|>` >>
     simp[listTheory.MEM_APPEND]) >>
    fs[bound_labels_def, pred_setTheory.IN_INSERT] >>
    fs[IN_set_MEM, listTheory.MEM_MAP, PULL_EXISTS] >>
    qexists `bb` >> simp[listTheory.MEM_APPEND]) >>
  metis_tac[lookup_block_MEM]
QED


Theorem fresh_vars_wrt_mono_next_var[local]:
  !st1 st2 ss.
    fresh_vars_wrt st1 ss /\ st1.cs_next_var <= st2.cs_next_var
    ==> fresh_vars_wrt st2 ss
Proof
  simp[fresh_vars_wrt_def] >> decide_tac
QED


Theorem rfb_jmp_external_assembled[local]:
  ∀fuel ctx st st' ss target_lbl jmp_id lbl bb.
    lookup_block lbl (assemble_blocks st') = SOME bb ∧
    bb.bb_instructions = [mk_inst jmp_id JMP [Label target_lbl] []] ∧
    ss.vs_current_bb = lbl ∧ ss.vs_inst_idx = 0 ∧
    ¬ss.vs_halted ∧
    lookup_block target_lbl (assemble_blocks st') = NONE
    ⇒
    run_fragment_blocks (SUC (SUC fuel)) ctx
      (assemble_function st st') ss = OK (jump_to target_lbl ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`fuel`,`ctx`,`assemble_function st st'`,`ss`,
                     `target_lbl`,`jmp_id`,`bb`]
           run_fragment_blocks_jmp_external) >>
  simp[assemble_function_def]
QED


(* Bridge lemma: chains rcf + observable_equiv + memory + call_ctx through
   ss → ss0 (normalized entry) → ss1 (after instrs) → jump_to next_lbl → ss' (IH result).
   Proved in a CLEAN context to avoid simp[] timeouts in the 30+ assumption
   context of selector_checks_cons_correct. *)
Theorem fragment_state_chain[local]:
  ∀ss ss0 ss1 next_lbl st st' cs7 fuel ss' ctx.
    ss0 = ss with <|vs_current_bb := st.cs_current_bb;
                    vs_inst_idx := LENGTH st.cs_current_insts|> ∧
    observable_equiv ss0 ss1 ∧
    ss1.vs_memory = ss0.vs_memory ∧
    ss1.vs_call_ctx = ss0.vs_call_ctx ∧
    (∀fuel. run_compiled_fragment ctx st st' ss0 fuel =
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to next_lbl ss1)) ∧
    run_compiled_fragment ctx cs7 st' (jump_to next_lbl ss1) fuel = OK ss' ∧
    observable_equiv (jump_to next_lbl ss1) ss' ∧
    ss'.vs_memory = (jump_to next_lbl ss1).vs_memory ∧
    ss'.vs_call_ctx = (jump_to next_lbl ss1).vs_call_ctx ∧
    (assemble_function st st').fn_blocks = (assemble_function cs7 st').fn_blocks ∧
    (* Preconditions for eq_run_fragment_blocks on the IH side *)
    next_lbl = cs7.cs_current_bb ∧
    cs7.cs_current_insts = [] ∧
    lookup_block cs7.cs_current_bb (assemble_blocks st') ≠ NONE ∧
    ¬ss1.vs_halted
    ⇒
    run_compiled_fragment ctx st st' ss (SUC fuel) = OK ss' ∧
    observable_equiv ss ss' ∧
    ss'.vs_memory = ss.vs_memory ∧
    ss'.vs_call_ctx = ss.vs_call_ctx
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive the rcf chain: rcf(ctx,st,st',ss,(SUC fuel)) = OK ss'
     Chain: ss → ss0 (by rcf_state_normalize: ss with <|...|>)
            ss0 → rfb (by ∀fuel bridge)
            rfb(st,_) → rfb(cs7,_) (by fn_blocks_cong)
            rfb(cs7,_) ← rcf(ctx,cs7,...,fuel) (by eq_run_fragment_blocks) = OK ss' *)
  `run_compiled_fragment ctx cs7 st' (jump_to next_lbl ss1) fuel =
    run_fragment_blocks (SUC fuel) ctx (assemble_function cs7 st')
      (jump_to next_lbl ss1)`
    by (match_mp_tac (GEN_ALL run_compiled_fragment_eq_run_fragment_blocks) >>
        simp[jump_to_vs_current_bb, jump_to_vs_inst_idx, jump_to_vs_halted]) >>
  `run_fragment_blocks (SUC fuel) ctx (assemble_function cs7 st')
      (jump_to next_lbl ss1) = OK ss'`
    by metis_tac[] >>
  `run_fragment_blocks (SUC fuel) ctx (assemble_function st st')
      (jump_to next_lbl ss1) = OK ss'`
    by metis_tac[run_fragment_blocks_fn_blocks_cong] >>
  `run_compiled_fragment ctx st st' ss0 (SUC fuel) = OK ss'` by simp[] >>
  `run_compiled_fragment ctx st st' ss (SUC fuel) =
    run_compiled_fragment ctx st st' ss0 (SUC fuel)`
    by (pure_once_rewrite_tac[rcf_state_normalize] >> simp[]) >>
  simp[] >>
  (* observable_equiv chain *)
  conj_tac >- (
    `observable_equiv ss ss0`
      by simp[observable_equiv_def, venom_state_with_bb_idx] >>
    `observable_equiv ss1 (jump_to next_lbl ss1)`
      by simp[observable_equiv_jump_to] >>
    metis_tac[observable_equiv_trans]) >>
  (* memory preservation *)
  conj_tac >- (
    `ss0.vs_memory = ss.vs_memory` by simp[venom_state_with_bb_idx] >>
    `(jump_to next_lbl ss1).vs_memory = ss1.vs_memory` by simp[jump_to_vs_memory] >>
    metis_tac[]) >>
  (* call_ctx preservation *)
  `ss0.vs_call_ctx = ss.vs_call_ctx` by simp[venom_state_with_bb_idx] >>
  `(jump_to next_lbl ss1).vs_call_ctx = ss1.vs_call_ctx` by simp[jump_to_vs_call_ctx] >>
  metis_tac[]
QED

(* Match-branch helper: when the selector matches (val = n2w sel),
   execution goes: entry block → JNZ → match_lbl block → JMP fn_label (external exit).
   Uses concrete fuel (SUC(SUC 0)) — no universally-quantified fuel' that blocks irule.
   Requires the ∀fuel equation to have already been specialized and simplified. *)
Theorem selector_checks_match_branch[local]:
  ∀ctx st st' ss ss0 ss1 match_lbl fn_label rest fallback_lbl jmp_id.
    ss0 = ss with <|vs_current_bb := st.cs_current_bb;
                    vs_inst_idx := LENGTH st.cs_current_insts|> ∧
    observable_equiv ss0 ss1 ∧
    ss1.vs_memory = ss0.vs_memory ∧
    ss1.vs_call_ctx = ss0.vs_call_ctx ∧
    ¬ss1.vs_halted ∧
    run_compiled_fragment ctx st st' ss0 (SUC (SUC 0)) =
      run_fragment_blocks (SUC (SUC 0)) ctx (assemble_function st st')
        (jump_to match_lbl ss1) ∧
    lookup_block match_lbl (assemble_blocks st') =
      SOME <|bb_label := match_lbl;
              bb_instructions := [mk_inst jmp_id JMP [Label fn_label] []]|> ∧
    lookup_block fn_label (assemble_blocks st') = NONE ∧
    compile_state_ok st' ∧
    fresh_vars_wrt st ss0 ∧ fresh_vars_wrt st' ss1
    ⇒
    ∃ss'.
      run_compiled_fragment ctx st st' ss (SUC (SUC 0)) = OK ss' ∧
      ss'.vs_current_bb = fn_label ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧ compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  (* JMP external exit at fn_label — USE WRAPPER NOT BASE *)
  `run_fragment_blocks (SUC (SUC 0)) ctx (assemble_function st st')
      (jump_to match_lbl ss1) =
    OK (jump_to fn_label (jump_to match_lbl ss1))`
    by (ho_match_mp_tac rfb_jmp_external_assembled >>
        qexistsl [`jmp_id`,`match_lbl`,
          `<|bb_label := match_lbl;
             bb_instructions := [mk_inst jmp_id JMP [Label fn_label] []]|>`] >>
        simp[jump_to_vs_current_bb, jump_to_vs_inst_idx, jump_to_vs_halted]) >>
  (* Normalize rcf from ss to rcf from ss0 *)
  `run_compiled_fragment ctx st st' ss (SUC (SUC 0)) =
    run_compiled_fragment ctx st st' ss0 (SUC (SUC 0))`
    by (pure_once_rewrite_tac[rcf_state_normalize] >> simp[]) >>
  (* Chain: rcf(ss) = rcf(ss0) = rfb = OK(jump_to fn_label ...) *)
  `run_compiled_fragment ctx st st' ss (SUC (SUC 0)) =
    OK (jump_to fn_label (jump_to match_lbl ss1))`
    by simp[] >>
  (* Provide witnesses *)
  qexists `jump_to fn_label (jump_to match_lbl ss1)` >>
  simp[jump_to_vs_current_bb, jump_to_vs_halted, jump_to_vs_memory,
       jump_to_vs_call_ctx] >>
  (* observable_equiv chain: ss ~ ss0 ~ ss1 ~ jump_to match_lbl ~ jump_to fn_label *)
  `observable_equiv ss ss0`
    by simp[observable_equiv_def, venom_state_with_bb_idx] >>
  `observable_equiv ss0 ss1` by simp[] >>
  `observable_equiv ss1 (jump_to match_lbl ss1)`
    by simp[observable_equiv_jump_to] >>
  `observable_equiv (jump_to match_lbl ss1) (jump_to fn_label (jump_to match_lbl ss1))`
    by simp[observable_equiv_jump_to] >>
  metis_tac[observable_equiv_trans, fresh_vars_wrt_jump_to_eq]
QED

(* Factored from selector_checks_cons_correct: fresh_vars_wrt cs7 (jump_to next_lbl ss1)
   cs7.cs_next_var = cs1.cs_next_var so fresh_vars_wrt cs1 implies fresh_vars_wrt cs7 *)
Theorem fresh_vars_wrt_cs7_jump_to[local]:
  !cs1 cs7 next_lbl ss1.
    fresh_vars_wrt cs1 (jump_to next_lbl ss1) /\
    cs7.cs_next_var = cs1.cs_next_var
    ==> fresh_vars_wrt cs7 (jump_to next_lbl ss1)
Proof
  simp[fresh_vars_wrt_def] >> decide_tac
QED

(* Factored from selector_checks_cons_correct: lookup_block for the match block
   Requires the FIND hypothesis + st'.cs_blocks = st_mid.cs_blocks + instruction shape *)
Theorem lookup_block_match_lbl[local]:
  !st' st_mid match_lbl jmp_id fn_label bb_insts.
    FIND (\b. b.bb_label = match_lbl) st_mid.cs_blocks =
      SOME <|bb_label := match_lbl; bb_instructions := bb_insts|> /\
    st'.cs_blocks = st_mid.cs_blocks /\
    bb_insts = [mk_inst jmp_id JMP [Label fn_label] []]
    ==> lookup_block match_lbl (assemble_blocks st') =
        SOME <|bb_label := match_lbl;
                bb_instructions := [mk_inst jmp_id JMP [Label fn_label] []]|>
Proof
  rpt strip_tac >>
  `FIND (\b. b.bb_label = match_lbl) st'.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := [mk_inst jmp_id JMP [Label fn_label] []]|>`
    by simp[] >>
  drule lookup_block_assemble_in_blocks >>
  simp[]
QED

(* No-match branch helper: when val ≠ n2w sel, execution goes to next_lbl
   where the remaining selector checks run. The IH gives us the result
   for the inner fragment; fragment_state_chain bridges back to the
   outer st context. *)
Theorem selector_checks_no_match_branch[local]:
  ∀ctx st st' ss ss0 ss1 next_lbl cs7 fn_label fallback_lbl
    fuel_ih ss_ih rest st_mid method_id.
    ss0 = ss with <|vs_current_bb := st.cs_current_bb;
                    vs_inst_idx := LENGTH st.cs_current_insts|> ∧
    observable_equiv ss0 ss1 ∧ ss1.vs_memory = ss0.vs_memory ∧
    ss1.vs_call_ctx = ss0.vs_call_ctx ∧ ¬ss1.vs_halted ∧
    fresh_vars_wrt st ss0 ∧ fresh_vars_wrt st' ss1 ∧
    (∀fuel. run_compiled_fragment ctx st st' ss0 fuel =
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to next_lbl ss1)) ∧
    run_compiled_fragment ctx cs7 st' (jump_to next_lbl ss1) fuel_ih = OK ss_ih ∧
    (MEM ss_ih.vs_current_bb (MAP SND rest) ∨ ss_ih.vs_current_bb = fallback_lbl) ∧
    observable_equiv (jump_to next_lbl ss1) ss_ih ∧
    ss_ih.vs_memory = (jump_to next_lbl ss1).vs_memory ∧
    ss_ih.vs_call_ctx = (jump_to next_lbl ss1).vs_call_ctx ∧
    ¬ss_ih.vs_halted ∧ fresh_vars_wrt st' ss_ih ∧
    compile_state_ok st' ∧ compile_state_ok cs7 ∧
    cs7.cs_current_bb = next_lbl ∧ cs7.cs_current_insts = [] ∧
    bound_labels st' = bound_labels st_mid ∧
    compile_selector_checks method_id rest cs7 = ((),st_mid) ∧
    EVERY (label_external cs7) (MAP SND rest) ∧
    label_external cs7 fallback_lbl ∧
    ¬MEM fallback_lbl (MAP SND rest) ∧
    ALL_DISTINCT (MAP SND rest)
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (MEM ss'.vs_current_bb (fn_label :: MAP SND rest) ∨
       ss'.vs_current_bb = fallback_lbl) ∧
      observable_equiv ss ss' ∧ ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧ compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >-
  ((* MEM case *)
   `(assemble_function st st').fn_blocks = (assemble_function cs7 st').fn_blocks`
     by EVAL_TAC >>
   `next_lbl IN bound_labels cs7`
     by simp[bound_labels_def, pred_setTheory.IN_INSERT] >>
   `bound_labels cs7 SUBSET bound_labels st_mid`
     by metis_tac[compile_selector_checks_bound_labels_mono] >>
   `lookup_block cs7.cs_current_bb (assemble_blocks st') ≠ NONE`
     by (match_mp_tac bound_labels_imp_lookup >>
         metis_tac[pred_setTheory.SUBSET_DEF]) >>
   mp_tac (Q.SPECL
     [`ss`,`ss0`,`ss1`,`next_lbl`,`st`,`st'`,`cs7`,`fuel_ih`,`ss_ih`,`ctx`]
     fragment_state_chain) >>
   impl_tac >- simp[] >>
   disch_tac >>
   qexistsl [`SUC fuel_ih`, `ss_ih`] >>
   simp[]) >>
  (* fallback_lbl case *)
  `(assemble_function st st').fn_blocks = (assemble_function cs7 st').fn_blocks`
    by EVAL_TAC >>
  `next_lbl IN bound_labels cs7`
    by simp[bound_labels_def, pred_setTheory.IN_INSERT] >>
  `bound_labels cs7 SUBSET bound_labels st_mid`
    by metis_tac[compile_selector_checks_bound_labels_mono] >>
  `lookup_block cs7.cs_current_bb (assemble_blocks st') ≠ NONE`
    by (match_mp_tac bound_labels_imp_lookup >>
        metis_tac[pred_setTheory.SUBSET_DEF]) >>
  mp_tac (Q.SPECL
    [`ss`,`ss0`,`ss1`,`next_lbl`,`st`,`st'`,`cs7`,`fuel_ih`,`ss_ih`,`ctx`]
    fragment_state_chain) >>
  impl_tac >- simp[] >>
  disch_tac >>
  qexistsl [`SUC fuel_ih`, `ss_ih`] >>
  simp[]
QED

Theorem selector_checks_cons_correct[local]:
  ∀method_id sel fn_label rest st st_mid st' fallback_lbl ss ctx.
    (∀st st_mid st' fallback_lbl ss ctx.
       compile_selector_checks method_id rest st = ((),st_mid) ∧
       emit_inst JMP [Label fallback_lbl] [] st_mid = ((),st') ∧
       compile_state_ok st ∧ EVERY (label_external st) (MAP SND rest) ∧
       label_external st fallback_lbl ∧ ¬MEM fallback_lbl (MAP SND rest) ∧
       ALL_DISTINCT (MAP SND rest) ∧ fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
       (∃v. eval_operand method_id ss = SOME v) ⇒
       ∃fuel ss'.
         run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
         (MEM ss'.vs_current_bb (MAP SND rest) ∨ ss'.vs_current_bb = fallback_lbl) ∧
         observable_equiv ss ss' ∧ ss'.vs_memory = ss.vs_memory ∧
         ss'.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss'.vs_halted ∧
         fresh_vars_wrt st' ss' ∧ compile_state_ok st') ⇒
    compile_selector_checks method_id ((sel,fn_label)::rest) st = ((),st_mid) ∧
    emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') ∧
    compile_state_ok st ∧
    EVERY (label_external st) (MAP SND ((sel,fn_label)::rest)) ∧
    label_external st fallback_lbl ∧
    ¬MEM fallback_lbl (MAP SND ((sel,fn_label)::rest)) ∧
    ALL_DISTINCT (MAP SND ((sel,fn_label)::rest)) ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    (∃v. eval_operand method_id ss = SOME v)
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (MEM ss'.vs_current_bb (fn_label :: MAP SND rest) ∨
       ss'.vs_current_bb = fallback_lbl) ∧
      observable_equiv ss ss' ∧ ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧ compile_state_ok st'
Proof
  rpt gen_tac >>
  (* Discharge the IH, label it to avoid drule_all confusion *)
  disch_tac >>
  qpat_x_assum `∀st st_mid st' fallback_lbl ss ctx. _` (mk_asm "IH") >>
  strip_tac >>
  (* Unfold the cons compilation monad chain *)
  qpat_x_assum `compile_selector_checks _ ((_,_)::_) _ = _` mp_tac >>
  simp[compile_selector_checks_cons_eqn] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >>
  `∃val. eval_operand method_id ss = SOME val` by simp[] >>
  `label_external st fn_label ∧ EVERY (label_external st) (MAP SND rest)`
    by metis_tac[EVERY_label_external_MAP_SND_cons] >>
  `fallback_lbl ≠ fn_label ∧ ¬MEM fallback_lbl (MAP SND rest)`
    by (Cases_on `fallback_lbl = fn_label` >> fs[] >> metis_tac[]) >>
  fs[listTheory.ALL_DISTINCT] >>
  qpat_x_assum `T` kall_tac >> qpat_x_assum `T` kall_tac >>
  (* All state/label facts from the 8 monadic steps *)
  drule_all selector_step_facts >> strip_tac >>
  (* Normalize entry state for selector_step_jnz_split *)
  qabbrev_tac `ss0 = ss with <|vs_current_bb := st.cs_current_bb;
                                vs_inst_idx := LENGTH st.cs_current_insts|>` >>
  `ss0.vs_current_bb = st.cs_current_bb` by simp[Abbr `ss0`] >>
  `ss0.vs_inst_idx = LENGTH st.cs_current_insts` by simp[Abbr `ss0`] >>
  `fresh_vars_wrt st ss0`
    by (simp[Abbr `ss0`, fresh_vars_wrt_def, venom_state_with_bb_idx]
        >> fs[fresh_vars_wrt_def]) >>
  `¬ss0.vs_halted` by simp[Abbr `ss0`] >>
  `eval_operand method_id ss0 = SOME val` by simp[Abbr `ss0`, eval_op_double_update] >>
  (* Apply JNZ split — needs monadic assumptions, do BEFORE killing them *)
  drule_all selector_step_jnz_split >> strip_tac >>
  (* Pre-derive facts needing monadic assumptions *)
  `FIND (\b. b.bb_label = match_lbl) st_mid.cs_blocks =
    SOME <|bb_label := match_lbl; bb_instructions := cs6.cs_current_insts|>`
    by (mp_tac (Q.SPECL
        [`method_id`,`sel`,`fn_label`,`rest`,`st`,`st_mid`,
         `match_op`,`cs1`,`match_lbl`,`cs2`,`next_lbl`,`cs3`,`cs4`,
         `old1`,`cs5`,`cs6`,`old2`,`cs7`]
        selector_checks_match_find) >> simp[]) >>
  `cs7.cs_next_var = cs1.cs_next_var`
    by (drule_all selector_step_preserves_next_var >> simp[]) >>
  `st_mid.cs_next_var ≥ cs7.cs_next_var`
    by (drule compile_selector_checks_next_var_mono >> simp[]) >>
  `st'.cs_next_var ≥ st_mid.cs_next_var` by
    (imp_res_tac emit_inst_extends >> fs[]) >>
  `st'.cs_next_var ≥ cs7.cs_next_var` by decide_tac >>
  (* NOW kill the 9 monadic-bind assumptions that bloat the context *)
  qpat_x_assum `emit_op EQ _ _ = _` kall_tac >>
  qpat_x_assum `fresh_label "match" _ = _` kall_tac >>
  qpat_x_assum `fresh_label "next" _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `new_block match_lbl _ = _` kall_tac >>
  qpat_x_assum `emit_inst JMP [Label fn_label] _ _ = _` kall_tac >>
  qpat_x_assum `new_block next_lbl _ = _` kall_tac >>
  (* DON'T kill compile_selector_checks — no-match branch needs it for IH *)
  qpat_x_assum `val = v` kall_tac >>
  (* Break down the ∀ctx. ∃ss1. ... from JNZ split to get ss1 + its properties *)
  qpat_x_assum `!ctx. ?ss1. _` (qspec_then `ctx` strip_assume_tac) >>
  (* Pre-derive branch-independent facts BEFORE Cases_on — avoids by-block timeout *)
  `cs1.cs_next_var <= st'.cs_next_var` by decide_tac >>
  `fresh_vars_wrt st' ss1`
    by metis_tac[fresh_vars_wrt_mono_next_var] >>
  `lookup_block match_lbl (assemble_blocks st') =
    SOME <|bb_label := match_lbl;
            bb_instructions := [mk_inst cs5.cs_next_id JMP [Label fn_label] []]|>`
    by metis_tac[lookup_block_match_lbl] >>
Cases_on `val = n2w sel`
>- (
  (* ===== Match branch: val = n2w sel ===== *)
  (* Apply the proved helper — all heavy lifting happens inside it
     with clean context, avoiding the 25+ assumption metis timeout *)
  mp_tac (Q.SPECL [`ctx`,`st`,`st'`,`ss`,`ss0`,`ss1`,`match_lbl`,`fn_label`,
                     `rest`,`fallback_lbl`,`cs5.cs_next_id`]
            selector_checks_match_branch) >>
  impl_tac >- (
    (* Specialize ∀fuel for match path, then all antecedents follow *)
    first_x_assum (Q.SPEC_THEN `SUC (SUC 0)` assume_tac) >>
    simp[Abbr `ss0`]) >>
  disch_then (qx_choose_then `ss'` STRIP_ASSUME_TAC) >>
  qexistsl [`SUC (SUC 0)`, `ss'`] >> simp[] >>
  DISJ1_TAC >> simp[])
>> (
    `fresh_vars_wrt cs7 (jump_to next_lbl ss1)`
      by (mp_tac (Q.SPECL [`cs1`,`cs7`,`next_lbl`,`ss1`] fresh_vars_wrt_cs7_jump_to) >>
          simp[fresh_vars_wrt_jump_to_eq]) >>
    `¬(jump_to next_lbl ss1).vs_halted` by simp[jump_to_vs_halted] >>
    `eval_operand method_id ss1 = SOME val`
      by (qpat_x_assum `!op w. eval_operand op ss0 = SOME w ==> eval_operand op ss1 = SOME w`
            (qspecl_then [`method_id`,`val`] mp_tac) >> simp[]) >>
    (* Kill dead assumptions before applying IH *)
    qpat_x_assum `compile_state_ok cs5` kall_tac >>
    qpat_x_assum `cs5.cs_current_insts = _` kall_tac >>
    qpat_x_assum `cs5.cs_current_bb = _` kall_tac >>
    qpat_x_assum `compile_state_ok cs6` kall_tac >>
    qpat_x_assum `cs6.cs_blocks = _` kall_tac >>
    qpat_x_assum `cs6.cs_current_bb = _` kall_tac >>
    qpat_x_assum `cs6.cs_current_insts = _` kall_tac >>
    qpat_x_assum `lookup_block fn_label (assemble_blocks st') = NONE` kall_tac >>
    qpat_x_assum `lookup_block match_lbl (assemble_blocks st') = _` kall_tac >>
    qpat_x_assum `eval_operand match_op ss1 = _` kall_tac >>
    qpat_x_assum `FIND _ st_mid.cs_blocks = _` kall_tac >>
    qpat_x_assum `!op w. eval_operand op ss0 = SOME w ==> eval_operand op ss1 = SOME w` kall_tac >>
    qpat_x_assum `eval_operand method_id ss0 = SOME val` kall_tac >>
    qpat_x_assum `bound_labels st' SUBSET _` kall_tac >>
    qpat_x_assum `bound_labels cs7 = _` kall_tac >>
    qpat_x_assum `cs7.cs_next_label = _` kall_tac >>
    qpat_x_assum `compile_state_ok st_mid` kall_tac >>
    qpat_x_assum `st'.cs_blocks = st_mid.cs_blocks` kall_tac >>
    qpat_x_assum `eval_operand method_id ss = SOME val` kall_tac >>
    qpat_x_assum `¬MEM fn_label (MAP SND rest)` kall_tac >>
    (* Apply IH *)
    asm "IH" (fn th =>
      mp_tac (Q.SPECL [`cs7`,`st_mid`,`st'`,`fallback_lbl`,
                        `jump_to next_lbl ss1`,`ctx`] th)) >>
    impl_tac >- (simp[] >> qexists `val` >> simp[eval_operand_jump_to]) >>
    disch_then (qx_choose_then `fuel_ih` (qx_choose_then `ss_ih` STRIP_ASSUME_TAC)) >>
    (* Apply the no-match branch helper — encapsulates fragment_state_chain *)
    mp_tac (Q.SPECL [`ctx`,`st`,`st'`,`ss`,`ss0`,`ss1`,`next_lbl`,`cs7`,
                      `fn_label`,`fallback_lbl`,`fuel_ih`,`ss_ih`,`rest`,
                      `st_mid`,`method_id`]
             selector_checks_no_match_branch) >>
    impl_tac >- (simp[Abbr `ss0`]) >> simp[])
QED


Theorem MAP_SND_cons[local]:
  ∀sel (fn_label:string) rest.
    MAP SND ((sel,fn_label)::rest) = fn_label :: MAP SND rest
Proof
  simp[listTheory.MAP]
QED

(* Same as selector_checks_cons_correct but with MAP SND ((sel,fn_label)::rest)
   in the conclusion instead of fn_label :: MAP SND rest.
   Using REWRITE_RULE[GSYM MAP_SND_cons] avoids the variable-shadowing issues
   that arise when trying to prove this via MATCH_MP + gen_tac + strip_tac. *)
val selector_checks_cons_correct_alt = save_thm(
  "selector_checks_cons_correct_alt",
  REWRITE_RULE [GSYM MAP_SND_cons] selector_checks_cons_correct);


Theorem compile_selector_checks_with_fallback_correct:
  ∀ method_id selectors st st_mid st' fallback_lbl ss ctx.
    compile_selector_checks method_id selectors st = ((), st_mid) ∧
    emit_inst JMP [Label fallback_lbl] [] st_mid = ((), st') ∧
    compile_state_ok st ∧
    EVERY (label_external st) (MAP SND selectors) ∧
    label_external st fallback_lbl ∧
    ¬MEM fallback_lbl (MAP SND selectors) ∧
    ALL_DISTINCT (MAP SND selectors) ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted ∧
    (∃v. eval_operand method_id ss = SOME v)
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (MEM ss'.vs_current_bb (MAP SND selectors) ∨
       ss'.vs_current_bb = fallback_lbl) ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  recInduct compile_selector_checks_ind >> conj_tac
  (* Base case: selectors = [] *)
  >- (
    rpt gen_tac >> strip_tac >>
    `st_mid = st` by (
      qpat_x_assum `compile_selector_checks _ [] _ = _` mp_tac >>
      simp[compile_selector_checks_nil]) >>
    rw[] >>
    drule jmp_external_exits_fragment >>
    simp[] >> strip_tac >>
    qexistsl [`fuel'`, `ss'`] >> simp[])
  (* Step case: MATCH_MP the IH into selector_checks_cons_correct_alt,
     then irule to discharge the remaining conjunction *)
  >- (
    rpt gen_tac >> rpt strip_tac >>
    first_x_assum (fn ih =>
      irule (MATCH_MP selector_checks_cons_correct_alt ih)) >>
    simp[])
QED

(* ===== Linear dispatch correct proof ===== *)
(* Decomposed into standalone [local] boundary lemmas to avoid context bloat.
   Each lemma has ≤15 assumptions. Main proof is a 30-line stitcher.
   Uses: fragment_entry_jnz_branch_correct (entry+JNZ),
         fragment_prefix_chain (CALLDATALOAD+SHR prefix),
         compile_selector_checks_with_fallback_correct (selector body),
         linear_dispatch_fallback_branch (external exit). *)

Theorem linear_dispatch_fallback_branch[local]:
  ∀ctx st st' ss_prefix fallback_lbl.
    lookup_block fallback_lbl (assemble_blocks st') = NONE ∧
    compile_state_ok st' ∧
    fresh_vars_wrt st' ss_prefix ∧
    observable_equiv ss_prefix (jump_to fallback_lbl ss_prefix) ∧
    (jump_to fallback_lbl ss_prefix).vs_memory = ss_prefix.vs_memory ∧
    (jump_to fallback_lbl ss_prefix).vs_call_ctx = ss_prefix.vs_call_ctx ∧
    ¬ss_prefix.vs_halted
    ⇒
    ∃fuel ss'.
      run_fragment_blocks fuel ctx (assemble_function st st')
        (jump_to fallback_lbl ss_prefix) = OK ss' ∧
      ss'.vs_current_bb = fallback_lbl ∧
      observable_equiv ss_prefix ss' ∧
      ss'.vs_memory = ss_prefix.vs_memory ∧
      ss'.vs_call_ctx = ss_prefix.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧ compile_state_ok st'
Proof
  rpt strip_tac >>
  qexistsl [`SUC 0`,`jump_to fallback_lbl ss_prefix`] >>
  simp[run_fragment_blocks_def, assemble_function_def,
       jump_to_vs_current_bb, jump_to_vs_inst_idx,
       jump_to_vs_memory, jump_to_vs_call_ctx, jump_to_vs_halted,
       observable_equiv_jump_to, fresh_vars_wrt_jump_to]
QED

(* Combined fallback branch: from entry_prefix result + structural facts
   to the full run_compiled_fragment fallback exit.
   Proved in a small context where metis_tac/irule work reliably. *)
Theorem linear_dispatch_fallback_exit[local]:
  ∀ctx st st' ss ss_prefix fallback_lbl rfb_eqn.
    (* entry_prefix gives this equation when cond_v = 0w *)
    rfb_eqn = (λfuel. run_fragment_blocks fuel ctx (assemble_function st st')
                         (jump_to fallback_lbl ss_prefix)) ∧
    (* structural facts *)
    lookup_block fallback_lbl (assemble_blocks st') = NONE ∧
    compile_state_ok st' ∧
    fresh_vars_wrt st' ss_prefix ∧
    observable_equiv ss ss_prefix ∧
    ss_prefix.vs_memory = ss.vs_memory ∧
    ss_prefix.vs_call_ctx = ss.vs_call_ctx ∧
    ¬ss_prefix.vs_halted ∧
    (∀fuel. run_compiled_fragment ctx st st' ss fuel = rfb_eqn fuel)
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      ss'.vs_current_bb = fallback_lbl ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt strip_tac >>
  `∃fuel0 ss0.
    run_fragment_blocks fuel0 ctx (assemble_function st st')
      (jump_to fallback_lbl ss_prefix) = OK ss0 ∧
    ss0.vs_current_bb = fallback_lbl ∧
    observable_equiv ss_prefix ss0 ∧ ss0.vs_memory = ss_prefix.vs_memory ∧
    ss0.vs_call_ctx = ss_prefix.vs_call_ctx ∧
    ¬ss0.vs_halted ∧ fresh_vars_wrt st' ss0 ∧ compile_state_ok st'`
    by (irule linear_dispatch_fallback_branch >>
        simp[observable_equiv_jump_to, fresh_vars_wrt_jump_to,
             jump_to_vs_memory, jump_to_vs_call_ctx, jump_to_vs_halted]) >>
  qexistsl [`fuel0`, `ss0`] >> simp[] >>
  metis_tac[observable_equiv_trans]
QED

(* Boundary lemma 1: lookup_block facts from bound_labels subset chain *)
Theorem linear_dispatch_lookup_facts[local]:
  ∀st cs6 cs8 st' dispatch_lbl.
    compile_state_ok st ∧ compile_state_ok cs6 ∧
    cs6.cs_current_bb = dispatch_lbl ∧ cs8.cs_current_bb = dispatch_lbl ∧
    bound_labels st ⊆ bound_labels st' ∧
    bound_labels cs8 ⊆ bound_labels st'
    ⇒
    lookup_block st.cs_current_bb (assemble_blocks st') ≠ NONE ∧
    lookup_block dispatch_lbl (assemble_blocks st') ≠ NONE
Proof
  rpt strip_tac >>
  `st.cs_current_bb ∈ bound_labels st` by
    simp[bound_labels_def, pred_setTheory.IN_INSERT] >>
  `dispatch_lbl ∈ bound_labels cs8` by
    simp[bound_labels_def, pred_setTheory.IN_INSERT] >>
  `st.cs_current_bb ∈ bound_labels st'` by
    metis_tac[pred_setTheory.SUBSET_DEF] >>
  `dispatch_lbl ∈ bound_labels st'` by
    metis_tac[pred_setTheory.SUBSET_DEF] >>
  metis_tac[bound_labels_imp_lookup]
QED

(* Standalone helper: CALLDATASIZE+LT+ISZERO chain correctness.
   Clean context (6 antecedents) avoids drule_all matching issues.
   Does NOT compute the exact value of has_sel2 — just provides cond_v
   existentially, since consumers use ∃-quantified JNZ branching. *)
Theorem calldatasize_lt_iszero_correct[local]:
  ∀st cds cs1 has_sel cs2 has_sel2 cs3 ss.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    compile_state_ok st ∧ fresh_vars_wrt st ss ∧ ¬ss.vs_halted
    ⇒
    ∃ss3 cond_v. run_inst_seq (emitted_insts st cs3) ss = OK ss3 ∧
          eval_operand has_sel2 ss3 = SOME cond_v ∧
          same_blocks st cs3 ∧ inst_extends st cs3 ∧
          fresh_vars_wrt cs3 ss3 ∧
          observable_equiv ss ss3 ∧ ss3.vs_memory = ss.vs_memory ∧
          ss3.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss3.vs_halted ∧
          EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs3) ∧
          EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs3) ∧
          (∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss3 = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  (* === PURITY FIRST: derive in tiny context (~5 assumptions) === *)
  `inst_extends st cs1` by metis_tac[inst_extends_emit_op] >>
  `inst_extends cs1 cs2` by metis_tac[inst_extends_emit_op] >>
  `inst_extends cs2 cs3` by metis_tac[inst_extends_emit_op] >>
  `inst_extends st cs2` by metis_tac[inst_extends_trans] >>
  `inst_extends st cs3` by metis_tac[inst_extends_trans] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st cs1)`
    by metis_tac[emit_op_CALLDATASIZE_everything_pure] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts cs1 cs2)`
    by metis_tac[emit_op_LT_everything_pure] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts cs2 cs3)`
    by metis_tac[emit_op_ISZERO_everything_pure] >>
  (* Compose emitted_insts via append equations + EVERY_APPEND *)
  `emitted_insts st cs2 = emitted_insts st cs1 ++ emitted_insts cs1 cs2`
    by metis_tac[emitted_insts_append_from_extends] >>
  `emitted_insts st cs3 = emitted_insts st cs2 ++ emitted_insts cs2 cs3`
    by metis_tac[emitted_insts_append_from_extends] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts st cs3)`
    by metis_tac[listTheory.EVERY_APPEND] >>
  `EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts st cs3)`
    by metis_tac[pure_everyy_imp_not_terminator] >>
  `EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts st cs3)`
    by metis_tac[pure_everyy_imp_not_invoke] >>
  (* === SEMANTIC CHAIN (context bloats here, but we already have purity) === *)
  drule_all emit_op_CALLDATASIZE_correct >> strip_tac >>
  `eval_operand (Lit 4w) ss' = SOME (4w:bytes32)` by simp[eval_operand_lit] >>
  drule_all emit_op_LT_correct >> strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `eval_operand has_sel2 s3 = SOME v3` >>
  rename1 `run_inst_seq (emitted_insts cs2 cs3) s2 = OK s3` >>
  rename1 `run_inst_seq (emitted_insts cs1 cs2) s1 = OK s2` >>
  rename1 `run_inst_seq (emitted_insts st cs1) ss = OK s1` >>
  (* same_blocks chain *)
  `same_blocks st cs3` by metis_tac[same_blocks_trans] >>
  (* Compose run_inst_seq *)
  `run_inst_seq (emitted_insts st cs2) ss = OK s2`
    by metis_tac[run_inst_seq_compose_ok] >>
  `run_inst_seq (emitted_insts st cs3) ss = OK s3`
    by metis_tac[run_inst_seq_compose_ok] >>
  (* Observable/memory/call_ctx/halted for each segment *)
  `observable_equiv ss s1 ∧ s1.vs_memory = ss.vs_memory ∧
   s1.vs_call_ctx = ss.vs_call_ctx ∧ ¬s1.vs_halted`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `observable_equiv s1 s2 ∧ s2.vs_memory = s1.vs_memory ∧
   s2.vs_call_ctx = s1.vs_call_ctx ∧ ¬s2.vs_halted`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `observable_equiv s2 s3 ∧ s3.vs_memory = s2.vs_memory ∧
   s3.vs_call_ctx = s2.vs_call_ctx ∧ ¬s3.vs_halted`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `observable_equiv ss s3` by metis_tac[observable_equiv_trans] >>
  `s3.vs_memory = ss.vs_memory` by simp[] >>
  `s3.vs_call_ctx = ss.vs_call_ctx` by simp[] >>
  (* Build witness *)
  qexistsl [`s3`, `v3`] >> simp[] >>
  (* eval_operand preservation by chaining 3 steps *)
  metis_tac[]
QED
(* Boundary lemma 2: entry prefix execution (CALLDATASIZE+LT+ISZERO then JNZ).
   Takes bb.bb_instructions as an explicit assumption to avoid the same_blocks gap.
   The main proof derives this from new_block + ALL_DISTINCT. *)
(* Boundary lemma: get_instruction into the middle segment of a triple append.
   Avoids EL_APPEND2 chaining in consumer proofs. *)
Theorem get_instruction_triple_append[local]:
  !bb prefix segment suffix k.
    bb.bb_instructions = prefix ++ segment ++ suffix /\
    k < LENGTH segment
    ==>
    get_instruction bb (LENGTH prefix + k) = SOME (EL k segment)
Proof
  rpt strip_tac >>
  simp[get_instruction_def] >>
  `LENGTH prefix + k < LENGTH bb.bb_instructions` by simp[] >>
  `LENGTH prefix + k - LENGTH prefix = k` by decide_tac >>
  rewrite_tac[listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.EL_APPEND] >>
  simp[rich_listTheory.EL_APPEND]
QED

Theorem get_instruction_triple_append_last[local]:
  !bb prefix segment last_inst.
    bb.bb_instructions = prefix ++ segment ++ [last_inst]
    ==>
    get_instruction bb (LENGTH prefix + LENGTH segment) = SOME last_inst
Proof
  rpt strip_tac >>
  simp[get_instruction_def] >>
  `LENGTH prefix + LENGTH segment < LENGTH bb.bb_instructions` by simp[] >>
  `LENGTH prefix + LENGTH segment - LENGTH prefix = LENGTH segment` by decide_tac >>
  rewrite_tac[listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.EL_APPEND] >>
  simp[rich_listTheory.EL_APPEND1]
QED

Theorem linear_dispatch_entry_prefix[local]:
  ∀st fallback_lbl cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5
    st' ss ctx bb insts.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
    emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
    compile_state_ok st ∧ fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    cs3.cs_blocks = st.cs_blocks ∧ cs3.cs_current_bb = st.cs_current_bb ∧
    bb.bb_instructions = cs5.cs_current_insts ∧
    emitted_insts st cs3 = insts
    ⇒
    ∃ss_prefix cond_v.
      run_inst_seq insts
        (ss with <|vs_current_bb := st.cs_current_bb;
                    vs_inst_idx := LENGTH st.cs_current_insts|>) = OK ss_prefix ∧
      eval_operand has_sel2 ss_prefix = SOME cond_v ∧
      observable_equiv ss ss_prefix ∧ ss_prefix.vs_memory = ss.vs_memory ∧
      ss_prefix.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss_prefix.vs_halted ∧
      fresh_vars_wrt cs3 ss_prefix ∧
      (∀fuel.
        run_compiled_fragment ctx st st' ss fuel =
          if cond_v ≠ 0w then
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to dispatch_lbl ss_prefix)
          else
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to fallback_lbl ss_prefix))
Proof
  rpt gen_tac >> strip_tac >>
  (* Derive shifted-state assumptions for calldatasize_lt_iszero_correct *)
  `fresh_vars_wrt st (ss with <|vs_current_bb := st.cs_current_bb;
                                  vs_inst_idx := LENGTH st.cs_current_insts|>)`
    by metis_tac[fresh_vars_wrt_with_bb_idx] >>
  `¬(ss with <|vs_current_bb := st.cs_current_bb;
                vs_inst_idx := LENGTH st.cs_current_insts|>).vs_halted`
    by simp[venom_state_with_bb_idx] >>
  (* Apply CALLDATASIZE+LT+ISZERO chain *)
  drule_all calldatasize_lt_iszero_correct >> strip_tac >>
  rename1 `eval_operand has_sel2 ss3' = SOME cond_v` >>
  (* Derive instruction structure *)
  `compile_state_ok cs3` by metis_tac[compile_state_ok_emit_op] >>
  `inst_extends cs3 cs4` by metis_tac[inst_extends_fresh_label] >>
  `inst_extends cs4 cs5` by metis_tac[inst_extends_emit_inst] >>
  `cs4.cs_current_insts = cs3.cs_current_insts`
    by metis_tac[fresh_label_props] >>
  `cs5.cs_current_insts = cs3.cs_current_insts ++ [mk_inst cs4.cs_next_id JNZ
      [has_sel2; Label dispatch_lbl; Label fallback_lbl] []]`
    by (drule emit_inst_extends >> simp[]) >>
  `cs3.cs_current_insts = st.cs_current_insts ++ insts`
    by (qpat_x_assum `inst_extends st cs3` mp_tac >> simp[inst_extends_def]) >>
  `cs5.cs_current_insts = st.cs_current_insts ++ insts ++
    [mk_inst cs4.cs_next_id JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] []]`
    by simp[] >>
  (* Purity from calldatasize_lt_iszero_correct *)
  `EVERY (λi. ¬is_terminator i.inst_opcode) insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) insts`
    by metis_tac[] >>
  (* get_instruction via boundary lemma *)
  `∀k. k < LENGTH insts ⇒
    get_instruction bb (LENGTH st.cs_current_insts + k) = SOME (EL k insts)`
    by metis_tac[get_instruction_triple_append] >>
  `get_instruction bb (LENGTH st.cs_current_insts + LENGTH insts) =
    SOME (mk_inst cs4.cs_next_id JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [])`
    by metis_tac[get_instruction_triple_append_last] >>
  (* Bridge observable_equiv from shifted state back to original ss *)
  `observable_equiv ss ss3'`
    by (irule observable_equiv_trans >>
        qexists `ss with <|vs_current_bb := st.cs_current_bb;
                            vs_inst_idx := LENGTH st.cs_current_insts|>` >>
        simp[observable_equiv_with_bb_idx]) >>
  `ss3'.vs_memory = ss.vs_memory`
    by (qpat_x_assum `ss3'.vs_memory = _` mp_tac >> simp[venom_state_component_equality]) >>
  `ss3'.vs_call_ctx = ss.vs_call_ctx`
    by (qpat_x_assum `ss3'.vs_call_ctx = _` mp_tac >> simp[venom_state_component_equality]) >>
  (* Build existential witness *)
  qexistsl [`ss3'`, `cond_v`] >> simp[] >>
  (* Remaining: run_inst_seq insts ... = OK ss3' ∧ ∀fuel. rcf = ... *)
  conj_tac >- (
    qpat_x_assum `emitted_insts st cs3 = insts`
      (fn th => once_rewrite_tac[GSYM th]) >> simp[]) >>
  (* ∀fuel part via fragment_entry_jnz_branch_correct *)
  gen_tac >>
  qspecl_then [`ctx`, `st`, `st'`, `ss`, `fuel`, `bb`, `insts`, `ss3'`,
               `has_sel2`, `cond_v`, `dispatch_lbl`, `fallback_lbl`,
               `cs4.cs_next_id`, `LENGTH st.cs_current_insts`]
    mp_tac fragment_entry_jnz_branch_correct >>
  impl_tac >- (
    simp[] >>
    qpat_x_assum `emitted_insts st cs3 = insts`
      (fn th => once_rewrite_tac[GSYM th]) >>
    simp[jump_to_vs_current_bb, jump_to_vs_inst_idx]) >>
  simp[]
QED

(* Simplified version without the insts parameter that caused reflexivity
   antecedent issues in large contexts. *)
Theorem linear_dispatch_entry_prefix_simple[local]:
  ∀st fallback_lbl cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5
    st' ss ctx bb.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
    emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
    compile_state_ok st ∧ fresh_vars_wrt st ss ∧ ¬ss.vs_halted ∧
    lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
    cs3.cs_blocks = st.cs_blocks ∧ cs3.cs_current_bb = st.cs_current_bb ∧
    bb.bb_instructions = cs5.cs_current_insts
    ⇒
    ∃ss_prefix cond_v.
      run_inst_seq (emitted_insts st cs3)
        (ss with <|vs_current_bb := st.cs_current_bb;
                    vs_inst_idx := LENGTH st.cs_current_insts|>) = OK ss_prefix ∧
      eval_operand has_sel2 ss_prefix = SOME cond_v ∧
      observable_equiv ss ss_prefix ∧ ss_prefix.vs_memory = ss.vs_memory ∧
      ss_prefix.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss_prefix.vs_halted ∧
      fresh_vars_wrt cs3 ss_prefix ∧
      (∀fuel.
        run_compiled_fragment ctx st st' ss fuel =
          if cond_v ≠ 0w then
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to dispatch_lbl ss_prefix)
          else
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to fallback_lbl ss_prefix))
Proof
  rpt gen_tac >> strip_tac >>
  Q.SPECL_THEN [`st`,`fallback_lbl`,`cds`,`cs1`,`has_sel`,`cs2`,
    `has_sel2`,`cs3`,`dispatch_lbl`,`cs4`,`cs5`,`st'`,`ss`,`ctx`,
    `bb`,`emitted_insts st cs3`] mp_tac linear_dispatch_entry_prefix >>
  simp[emitted_insts_refl]
QED


(* Boundary lemma 3: rfb(assemble_function st st') = rcf(cs6, st') for
   the dispatch block. Uses fn_blocks_cong + run_compiled_fragment_eq. *)
Theorem linear_dispatch_rfb_to_rcf[local]:
  ∀ctx st cs6 st' ss_prefix dispatch_lbl fuel.
    cs6.cs_current_bb = dispatch_lbl ∧ cs6.cs_current_insts = [] ∧
    lookup_block dispatch_lbl (assemble_blocks st') ≠ NONE ∧
    fresh_vars_wrt cs6 (jump_to dispatch_lbl ss_prefix) ∧
    ¬(jump_to dispatch_lbl ss_prefix).vs_halted
    ⇒
    run_fragment_blocks (SUC fuel) ctx (assemble_function st st')
        (jump_to dispatch_lbl ss_prefix) =
      run_compiled_fragment ctx cs6 st'
        (jump_to dispatch_lbl ss_prefix) fuel
Proof
  rpt strip_tac >>
  `(assemble_function st st').fn_blocks = (assemble_function cs6 st').fn_blocks` by
    simp[assemble_function_fn_blocks_irrel] >>
  `run_compiled_fragment ctx cs6 st' (jump_to dispatch_lbl ss_prefix) fuel =
    run_fragment_blocks (SUC fuel) ctx (assemble_function cs6 st')
      (jump_to dispatch_lbl ss_prefix)`
    by simp[run_compiled_fragment_eq_run_fragment_blocks,
            jump_to_vs_current_bb, jump_to_vs_inst_idx, jump_to_vs_halted] >>
  metis_tac[run_fragment_blocks_fn_blocks_cong]
QED

(* Entry block is in st'.cs_blocks with known instructions.
   After new_block dispatch_lbl cs5, the entry block (st.cs_current_bb) is
   finalized into cs6.cs_blocks. compile_selector_checks preserves it
   (via compile_selector_checks_blocks_preserved, since st.cs_current_bb
   is not cs8.cs_current_bb and is not in compiler_labels_future).
   emit_inst JMP also preserves cs_blocks. *)
Theorem entry_block_findable[local]:
  ∀st cs5 dispatch_lbl cs6 cs8 cs9 st' selectors method_id.
    compile_state_ok st ∧
    cs5.cs_current_bb = st.cs_current_bb ∧
    cs5.cs_blocks = st.cs_blocks ∧
    new_block dispatch_lbl cs5 = (st.cs_current_bb, cs6) ∧
    cs8.cs_current_bb = dispatch_lbl ∧
    same_blocks cs6 cs8 ∧
    compile_state_ok cs8 ∧
    dispatch_lbl ≠ st.cs_current_bb ∧
    compile_selector_checks method_id selectors cs8 = ((), cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((), st')
    ⇒
    FIND (λb. b.bb_label = st.cs_current_bb) st'.cs_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|>
Proof
  rpt gen_tac >> strip_tac >>
  (* new_block finalized the entry block into cs6.cs_blocks *)
  `cs6.cs_blocks = <|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|> :: st.cs_blocks`
    by (drule new_block_props >> simp[]) >>
  (* The entry block is findable in cs8.cs_blocks (same_blocks) *)
  `FIND (λb. b.bb_label = st.cs_current_bb) cs8.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|>`
    by fs[same_blocks_def, listTheory.FIND_thm] >>
  (* st.cs_current_bb is in bound_labels cs8 but not the current_bb *)
  `st.cs_current_bb ∈ bound_labels cs8` by (
    fs[bound_labels_def, same_blocks_def, PULL_EXISTS] >>
    metis_tac[]) >>
  `st.cs_current_bb NOTIN compiler_labels_future cs8.cs_next_label` by (
    fs[compile_state_ok_def] >>
    fs[pred_setTheory.IN_DISJOINT] >>
    metis_tac[]) >>
  (* compile_selector_checks preserves the block in cs9 *)
  drule compile_selector_checks_blocks_preserved >>
  disch_then (qspecl_then [`st.cs_current_bb`,
    `<|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|>`] mp_tac) >>
  simp[] >> strip_tac >>
  (* compile_state_ok cs9 (from compile_selector_checks_bound_labels) *)
  `compile_state_ok cs9` by (
    drule compile_selector_checks_bound_labels >> simp[]) >>
  (* emit_inst JMP preserves cs_blocks *)
  `st'.cs_blocks = cs9.cs_blocks` by (
    drule compile_state_ok_emit_inst >> simp[]) >>
  simp[]
QED

(* Boundary lemma: CALLDATALOAD [0w] then SHR [224w; raw] produces method_id.
   2-segment version of calldatasize_lt_iszero_correct. *)
Theorem calldataload_shr_correct[local]:
  ∀cs6 raw cs7 method_id cs8 ss.
    emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
    emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
    compile_state_ok cs6 ∧ fresh_vars_wrt cs6 ss ∧ ¬ss.vs_halted
    ⇒
    ∃ss2 method_v. run_inst_seq (emitted_insts cs6 cs8) ss = OK ss2 ∧
          eval_operand method_id ss2 = SOME method_v ∧
          same_blocks cs6 cs8 ∧ inst_extends cs6 cs8 ∧
          fresh_vars_wrt cs8 ss2 ∧
          observable_equiv ss ss2 ∧ ss2.vs_memory = ss.vs_memory ∧
          ss2.vs_call_ctx = ss.vs_call_ctx ∧ ¬ss2.vs_halted ∧
          EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts cs6 cs8) ∧
          EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts cs6 cs8) ∧
          (∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss2 = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  (* === PURITY FIRST === *)
  `inst_extends cs6 cs7` by metis_tac[inst_extends_emit_op] >>
  `inst_extends cs7 cs8` by metis_tac[inst_extends_emit_op] >>
  `inst_extends cs6 cs8` by metis_tac[inst_extends_trans] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts cs6 cs7)`
    by metis_tac[emit_op_CALLDATALOAD_everything_pure] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts cs7 cs8)`
    by metis_tac[emit_op_SHR_everything_pure] >>
  `emitted_insts cs6 cs8 = emitted_insts cs6 cs7 ++ emitted_insts cs7 cs8`
    by metis_tac[emitted_insts_append_from_extends] >>
  `EVERY (λi. i.inst_opcode IN {ADD; SUB; MUL; Div; Mod; SDIV; SMOD; SHL; SHR; SAR;
                    SIGNEXTEND; BYTE; ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
                    ISZERO; AND; OR; XOR; NOT;
                    CALLDATASIZE; CALLDATALOAD; CALLVALUE; CALLER; ADDRESS;
                    GAS; ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP;
                    NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
                    MLOAD; SLOAD; TLOAD; OFFSET; PARAM})
           (emitted_insts cs6 cs8)`
    by metis_tac[listTheory.EVERY_APPEND] >>
  `EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts cs6 cs8)`
    by metis_tac[pure_every_imp_not_terminator] >>
  `EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts cs6 cs8)`
    by metis_tac[pure_every_imp_not_invoke] >>
  (* === SEMANTIC CHAIN === *)
  `eval_operand (Lit 0w) ss = SOME (0w:bytes32)` by simp[eval_operand_lit] >>
  drule_all emit_op_CALLDATALOAD_correct >> strip_tac >>
  `eval_operand (Lit 224w) ss' = SOME (224w:bytes32)` by simp[eval_operand_lit] >>
  drule_all emit_op_SHR_correct >> strip_tac >>
  rename1 `eval_operand method_id s2 = SOME v2` >>
  rename1 `run_inst_seq (emitted_insts cs7 cs8) s1 = OK s2` >>
  rename1 `run_inst_seq (emitted_insts cs6 cs7) ss = OK s1` >>
  (* Compose run_inst_seq *)
  `cs7.cs_current_insts = cs6.cs_current_insts ++ emitted_insts cs6 cs7`
    by metis_tac[inst_extends_def] >>
  `cs8.cs_current_insts = cs7.cs_current_insts ++ emitted_insts cs7 cs8`
    by metis_tac[inst_extends_def] >>
  drule_all run_emitted_compose2 >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts cs6 cs8) ss = OK ss2` >>
  (* same_blocks chain *)
  `same_blocks cs6 cs8` by metis_tac[same_blocks_trans] >>
  (* Observable/memory/call_ctx/halted from purity *)
  `observable_equiv ss s1`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `observable_equiv s1 ss2`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `observable_equiv ss ss2`
    by metis_tac[observable_equiv_trans] >>
  `ss2.vs_memory = ss.vs_memory`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `ss2.vs_call_ctx = ss.vs_call_ctx`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  `¬ss2.vs_halted`
    by metis_tac[run_inst_seq_preserves_observable_and_memory] >>
  (* Build witness *)
  qexistsl [`ss2`, `v2`] >> simp[] >>
  metis_tac[]
QED

(* ===== Main theorem: stitcher using boundary lemmas ===== *)
(* New dispatch_block_correct: starts from cs8 (post CALLDATALOAD+SHR prefix),
   where method_id is already a computed variable. This avoids the existential
   bb mismatch that plagued dispatch_block_prefix_get_instruction for 3 sessions.
   The CALLDATALOAD+SHR prefix is the caller's responsibility. *)
Theorem dispatch_block_correct[local]:
  ∀selectors fallback_lbl method_id cs8 cs9 st' ss ctx.
    compile_selector_checks method_id selectors cs8 = ((), cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((), st') ∧
    compile_state_ok cs8 ∧
    EVERY (label_external cs8) (MAP SND selectors) ∧
    label_external cs8 fallback_lbl ∧
    ¬MEM fallback_lbl (MAP SND selectors) ∧
    ALL_DISTINCT (MAP SND selectors) ∧
    fresh_vars_wrt cs8 ss ∧
    ¬ss.vs_halted ∧
    (∃v. eval_operand method_id ss = SOME v)
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx cs8 st' ss fuel = OK ss' ∧
      (MEM ss'.vs_current_bb (MAP SND selectors) ∨
       ss'.vs_current_bb = fallback_lbl) ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt strip_tac >>
  irule compile_selector_checks_with_fallback_correct >>
  simp[] >>
  qexistsl [`method_id`, `cs9`] >>
  simp[]
QED

(* Monad-equation boundary lemma: iff version, following the proven pattern
   from compile_selector_checks_cons (line 1266). *)
Theorem compile_selector_dispatch_linear_eqns[local]:
  ∀selectors fallback_lbl st st'.
    compile_selector_dispatch_linear selectors fallback_lbl st = ((),st') ⇔
    ∃cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5 old_lbl cs6
       raw cs7 method_id cs8 cs9.
      emit_op CALLDATASIZE [] st = (cds,cs1) ∧
      emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
      emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
      fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
      emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
      new_block dispatch_lbl cs5 = (old_lbl,cs6) ∧
      emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
      emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
      compile_selector_checks method_id selectors cs8 = ((),cs9) ∧
      emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st')
Proof
  simp[compile_selector_dispatch_linear_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def] >>
  rpt gen_tac >> eq_tac >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[])
QED

(* Combined helper: from prefix_invariants facts to entry block lookup.
   Uses irule to avoid variable capture issues with qspecl_then. *)
Theorem linear_dispatch_entry_lookup[local]:
  ∀st cs5 dispatch_lbl cs6 cs8 cs9 st' selectors method_id.
    compile_state_ok st ∧
    cs5.cs_current_bb = st.cs_current_bb ∧ cs5.cs_blocks = st.cs_blocks ∧
    cs6.cs_current_bb = dispatch_lbl ∧
    same_blocks cs6 cs8 ∧ compile_state_ok cs8 ∧
    dispatch_lbl ≠ st.cs_current_bb ∧
    compile_selector_checks method_id selectors cs8 = ((),cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st') ∧
    new_block dispatch_lbl cs5 = (st.cs_current_bb, cs6)
    ⇒
    ∃bb. lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
         bb.bb_instructions = cs5.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  fs[same_blocks_def] >>
  (* Inline the proof of entry_block_findable to avoid variable capture *)
  `cs6.cs_blocks = <|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|> :: st.cs_blocks`
    by (drule new_block_props >> simp[]) >>
  `FIND (λb. b.bb_label = st.cs_current_bb) cs8.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|>`
    by fs[listTheory.FIND_thm] >>
  `st.cs_current_bb ∈ bound_labels cs8` by (
    fs[bound_labels_def, PULL_EXISTS] >> metis_tac[]) >>
  `st.cs_current_bb NOTIN compiler_labels_future cs8.cs_next_label` by (
    fs[compile_state_ok_def, pred_setTheory.IN_DISJOINT] >> metis_tac[]) >>
  drule compile_selector_checks_blocks_preserved >>
  disch_then (qspecl_then [`st.cs_current_bb`,
    `<|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|>`] mp_tac) >>
  simp[] >> strip_tac >>
  `compile_state_ok cs9` by (
    drule compile_selector_checks_bound_labels >> simp[]) >>
  (* compile_state_ok_emit_inst gives cs_blocks, cs_current_bb, and cs_next_label preservation *)
  `compile_state_ok st' ∧ st'.cs_blocks = cs9.cs_blocks ∧
   st'.cs_current_bb = cs9.cs_current_bb ∧ st'.cs_next_label = cs9.cs_next_label`
    by (drule compile_state_ok_emit_inst >> simp[]) >>
  (* Transfer FIND from cs9.cs_blocks to st'.cs_blocks (they're equal by compile_state_ok_emit_inst) *)
  `FIND (λb. b.bb_label = st.cs_current_bb) st'.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs5.cs_current_insts|>`
    by fs[] >>
  drule lookup_block_assemble_in_blocks >> simp[]
QED
(* Boundary lemma: cs8→cs9→st' structural facts.
   Proved in small context where drule works correctly on the single
   emit_inst equation. *)
(* Boundary lemma: cs8→cs9→st' structural facts.
   Takes cs8 facts from prefix_invariants and produces st'-side facts.
   Does NOT re-derive prefix facts (bound_labels st ⊆ bound_labels cs8). *)
Theorem linear_dispatch_st_prime_facts[local]:
  ∀st selectors method_id fallback_lbl cs8 cs9 st'.
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP SND selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP SND selectors) ∧
    compile_state_ok cs8 ∧
    bound_labels cs8 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    cs8.cs_next_label ≥ st.cs_next_label ∧
    compile_selector_checks method_id selectors cs8 = ((), cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((), st')
    ⇒
    compile_state_ok st' ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    bound_labels cs8 ⊆ bound_labels st' ∧
    label_external cs8 fallback_lbl ∧
    EVERY (label_external cs8) (MAP SND selectors) ∧
    ¬MEM fallback_lbl (MAP SND selectors) ∧
    lookup_block fallback_lbl (assemble_blocks st') = NONE
Proof
  rpt gen_tac >> strip_tac >>
  (* cs9 facts *)
  drule compile_selector_checks_bound_labels >> simp[] >> strip_tac >>
  (* st' facts *)
  drule compile_state_ok_emit_inst >> simp[] >> strip_tac >>
  (* bound_labels chain: st → cs8 → cs9 → st' *)
  `bound_labels cs9 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label` by (
    match_mp_tac bound_labels_subset_trans >>
    qexists `cs8` >> simp[]) >>
  `bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label` by simp[] >>
  (* label_external cs8 *)
  `label_external cs8 fallback_lbl` by (
    mp_tac (Q.SPECL [`st`, `cs8`, `fallback_lbl`]
      label_external_through_compile_ops) >> simp[]) >>
  `EVERY (label_external cs8) (MAP SND selectors)` by (
    mp_tac (Q.SPECL [`st`, `cs8`] EVERY_label_external_preserved) >> simp[]) >>
  `¬MEM fallback_lbl (MAP SND selectors)` by fs[] >>
  `lookup_block fallback_lbl (assemble_blocks st') = NONE` by
    metis_tac[label_external_not_in_assembled] >>
  (* bound_labels cs8 ⊆ bound_labels st' : cs8 ⊆ cs9 = st' *)
  `bound_labels cs8 ⊆ bound_labels cs9` by
    metis_tac[compile_selector_checks_bound_labels_mono] >>
  simp[]
QED

(* cs_next_var is monotonically non-decreasing through the entire compile
   chain cs3 → cs4 → ... → st'. Each emit_op adds 1, each emit_inst /
   fresh_label / new_block preserves. compile_selector_checks is
   non-decreasing. Consequence: fresh_vars_wrt cs3 ss ⇒ fresh_vars_wrt st' ss. *)
Theorem linear_dispatch_next_var_chain[local]:
  ∀st cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 st'
    cds has_sel has_sel2 dispatch_lbl old_lbl raw method_id
    selectors fallback_lbl ss.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
    emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
    new_block dispatch_lbl cs5 = (old_lbl,cs6) ∧
    emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
    emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
    compile_selector_checks method_id selectors cs8 = ((),cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st') ∧
    fresh_vars_wrt cs3 ss
    ⇒ fresh_vars_wrt st' ss
Proof
  rpt gen_tac >> strip_tac >>
  `cs4.cs_next_var = cs3.cs_next_var` by metis_tac[fresh_label_props] >>
  `cs5.cs_next_var = cs4.cs_next_var` by metis_tac[emit_inst_extends] >>
  `cs6.cs_next_var = cs5.cs_next_var` by metis_tac[new_block_props] >>
  `cs7.cs_next_var = cs6.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
  `cs8.cs_next_var = cs7.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
  `cs9.cs_next_var ≥ cs8.cs_next_var` by metis_tac[compile_selector_checks_next_var_mono] >>
  `st'.cs_next_var = cs9.cs_next_var` by metis_tac[emit_inst_extends] >>
  `st'.cs_next_var ≥ cs3.cs_next_var` by decide_tac >>
  metis_tac[fresh_vars_wrt_mono]
QED


(* Dispatch branch: from jump_to dispatch_lbl ss_prefix, run the
   CALLDATALOAD+SHR prefix, then dispatch through selector checks.
   Extracted as a boundary lemma to keep the main proof context small. *)
(* Tiny bridge: run_inst_seq preserves current_bb when starting from jump_to *)
Theorem run_inst_seq_preserves_current_bb_jump_to[local]:
  ∀is lbl ss ss'.
    run_inst_seq is (jump_to lbl ss) = OK ss' ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) is ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) is ∧
    ¬ss.vs_halted
    ⇒ ss'.vs_current_bb = lbl
Proof
  rpt strip_tac >>
  Q.SPECL_THEN [`is`, `jump_to lbl ss`, `ss'`] mp_tac
    run_inst_seq_preserves_current_bb >>
  simp[jump_to_vs_halted, jump_to_vs_current_bb]
QED



(* Boundary lemma (cons step): the first selector step finalizes the dispatch
   block (st.cs_current_bb) into cs_blocks with instructions = cs4.cs_current_insts,
   which extend st.cs_current_insts. Also gives the label-space facts needed for
   compile_selector_checks_blocks_preserved. *)
Theorem selector_step_dispatch_block[local]:
  ∀st method_id sel match_op cs1 match_lbl cs2 next_lbl cs3 cs4
     old1 cs5 cs6 old2 cs7 fn_label.
    emit_op EQ [method_id; Lit (n2w sel)] st = (match_op,cs1) ∧
    fresh_label "match" cs1 = (match_lbl,cs2) ∧
    fresh_label "next" cs2 = (next_lbl,cs3) ∧
    emit_inst JNZ [match_op; Label match_lbl; Label next_lbl] [] cs3 = ((),cs4) ∧
    new_block match_lbl cs4 = (old1,cs5) ∧
    emit_inst JMP [Label fn_label] [] cs5 = ((),cs6) ∧
    new_block next_lbl cs6 = (old2,cs7) ∧
    compile_state_ok st
    ⇒
    FIND (λb. b.bb_label = st.cs_current_bb) cs7.cs_blocks =
      SOME <|bb_label := st.cs_current_bb; bb_instructions := cs4.cs_current_insts|> ∧
    st.cs_current_bb ≠ cs7.cs_current_bb ∧
    st.cs_current_bb ∉ compiler_labels_future cs7.cs_next_label ∧
    inst_extends st cs4
Proof
  rpt gen_tac >> strip_tac >>
  (* Get compile_state_ok cs4, bound_labels, label_external from step chain *)
  drule_all step_emit_chain_state_ok >> disch_tac >>
  pop_assum (STRIP_ASSUME_TAC o SPEC_ALL) >>
  (* Get compile_state_ok cs7, bound_labels cs7, cs7.cs_next_label from full chain *)
  drule_all step_chain_cs7_ok >> disch_tac >>
  pop_assum (STRIP_ASSUME_TAC o SPEC_ALL) >>
  (* new_block_props: cs5 structure *)
  qpat_x_assum `new_block match_lbl cs4 = (old1,cs5)`
    (strip_assume_tac o MATCH_MP new_block_props) >>
  (* new_block_props: cs7 structure *)
  qpat_x_assum `new_block next_lbl cs6 = (old2,cs7)`
    (strip_assume_tac o MATCH_MP new_block_props) >>
  (* cs4.cs_current_bb = st.cs_current_bb (preserved through emit chain) *)
  `cs1.cs_current_bb = st.cs_current_bb` by
    metis_tac[compile_state_ok_emit_op] >>
  `cs2.cs_current_bb = cs1.cs_current_bb` by metis_tac[fresh_label_props] >>
  `cs3.cs_current_bb = cs2.cs_current_bb` by metis_tac[fresh_label_props] >>
  `cs4.cs_current_bb = cs3.cs_current_bb` by metis_tac[emit_inst_extends] >>
  `cs4.cs_current_bb = st.cs_current_bb` by simp[] >>
  (* Dispatch block finalized into cs5.cs_blocks *)
  `FIND (λb. b.bb_label = st.cs_current_bb) cs5.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by
    simp[listTheory.FIND_thm] >>
  (* emit_inst JMP preserves blocks *)
  `cs6.cs_blocks = cs5.cs_blocks` by metis_tac[emit_inst_extends] >>
  `FIND (λb. b.bb_label = st.cs_current_bb) cs6.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by
    metis_tac[] >>
  (* dispatch_lbl ≠ match_lbl and ≠ next_lbl since both are fresh labels *)
  `st.cs_current_bb ≠ match_lbl` by (
    `match_lbl ∉ bound_labels st` by metis_tac[step_emit_chain_state_ok, label_external_def] >>
    `st.cs_current_bb ∈ bound_labels st` by fs[bound_labels_def] >>
    metis_tac[]) >>
  `st.cs_current_bb ≠ next_lbl` by (
    `next_lbl ∉ bound_labels st` by metis_tac[step_emit_chain_state_ok, label_external_def] >>
    `st.cs_current_bb ∈ bound_labels st` by fs[bound_labels_def] >>
    metis_tac[]) >>
  (* cs6.cs_current_bb = match_lbl (preserved from cs5) *)
  `cs6.cs_current_bb = match_lbl` by metis_tac[emit_inst_extends] >>
  (* Dispatch block survives through new_block next_lbl *)
  `FIND (λb. b.bb_label = st.cs_current_bb) cs7.cs_blocks =
    SOME <|bb_label := st.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by
    simp[listTheory.FIND_thm] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    (* st.cs_current_bb ≠ cs7.cs_current_bb:
       cs7.cs_current_bb = next_lbl (from new_block_props) and st.cs_current_bb ≠ next_lbl *)
    metis_tac[]) >>
  (* Remaining: ∉ compiler_labels_future ∧ inst_extends *)
  conj_tac >- (
    `st.cs_current_bb ∉ compiler_labels_future st.cs_next_label` by (
      fs[compile_state_ok_def, pred_setTheory.IN_DISJOINT] >>
      `st.cs_current_bb ∈ bound_labels st` by fs[bound_labels_def] >>
      metis_tac[]) >>
    `cs7.cs_next_label ≥ st.cs_next_label` by decide_tac >>
    `compiler_labels_future cs7.cs_next_label ⊆ compiler_labels_future st.cs_next_label` by
      metis_tac[compiler_labels_future_mono] >>
    metis_tac[pred_setTheory.SUBSET_DEF]) >>
  (* inst_extends st cs4 via boundary lemma (proved in small context) *)
  drule_all step_emit_chain_inst_extends >> simp[]
QED

(* Boundary lemma: the dispatch block in assemble_blocks st' has instructions
   that start with cs8.cs_current_insts. Proved by case split on selectors:
   - []: dispatch_lbl remains the current block in st', found via
     lookup_block_assemble_current. emit_inst JMP extends current_insts.
   - (sel,fn_lbl)::rest: new_block match_lbl cs4 finalizes the dispatch block
     with cs4.cs_current_insts = cs8.cs_current_insts ++ suffix_insts.
     compile_selector_checks_blocks_preserved keeps it through rest+JMP. *)
Theorem dispatch_block_instructions_prefix[local]:
  ∀cs8 cs9 st' dispatch_lbl method_id selectors fallback_lbl bb.
    cs8.cs_current_bb = dispatch_lbl ∧
    compile_state_ok cs8 ∧
    compile_selector_checks method_id selectors cs8 = ((), cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((), st') ∧
    lookup_block dispatch_lbl (assemble_blocks st') = SOME bb
    ⇒
    ∃suffix. bb.bb_instructions = cs8.cs_current_insts ++ suffix
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `selectors` >> gvs[]
  >- (
    (* Empty selectors: cs9 = cs8, dispatch block is still current in st' *)
    gvs[compile_selector_checks_def, comp_return_def] >>
    drule compile_state_ok_emit_inst >> simp[] >> strip_tac >>
    `¬MEM cs8.cs_current_bb (MAP (λbb. bb.bb_label) st'.cs_blocks)` by
      fs[compile_state_ok_def] >>
    imp_res_tac lookup_block_assemble_current >>
    gvs[optionTheory.SOME_11, basic_block_11] >>
    drule emit_inst_extends >> rw[inst_extends_def] >>
    qexists `emitted_insts cs8 st'` >>
    simp[emitted_insts_def])
  >- (
    (* Cons case: selectors = h::t where h = (sel,fn_label) *)
    PairCases_on `h` >>
    qpat_x_assum `compile_selector_checks _ _ cs8 = _` mp_tac >>
    simp[compile_selector_checks_cons_eqn] >> rpt strip_tac >>
    (* Apply selector_step_dispatch_block: gives FIND + inst_extends cs8 cs4 *)
    drule_all selector_step_dispatch_block >> strip_tac >>
    (* Get compile_state_ok cs7 *)
    drule_all step_chain_cs7_ok >> strip_tac >>
    pop_assum (STRIP_ASSUME_TAC o SPEC_ALL) >>
    (* Propagate FIND through compile_selector_checks rest *)
    `FIND (λb. b.bb_label = cs8.cs_current_bb) cs9.cs_blocks =
      SOME <|bb_label := cs8.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by (
      irule compile_selector_checks_blocks_preserved >>
      qexistsl [`method_id`, `t`] >> simp[] >>
      qexists `cs7` >> simp[] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
    (* emit_inst JMP preserves blocks *)
    `st'.cs_blocks = cs9.cs_blocks` by metis_tac[emit_inst_extends] >>
    (* Convert FIND to lookup_block *)
    `lookup_block cs8.cs_current_bb (assemble_blocks st') =
      SOME <|bb_label := cs8.cs_current_bb; bb_instructions := cs4.cs_current_insts|>` by
      metis_tac[lookup_block_assemble_in_blocks] >>
    (* Equate lookup results and extract suffix *)
    gvs[] >> fs[inst_extends_def] >> metis_tac[])
QED

(* Bridge lemma: running the CALLDATALOAD+SHR prefix via fragment_prefix_chain.
   Extracted from the by-block to work in a small context.
   Takes dispatch_bb.bb_instructions as an explicit assumption to avoid
   the assemble_blocks st' vs assemble_blocks cs8 mismatch. *)
Theorem linear_dispatch_prefix_bridge[local]:
  ∀ctx cs6 cs8 st' dispatch_lbl ss_prefix ss2 dispatch_bb fuel suffix.
    cs8.cs_current_insts = emitted_insts cs6 cs8 ∧
    cs6.cs_current_bb = dispatch_lbl ∧
    cs6.cs_current_insts = [] ∧
    same_blocks cs6 cs8 ∧
    compile_state_ok cs6 ∧
    fresh_vars_wrt cs6 (jump_to dispatch_lbl ss_prefix) ∧
    fresh_vars_wrt cs8 ss2 ∧
    lookup_block dispatch_lbl (assemble_blocks st') = SOME dispatch_bb ∧
    dispatch_bb.bb_instructions = emitted_insts cs6 cs8 ++ suffix ∧
    run_inst_seq (emitted_insts cs6 cs8) (jump_to dispatch_lbl ss_prefix) = OK ss2 ∧
    EVERY (λi. ¬is_terminator i.inst_opcode) (emitted_insts cs6 cs8) ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE) (emitted_insts cs6 cs8) ∧
    inst_extends cs6 cs8 ∧
    ¬ss_prefix.vs_halted ∧
    ¬ss2.vs_halted
    ⇒
    run_compiled_fragment ctx cs6 st' (jump_to dispatch_lbl ss_prefix) fuel =
    run_compiled_fragment ctx cs8 st' ss2 fuel
Proof
  rpt strip_tac >>
  `ss2.vs_current_bb = dispatch_lbl` by (
    Q.SPECL_THEN [`emitted_insts cs6 cs8`, `dispatch_lbl`, `ss_prefix`, `ss2`]
      mp_tac run_inst_seq_preserves_current_bb_jump_to >>
    simp[]) >>
  `(jump_to dispatch_lbl ss_prefix) with vs_current_bb := dispatch_lbl =
    jump_to dispatch_lbl ss_prefix` by
    simp[venom_state_component_equality, jump_to_vs_current_bb] >>
  `cs8.cs_current_bb = dispatch_lbl` by fs[same_blocks_def] >>
  `∀k. k < LENGTH (emitted_insts cs6 cs8) ⇒
    get_instruction dispatch_bb k = SOME (EL k (emitted_insts cs6 cs8))` by (
    simp[get_instruction_def] >> rpt strip_tac >>
    `k < LENGTH dispatch_bb.bb_instructions` by simp[] >>
    simp[rich_listTheory.EL_APPEND]) >>
  ho_match_mp_tac fragment_prefix_chain >>
  qexistsl [`dispatch_bb`, `emitted_insts cs6 cs8`] >>
  rw[same_blocks_def, jump_to_vs_current_bb, jump_to_vs_inst_idx,
     jump_to_vs_halted, fresh_vars_wrt_jump_to]
QED

(* Fuel composition: compose rfb-to-rcf bridge with prefix bridge and
   dispatch result, yielding an existential fuel witness for rfb.
   This is the KEY abstraction boundary that prevents >4KB goal states
   in branch_correct by keeping the fuel composition in 3 antecedents. *)
Theorem fragment_fuel_composition[local]:
  ∀ctx st cs st' lbl ss_prefix cs' ss_mid fuel0 ss'.
    (∀fuel. run_fragment_blocks (SUC fuel) ctx (assemble_function st st')
              (jump_to lbl ss_prefix) =
            run_compiled_fragment ctx cs st' (jump_to lbl ss_prefix) fuel) ∧
    (∀fuel. run_compiled_fragment ctx cs st' (jump_to lbl ss_prefix) fuel =
            run_compiled_fragment ctx cs' st' ss_mid fuel) ∧
    run_compiled_fragment ctx cs' st' ss_mid fuel0 = OK ss'
    ⇒ ∃fuel. run_fragment_blocks fuel ctx (assemble_function st st')
               (jump_to lbl ss_prefix) = OK ss'
Proof
  rpt strip_tac >>
  qexists `SUC fuel0` >> simp[]
QED

Theorem linear_dispatch_branch_correct[local]:
  ∀st selectors fallback_lbl method_id raw cs6 cs7 cs8 cs9 st'
    ss_prefix ss ctx dispatch_lbl.
    emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
    emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
    compile_selector_checks method_id selectors cs8 = ((),cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st') ∧
    cs6.cs_current_bb = dispatch_lbl ∧ cs6.cs_current_insts = [] ∧
    compile_state_ok cs6 ∧ compile_state_ok cs8 ∧
    same_blocks cs6 cs8 ∧
    EVERY (label_external cs8) (MAP SND selectors) ∧
    label_external cs8 fallback_lbl ∧
    ¬MEM fallback_lbl (MAP SND selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP SND selectors) ∧
    fresh_vars_wrt cs6 (jump_to dispatch_lbl ss_prefix) ∧
    compile_state_ok st' ∧
    bound_labels cs8 ⊆ bound_labels st' ∧
    observable_equiv ss ss_prefix ∧
    ss_prefix.vs_memory = ss.vs_memory ∧
    ss_prefix.vs_call_ctx = ss.vs_call_ctx ∧
    ¬ss_prefix.vs_halted ∧
    lookup_block dispatch_lbl (assemble_blocks st') ≠ NONE ∧
    (∀fuel.
      run_fragment_blocks (SUC fuel) ctx (assemble_function st st')
        (jump_to dispatch_lbl ss_prefix) =
      run_compiled_fragment ctx cs6 st' (jump_to dispatch_lbl ss_prefix) fuel)
    ⇒
    ∃fuel ss'.
      run_fragment_blocks fuel ctx (assemble_function st st')
        (jump_to dispatch_lbl ss_prefix) = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP SND selectors)) ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧ fresh_vars_wrt st' ss'
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: CALLDATALOAD+SHR produces ss2, method_v *)
  mp_tac (Q.SPECL [`cs6`, `raw`, `cs7`, `method_id`, `cs8`,
    `jump_to dispatch_lbl ss_prefix`] calldataload_shr_correct) >>
  impl_tac >- simp[jump_to_vs_halted, fresh_vars_wrt_jump_to] >>
  strip_tac >>
  fs[jump_to_vs_memory, jump_to_vs_call_ctx] >>
  (* Step 2: Derive prefix facts *)
  `cs8.cs_current_insts = emitted_insts cs6 cs8` by fs[inst_extends_def] >>
  `cs8.cs_current_bb = dispatch_lbl` by fs[same_blocks_def] >>
  `∃dispatch_bb. lookup_block dispatch_lbl (assemble_blocks st') = SOME dispatch_bb`
    by (Cases_on `lookup_block dispatch_lbl (assemble_blocks st')` >> fs[]) >>
  `∃suffix. dispatch_bb.bb_instructions = cs8.cs_current_insts ++ suffix`
    by (mp_tac (Q.SPECL [`cs8`, `cs9`, `st'`, `dispatch_lbl`, `method_id`,
        `selectors`, `fallback_lbl`, `dispatch_bb`]
        dispatch_block_instructions_prefix) >>
        impl_tac >- simp[] >> simp[]) >>
  `dispatch_bb.bb_instructions = emitted_insts cs6 cs8 ++ suffix` by simp[] >>
  (* Step 3: Prefix bridge *)
  `∀fuel. run_compiled_fragment ctx cs6 st' (jump_to dispatch_lbl ss_prefix) fuel =
         run_compiled_fragment ctx cs8 st' ss2 fuel`
    by (gen_tac >> irule linear_dispatch_prefix_bridge >>
        simp[jump_to_vs_halted, fresh_vars_wrt_jump_to] >>
        qexists `dispatch_bb` >> simp[same_blocks_def]) >>
  (* Step 4: Derive obs_equiv/memory/call_ctx chains BEFORE dispatch *)
  `observable_equiv ss (jump_to dispatch_lbl ss_prefix)`
    by metis_tac[observable_equiv_jump_to, observable_equiv_trans] >>
  `observable_equiv ss ss2` by metis_tac[observable_equiv_trans] >>
  `ss2.vs_memory = ss.vs_memory` by simp[] >>
  `ss2.vs_call_ctx = ss.vs_call_ctx` by simp[] >>
  (* Step 5: Apply dispatch_block_correct.
     Use mp_tac + impl_tac to avoid by-block issues with ∨-splitting. *)
  mp_tac (Q.SPECL [`selectors`, `fallback_lbl`, `method_id`,
      `cs8`, `cs9`, `st'`, `ss2`, `ctx`] dispatch_block_correct) >>
  impl_tac >- (simp[] >> qexists `method_v` >> simp[]) >>
  (* strip_tac on dispatch result: ∃ witnesses + ∨ split → 2 subgoals *)
  strip_tac >- (
    (* fallback case: ss'.vs_current_bb = fallback_lbl *)
    mp_tac (Q.SPECL [`ctx`, `st`, `cs6`, `st'`, `dispatch_lbl`,
        `ss_prefix`, `cs8`, `ss2`, `fuel`, `ss'`] fragment_fuel_composition) >>
    impl_tac >- simp[] >> strip_tac >>
    qexistsl [`fuel'`, `ss'`] >> simp[] >>
    metis_tac[observable_equiv_trans]
  ) >>
  (* MEM case: MEM ss'.vs_current_bb (MAP SND selectors) *)
  mp_tac (Q.SPECL [`ctx`, `st`, `cs6`, `st'`, `dispatch_lbl`,
      `ss_prefix`, `cs8`, `ss2`, `fuel`, `ss'`] fragment_fuel_composition) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl [`fuel'`, `ss'`] >> simp[] >>
  metis_tac[observable_equiv_trans]
QED

(* Boundary lemma: compose branch_correct output with the ∀fuel equation.
   branch_correct gives ∃fuel ss'. run_fragment_blocks fuel ... = OK ss' ∧ P;
   the ∀fuel equation bridges rcf → rfb.
   compile_state_ok st' comes from assumptions, not from branch_correct. *)
Theorem linear_dispatch_branch_conclude[local]:
  ∀ctx st st' ss lbl ss_prefix selectors fallback_lbl.
    (∀fuel. run_compiled_fragment ctx st st' ss fuel =
            run_fragment_blocks fuel ctx (assemble_function st st')
              (jump_to lbl ss_prefix)) ∧
    (∃fuel ss'.
       run_fragment_blocks fuel ctx (assemble_function st st')
         (jump_to lbl ss_prefix) = OK ss' ∧
       (ss'.vs_current_bb = fallback_lbl ∨
        MEM ss'.vs_current_bb (MAP SND selectors)) ∧
       observable_equiv ss ss' ∧
       ss'.vs_memory = ss.vs_memory ∧
       ss'.vs_call_ctx = ss.vs_call_ctx ∧
       ¬ss'.vs_halted ∧ fresh_vars_wrt st' ss') ∧
    compile_state_ok st'
    ⇒ ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP SND selectors)) ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧ fresh_vars_wrt st' ss' ∧ compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  qexistsl [`fuel`,`ss'`] >> simp[]
QED


Theorem compile_selector_dispatch_linear_correct:
  ∀ selectors fallback_lbl ss st st' ctx.
    compile_selector_dispatch_linear selectors fallback_lbl st = ((), st') ∧
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP SND selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP SND selectors) ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP SND selectors)) ∧
      observable_equiv ss ss' ∧
      ss'.vs_memory = ss.vs_memory ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  fs[compile_selector_dispatch_linear_eqns] >>
  rpt (pairarg_tac >> fs[]) >>
  rpt strip_tac >>
  (* Step 1: prefix_invariants *)
  mp_tac (Q.SPECL [`st`,`fallback_lbl`,`cds`,`cs1`,`has_sel`,`cs2`,
    `has_sel2`,`cs3`,`dispatch_lbl`,`cs4`,`cs5`,`old_lbl`,`cs6`,
    `raw`,`cs7`,`method_id`,`cs8`] linear_dispatch_prefix_invariants) >>
  impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >> strip_tac >>
  (* Step 2: st_prime_facts *)
  mp_tac (Q.SPECL [`st`,`selectors`,`method_id`,`fallback_lbl`,
    `cs8`,`cs9`,`st'`] linear_dispatch_st_prime_facts) >>
  impl_tac >- (simp[listTheory.ALL_DISTINCT]) >> strip_tac >>
  (* Step 2.5: bound_labels st ⊆ st' *)
  `bound_labels st ⊆ bound_labels st'` by
    metis_tac[pred_setTheory.SUBSET_TRANS] >>
  (* Step 3: lookup_facts *)
  mp_tac (Q.SPECL [`st`,`cs6`,`cs8`,`st'`,`dispatch_lbl`]
    linear_dispatch_lookup_facts) >>
  impl_tac >- simp[] >> strip_tac >>
  (* Step 3.5: cs5 chain *)
  `cs4.cs_current_bb = cs3.cs_current_bb` by metis_tac[fresh_label_props] >>
  `cs4.cs_blocks = cs3.cs_blocks` by metis_tac[fresh_label_props] >>
  `cs5.cs_current_bb = cs4.cs_current_bb` by metis_tac[emit_inst_extends] >>
  `cs5.cs_blocks = cs4.cs_blocks` by metis_tac[emit_inst_extends] >>
  `cs5.cs_current_bb = st.cs_current_bb` by fs[] >>
  `cs5.cs_blocks = st.cs_blocks` by fs[] >>
  (* Step 4: entry_lookup *)
  mp_tac (Q.SPECL [`st`,`cs5`,`dispatch_lbl`,`cs6`,`cs8`,`cs9`,`st'`,
    `selectors`,`method_id`] linear_dispatch_entry_lookup) >>
  impl_tac >- simp[] >> strip_tac >>
  (* Step 4.5: derive fresh_vars_wrt cs3 ss for next_var_chain *)
  `cs1.cs_next_var = st.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
  `cs2.cs_next_var = cs1.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
  `cs3.cs_next_var = cs2.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
  `cs3.cs_next_var ≥ st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt cs3 ss` by metis_tac[fresh_vars_wrt_mono] >>
  (* Step 5: next_var_chain *)
  mp_tac (Q.SPECL [`st`,`cs1`,`cs2`,`cs3`,`cs4`,`cs5`,`cs6`,`cs7`,`cs8`,
    `cs9`,`st'`,`cds`,`has_sel`,`has_sel2`,`dispatch_lbl`,`old_lbl`,
    `raw`,`method_id`,`selectors`,`fallback_lbl`,`ss`]
    linear_dispatch_next_var_chain) >>
  impl_tac >- simp[] >> strip_tac >>
  (* Step 6: entry_prefix_simple *)
  mp_tac (Q.SPECL [`st`,`fallback_lbl`,`cds`,`cs1`,`has_sel`,`cs2`,
    `has_sel2`,`cs3`,`dispatch_lbl`,`cs4`,`cs5`,`st'`,`ss`,`ctx`,`bb`]
    linear_dispatch_entry_prefix_simple) >>
  impl_tac >- simp[] >> strip_tac >>
  (* Step 6.5: derive fresh_vars_wrt cs6 (jump_to dispatch_lbl ss_prefix) for rfb_to_rcf *)
  `cs4.cs_next_var = cs3.cs_next_var` by metis_tac[fresh_label_props] >>
  `cs5.cs_next_var = cs4.cs_next_var` by metis_tac[emit_inst_extends] >>
  `cs6.cs_next_var = cs5.cs_next_var` by metis_tac[new_block_props] >>
  `cs6.cs_next_var ≥ cs3.cs_next_var` by decide_tac >>
  `fresh_vars_wrt cs6 ss_prefix` by metis_tac[fresh_vars_wrt_mono] >>
  (* Step 7: rfb_to_rcf *)
  mp_tac (Q.SPECL [`ctx`,`st`,`cs6`,`st'`,`ss_prefix`,`dispatch_lbl`]
    linear_dispatch_rfb_to_rcf) >>
  impl_tac >- (
    simp[jump_to_vs_halted, fresh_vars_wrt_jump_to,
         jump_to_vs_current_bb]) >>
  strip_tac >>
  (* Clean up dead assumptions before Cases_on to keep context small.
     DO NOT kill CALLDATALOAD/SHR/compile_selector_checks/JMP --
     they are antecedents of linear_dispatch_branch_correct's impl_tac. *)
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` kall_tac >>
  qpat_x_assum `emit_op LT _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` kall_tac >>
  qpat_x_assum `fresh_label _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `new_block _ _ = _` kall_tac >>
  qpat_x_assum `cs1.cs_next_var = _` kall_tac >>
  qpat_x_assum `cs2.cs_next_var = _` kall_tac >>
  qpat_x_assum `cs3.cs_next_var = _` kall_tac >>
  qpat_x_assum `cs3.cs_next_var ≥ _` kall_tac >>
  qpat_x_assum `fresh_vars_wrt cs3 ss` kall_tac >>
  qpat_x_assum `cs4.cs_current_bb = _` kall_tac >>
  qpat_x_assum `cs4.cs_blocks = _` kall_tac >>
  qpat_x_assum `cs5.cs_current_bb = _` kall_tac >>
  qpat_x_assum `cs5.cs_blocks = _` kall_tac >>
  qpat_x_assum `cs4.cs_next_var = _` kall_tac >>
  qpat_x_assum `cs5.cs_next_var = _` kall_tac >>
  qpat_x_assum `cs6.cs_next_var = _` kall_tac >>
  qpat_x_assum `cs6.cs_next_var ≥ _` kall_tac >>
  qpat_x_assum `fresh_vars_wrt cs3 ss_prefix` kall_tac >>
  qpat_x_assum `old_lbl = _` kall_tac >>
  qpat_x_assum `compile_state_ok cs3` kall_tac >>
  qpat_x_assum `compile_state_ok st` kall_tac >>
  (* Step 8: specialize ∀fuel inside each Cases_on branch *)
  Cases_on `cond_v ≠ 0w`
  >- (
    (* dispatch branch: get witnesses from branch_correct, bridge via ∀fuel, qexistsl *)
    mp_tac (Q.SPECL [`st`,`selectors`,`fallback_lbl`,`method_id`,`raw`,
      `cs6`,`cs7`,`cs8`,`cs9`,`st'`,`ss_prefix`,`ss`,`ctx`,`dispatch_lbl`]
      linear_dispatch_branch_correct) >>
    impl_tac >- (
      simp[fresh_vars_wrt_jump_to, jump_to_vs_current_bb,
           jump_to_vs_halted, jump_to_vs_memory, jump_to_vs_call_ctx,
           listTheory.ALL_DISTINCT] >>
      metis_tac[]) >>
    DISCH_THEN (qx_choose_then `fuel0` (qx_choose_then `ss0`
      (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) >>
    (* Bridge: specialize ∀fuel equation to fuel0 *)
    `run_compiled_fragment ctx st st' ss fuel0 =
      run_fragment_blocks fuel0 ctx (assemble_function st st')
        (jump_to dispatch_lbl ss_prefix)`
      by (qpat_x_assum `∀fuel. run_compiled_fragment _ _ _ _ fuel = if _ then _ else _`
            (qspec_then `fuel0` mp_tac) >> simp[]) >>
    qexistsl [`fuel0`,`ss0`] >> simp[]
  ) >>
  mp_tac (Q.SPECL [`ctx`,`st`,`st'`,`ss_prefix`,`fallback_lbl`]
    linear_dispatch_fallback_branch) >>
  impl_tac >- (
    simp[observable_equiv_jump_to, jump_to_vs_memory,
         jump_to_vs_call_ctx, jump_to_vs_halted] >>
    (* lookup_block, compile_state_ok, ¬halted are all direct from assumptions *)
    `fresh_vars_wrt st' ss_prefix` by (
      `cs7.cs_next_var = cs6.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
      `cs8.cs_next_var = cs7.cs_next_var + 1` by metis_tac[emitted_insts_emit_op] >>
      `cs9.cs_next_var ≥ cs8.cs_next_var` by metis_tac[compile_selector_checks_next_var_mono] >>
      `st'.cs_next_var = cs9.cs_next_var` by metis_tac[emit_inst_extends] >>
      `st'.cs_next_var ≥ cs6.cs_next_var` by decide_tac >>
      metis_tac[fresh_vars_wrt_mono]) >>
    simp[]) >>
  DISCH_THEN (qx_choose_then `fuel0` (qx_choose_then `ss0`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) >>
  (* Bridge: specialize ∀fuel equation to fuel0 *)
  `run_compiled_fragment ctx st st' ss fuel0 =
    run_fragment_blocks fuel0 ctx (assemble_function st st')
      (jump_to fallback_lbl ss_prefix)`
    by (qpat_x_assum `∀fuel. run_compiled_fragment _ _ _ _ fuel = if _ then _ else _`
          (qspec_then `fuel0` mp_tac) >> simp[]) >>
  qexistsl [`fuel0`,`ss0`] >> simp[] >>
  metis_tac[observable_equiv_trans]

QED

(* ===== Sparse table dispatch proof status ===== *)

(* Sparse bucket_count > 1 needs a lower_dload-style code-layout invariant:
   BUCKET_HEADERS and bucket labels must be resolved in vs_labels, and vs_code
   must contain the assembled code plus data sections.  DJMP's dynamic operand
   is a bytecode destination constrained to the listed labels, so IR execution
   resolves it through vs_labels. *)

Theorem djmp_target_not_in_label_set_counterexample:
  step_inst_base (mk_inst 0 DJMP [Var (STRING #"%" (toString 0)); Label "a"; Label "b"] [])
    (<| vs_vars := FEMPTY |+ (STRING #"%" (toString 0), 2w:bytes32);
       vs_labels := FEMPTY |>) = Error "djmp: target not in label set"
Proof
  EVAL_TAC
QED

(* ===== Real proof of sparse dispatch (≤1 case) ===== *)
(* Uses linear_dispatch infrastructure — projected selectors share identical proof structure. *)

Theorem sparse_snd_projection[local]:
  ∀l. MAP SND (MAP (λ(sel,lbl,_). (sel,lbl)) l) = MAP (FST o SND) l
Proof
  Induct >> simp[] >> Cases_on `h` >> Cases_on `r` >> simp[]
QED

Theorem sparse_dispatch_st_prime_facts[local]:
  ∀st selectors method_id fallback_lbl cs8 cs9 st'.
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP (FST o SND) selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP (FST o SND) selectors) ∧
    compile_state_ok cs8 ∧
    bound_labels cs8 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    cs8.cs_next_label ≥ st.cs_next_label ∧
    compile_selector_checks method_id (MAP (λ(sel,lbl,_). (sel,lbl)) selectors) cs8 = ((),cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st')
    ⇒
    compile_state_ok st' ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    bound_labels cs8 ⊆ bound_labels st' ∧
    label_external cs8 fallback_lbl ∧
    EVERY (label_external cs8) (MAP (FST o SND) selectors) ∧
    ¬MEM fallback_lbl (MAP (FST o SND) selectors) ∧
    lookup_block fallback_lbl (assemble_blocks st') = NONE
Proof
  rpt gen_tac >> strip_tac >>
  (* cs9 and st' facts from compile_selector_checks + emit_inst *)
  drule compile_selector_checks_bound_labels >> simp[] >> strip_tac >>
  drule compile_state_ok_emit_inst >> simp[] >> strip_tac >>
  (* bound_labels chain *)
  `bound_labels cs9 ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label` by (
    match_mp_tac bound_labels_subset_trans >>
    qexists `cs8` >> simp[]) >>
  `bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label` by simp[] >>
  (* label_external cs8 *)
  `label_external cs8 fallback_lbl` by (
    mp_tac (Q.SPECL [`st`,`cs8`,`fallback_lbl`] label_external_through_compile_ops) >>
    simp[]) >>
  `EVERY (label_external cs8) (MAP (FST o SND) selectors)` by (
    mp_tac (Q.SPECL [`st`,`cs8`] EVERY_label_external_preserved) >>
    simp[sparse_snd_projection]) >>
  `¬MEM fallback_lbl (MAP (FST o SND) selectors)` by (
    fs[listTheory.ALL_DISTINCT]) >>
  `lookup_block fallback_lbl (assemble_blocks st') = NONE` by
    metis_tac[label_external_not_in_assembled] >>
  (* bound_labels cs8 ⊆ bound_labels st' : cs8 ⊆ cs9 ⊆ st' *)
  `bound_labels cs8 ⊆ bound_labels cs9` by
    metis_tac[compile_selector_checks_bound_labels_mono] >>
  simp[]
QED

(* Boundary lemma for sparse ≤1: wraps steps 1-4 (prefix_invariants through
   entry_lookup) to avoid context bloat in the main proof. *)
Theorem sparse_dispatch_le1_setup[local]:
  ∀st fallback_lbl cds cs1 has_sel cs2 has_sel2 cs3 dispatch_lbl cs4 cs5
    old_lbl cs6 raw cs7 method_id cs8 cs9 st' selectors.
    emit_op CALLDATASIZE [] st = (cds,cs1) ∧
    emit_op LT [cds; Lit 4w] cs1 = (has_sel,cs2) ∧
    emit_op ISZERO [has_sel] cs2 = (has_sel2,cs3) ∧
    fresh_label "dispatch" cs3 = (dispatch_lbl,cs4) ∧
    emit_inst JNZ [has_sel2; Label dispatch_lbl; Label fallback_lbl] [] cs4 = ((),cs5) ∧
    new_block dispatch_lbl cs5 = (old_lbl,cs6) ∧
    emit_op CALLDATALOAD [Lit 0w] cs6 = (raw,cs7) ∧
    emit_op SHR [Lit 224w; raw] cs7 = (method_id,cs8) ∧
    compile_selector_checks method_id (MAP (λ(sel,lbl,_). (sel,lbl)) selectors) cs8 = ((),cs9) ∧
    emit_inst JMP [Label fallback_lbl] [] cs9 = ((),st') ∧
    compile_state_ok st ∧ label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP (FST o SND) selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP (FST o SND) selectors)
    ⇒
    compile_state_ok st' ∧
    bound_labels st' ⊆ bound_labels st ∪ compiler_labels_future st.cs_next_label ∧
    bound_labels st ⊆ bound_labels st' ∧
    label_external cs8 fallback_lbl ∧
    EVERY (label_external cs8) (MAP (FST o SND) selectors) ∧
    ¬MEM fallback_lbl (MAP (FST o SND) selectors) ∧
    lookup_block fallback_lbl (assemble_blocks st') = NONE ∧
    lookup_block dispatch_lbl (assemble_blocks st') ≠ NONE ∧
    same_blocks cs6 cs8 ∧
    cs6.cs_current_bb = dispatch_lbl ∧
    cs6.cs_current_insts = [] ∧
    dispatch_lbl ≠ st.cs_current_bb ∧
    cs5.cs_current_bb = st.cs_current_bb ∧
    cs5.cs_blocks = st.cs_blocks ∧
    ∃bb. lookup_block st.cs_current_bb (assemble_blocks st') = SOME bb ∧
         bb.bb_instructions = cs5.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: prefix_invariants *)
  drule_all linear_dispatch_prefix_invariants >> strip_tac >>
  (* Step 2: st_prime_facts *)
  `ALL_DISTINCT (fallback_lbl :: MAP (FST o SND) selectors)` by
    simp[listTheory.ALL_DISTINCT] >>
  drule_all sparse_dispatch_st_prime_facts >> strip_tac >>
  (* Step 2.5: bound_labels st ⊆ st' *)
  `bound_labels st ⊆ bound_labels st'` by
    metis_tac[pred_setTheory.SUBSET_TRANS] >>
  (* Step 3: lookup_facts *)
  drule_all linear_dispatch_lookup_facts >> strip_tac >>
  (* Step 3.5: cs5 chain *)
  `cs4.cs_current_bb = cs3.cs_current_bb` by metis_tac[fresh_label_props] >>
  `cs4.cs_blocks = cs3.cs_blocks` by metis_tac[fresh_label_props] >>
  `cs5.cs_current_bb = cs4.cs_current_bb` by metis_tac[emit_inst_extends] >>
  `cs5.cs_blocks = cs4.cs_blocks` by metis_tac[emit_inst_extends] >>
  `cs5.cs_current_bb = st.cs_current_bb` by simp[] >>
  `cs5.cs_blocks = st.cs_blocks` by simp[] >>
  (* Step 4: entry_lookup *)
  qpat_x_assum `old_lbl = _` SUBST_ALL_TAC >>
  drule_all linear_dispatch_entry_lookup >> strip_tac >>
  simp[]
QED

(* Bridge: sparse ≤1 compilation equals linear compilation on projected selectors.
   Both eqns lemmas expand to the same existential form of emit equations. *)
Theorem sparse_dispatch_le1_eq_linear[local]:
  ∀selectors bucket_count fallback_lbl st st'.
    bucket_count ≤ 1 ⇒
    (compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st = ((),st') ⇔
     compile_selector_dispatch_linear (MAP (λ(sel,lbl,_). (sel,lbl)) selectors) fallback_lbl st = ((),st'))
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[compile_selector_dispatch_sparse_le1_eqns,
       compile_selector_dispatch_linear_eqns]
QED

(* Boundary lemma: sparse ≤1 correctness reduces to linear on projected selectors.
   This isolates the MAP (FST o SND) ↔ MAP SND (MAP ...) bridging. *)
Theorem sparse_le1_from_linear[local]:
  ∀selectors fallback_lbl ss st st' ctx.
    compile_selector_dispatch_linear (MAP (λ(sel,lbl,_). (sel,lbl)) selectors)
        fallback_lbl st = ((),st') ∧
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP (FST o SND) selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP (FST o SND) selectors) ∧
    fresh_vars_wrt st ss ∧ ¬ss.vs_halted
    ⇒
    ∃fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP (FST o SND) selectors)) ∧
      observable_equiv ss ss' ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  metis_tac[sparse_snd_projection, compile_selector_dispatch_linear_correct]
QED

Theorem compile_selector_dispatch_sparse_correct:
  ∀ selectors bucket_count fallback_lbl ss st st' ctx.
    compile_selector_dispatch_sparse selectors bucket_count fallback_lbl st =
      ((), st') ∧
    compile_state_ok st ∧
    label_external st fallback_lbl ∧
    EVERY (label_external st) (MAP (FST o SND) selectors) ∧
    ALL_DISTINCT (fallback_lbl :: MAP (FST o SND) selectors) ∧
    fresh_vars_wrt st ss ∧
    ¬ss.vs_halted ∧
    ss.vs_memory = [] ∧
    bucket_count ≤ 1
    ⇒
    ∃ fuel ss'.
      run_compiled_fragment ctx st st' ss fuel = OK ss' ∧
      (ss'.vs_current_bb = fallback_lbl ∨
       MEM ss'.vs_current_bb (MAP (FST o SND) selectors)) ∧
      observable_equiv ss ss' ∧
      ss'.vs_call_ctx = ss.vs_call_ctx ∧
      ¬ss'.vs_halted ∧
      fresh_vars_wrt st' ss' ∧
      compile_state_ok st'
Proof
  rpt gen_tac >> strip_tac >>
  `compile_selector_dispatch_linear (MAP (λ(sel,lbl,_). (sel,lbl)) selectors)
      fallback_lbl st = ((),st')` by
    metis_tac[sparse_dispatch_le1_eq_linear] >>
  irule sparse_le1_from_linear >>
  simp[]
QED

(* NOTE [sparse >1 needs table layout]:
   The sparse dispatch >1 case uses OFFSET [Lit 0w; Label "BUCKET_HEADERS"],
   CODECOPY, MLOAD, and DJMP.  Like lower_dload, this is provable only under
   a code-layout invariant connecting emitted data sections to vs_labels and
   vs_code.  The current theorem covers bucket_count ≤ 1 until that invariant
   is added for selector-table data sections. *)
