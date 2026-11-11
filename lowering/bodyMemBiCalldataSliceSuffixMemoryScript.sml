(* Memory checks at the two writes of calldata slicing. *)
Theory bodyMemBiCalldataSliceSuffixMemory
Ancestors
  bodyMemBiCalldataSliceFacts fragExecMem instMemFrontier
  venomState venomInst venomExecSemantics venomMemDefs
  fragExec compileEnv loweringStateRelDefs emitHelper emitHelperProps context loweringSlice
  words list builtinBytes exprLoweringProps freshWrites exprSimDefs arithmetic
  exprSimAlloc loweringPosts finite_map valueTypingMemoryProps builtinBytesMemory
  venomMemProps venomMemProofs venomInstProps exprSimCalldataSlice

Theorem calldata_slice_copy_store_mem:
  eval_operand dst s = SOME wd /\ eval_operand src s = SOME wa /\
  eval_operand len s = SOME wn /\ eval_operand pop s = SOME wp /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  w2n wp + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst i CALLDATACOPY [dst; src; len] [];
     mk_inst j MSTORE [pop; len] []] s
Proof
  strip_tac >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_CALLDATACOPY,
       run_inst_seq_mem_ok_last] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[below_frontier_MSTORE, write_memory_with_expansion_def,
       write_memory_def, eval_operand_def]
QED


(* Same pure-prefix boundary as slice_bounds_writes_fresh in the
   non-exporting exprSimCalldataSlice theory. *)
Theorem calldata_slice_bounds_fresh:
  compile_assert_slice_bounds a num_op limit sa = ((),sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       writes_fresh_def, fresh_write_op_def, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem calldata_slice_copy_store_emitted_mem:
  emit_void CALLDATACOPY [dst; src; len] sa = ((),sm) /\
  emit_void MSTORE [pop; len] sm = ((),sb) /\
  eval_operand dst s = SOME wd /\ eval_operand src s = SOME wa /\
  eval_operand len s = SOME wn /\ eval_operand pop s = SOME wp /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  w2n wp + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  !t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  conj_tac
  >- (irule calldata_slice_copy_store_mem >> metis_tac[]) >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_write2_def, mk_inst_def] >>
  Cases_on `pop` >> Cases_on `len` >>
  gvs[write_memory_with_expansion_def, write_memory_def,
      eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> gvs[mstore_def]
QED

Theorem calldata_slice_checked_tail_mem:
  compile_assert_slice_bounds a num_op limit sa = ((),sm) /\
  emit_void CALLDATACOPY [dst; src; len] sm = ((),sn) /\
  emit_void MSTORE [pop; len] sn = ((),sb) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. len = Var x ==> not_fresh_at sa x) /\
  (!x. pop = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME wd /\ eval_operand src s = SOME wa /\
  eval_operand len s = SOME wn /\ eval_operand pop s = SOME wp /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  w2n wp + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (drule calldata_slice_bounds_extends >> simp[inst_extends_def]) >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans, inst_extends_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  pop_assum SUBST1_TAC >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule compile_assert_slice_bounds_mem_ok >> goal_assum drule) >>
  irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >>
  drule calldata_slice_bounds_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qpat_x_assum `s' = s with vs_vars := _` (strip_assume_tac o
    SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `!op w. (!x. op = Var x ==> not_fresh_at sa x) /\ eval_operand op s = SOME w ==>
          eval_operand op s' = SOME w` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `eval_operand dst s' = SOME wd /\ eval_operand src s' = SOME wa /\
   eval_operand len s' = SOME wn /\ eval_operand pop s' = SOME wp` by
    (rpt conj_tac >> first_assum irule >> simp[]) >>
  irule (cj 1 calldata_slice_copy_store_emitted_mem) >> metis_tac[]
QED

(* Run boundary restated from local slice_calldata_address_size_run in
   exprSimCalldataSlice, extended with the per-instruction memory checks. *)
Theorem calldata_slice_address_size_mem:
  !buf_op data_op len_op sa sm sb s w.
  emit_op ADD [buf_op; Lit 32w] sa = (data_op,sm) /\
  emit_op CALLDATASIZE [] sm = (len_op,sb) /\
  eval_operand buf_op s = SOME w ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 2 /\
  sb.cs_next_id = sa.cs_next_id + 2 /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand data_op t = SOME (w + 32w) /\
    eval_operand len_op t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. data_op = Var x ==> not_fresh_at sb x) /\
    (!x. len_op = Var x ==> not_fresh_at sb x))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
      emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, rich_listTheory.DROP_APPEND1,
       run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_read0_def, eval_operand_def, bind_outputs_def] >>
  simp[lookup_var_update_var, update_var_def, not_fresh_at_def,
       run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_no_ranges] >>
  rpt strip_tac >> gvs[] >> CASE_TAC >> simp[]
QED

Theorem calldata_slice_after_alloc_mem:
  emit_op ADD [buf_op; Lit 32w] sa = (data_op,s1) /\
  emit_op CALLDATASIZE [] s1 = (len_op,s2) /\
  compile_assert_slice_bounds start_op (Lit (n2w n)) len_op s2 = ((),s3) /\
  emit_void CALLDATACOPY [data_op; start_op; Lit (n2w n)] s3 = ((),s4) /\
  emit_void MSTORE [buf_op; Lit (n2w n)] s4 = ((),sb) /\
  eval_operand buf_op s = SOME w /\ eval_operand start_op s = SOME wa /\
  (!x. buf_op = Var x ==> not_fresh_at sa x) /\
  (!x. start_op = Var x ==> not_fresh_at sa x) /\
  n < dimword (:256) /\ w2n w + 32 < dimword (:256) /\
  w2n w + 32 + n <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> drule_all calldata_slice_address_size_mem >> strip_tac >>
  `sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb` by
    (imp_res_tac inst_extends_emit_void >>
     drule calldata_slice_bounds_extends >> strip_tac >>
     metis_tac[inst_extends_trans, inst_extends_def]) >>
  `emitted_insts sa sb = emitted_insts sa s2 ++ emitted_insts s2 sb` by
    (irule emitted_insts_append >> simp[]) >>
  pop_assum SUBST1_TAC >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >>
  `eval_operand buf_op t = SOME w /\ eval_operand start_op t = SOME wa /\
   t.vs_alloca_next = s.vs_alloca_next` by
    (fs[venom_state_component_equality] >>
     Cases_on `buf_op` >> Cases_on `start_op` >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `(!x. buf_op = Var x ==> not_fresh_at s2 x) /\
   (!x. start_op = Var x ==> not_fresh_at s2 x)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
                                      arithmeticTheory.LESS_EQ_ADD]) >>
  `w2n (w + 32w) = w2n w + 32` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD] >>
  `w2n w + 32 <= t.vs_alloca_next /\
   n + w2n (w + 32w) <= t.vs_alloca_next` by simp[] >>
  drule calldata_slice_checked_tail_mem >>
  disch_then drule >> disch_then drule >>
  simp[eval_operand_def, wordsTheory.w2n_add, LESS_MOD] >>
  disch_then irule >> metis_tac[]
QED


Theorem calldata_slice_seq_mem:
  !func cenv cx es n start_op sa sb buf_op s ctx wa.
    compile_slice_calldata start_op (Lit (n2w n))
      (32 + 32 * word_size n) sa = (buf_op,sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    32 + 32 * word_size n < dimword (:256) /\ 0 < n /\
    eval_operand start_op s = SOME wa /\
    (!x. start_op = Var x ==> not_fresh_at sa x) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32 + 32 * word_size n))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt gen_tac >> strip_tac >>
  drule slice_calldata_parts >> strip_tac >> gvs[] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule calldata_slice_allocation_split >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  irule run_inst_seq_mem_ok_append >>
  reverse conj_tac
  >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
      pairarg_tac >> strip_tac >> gvs[] >>
      drule emitted_insts_emit_op >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, mk_inst_def, below_frontier_no_ranges]) >>
  simp[] >>
  `w2n w + (32 + 32 * word_size n) <= t.vs_alloca_next` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> simp[]) >>
  `n <= 32 * word_size n` by simp[valueTypingMemoryPropsTheory.word_size_capacity] >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand start_op t = SOME wa` by
    (Cases_on `start_op` >> gvs[eval_operand_def, lookup_var_def]) >>
  `sm.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> simp[]) >>
  `!x. start_op = Var x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  drule calldata_slice_after_alloc_mem >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  simp[] >> disch_then irule >>
  conj_tac >- metis_tac[] >> qexists_tac `w` >> gvs[] >> decide_tac
QED

Theorem calldata_slice_seq_frontier:
  !insts s t.
    EVERY (\i. i.inst_opcode <> INVOKE) insts /\
    run_inst_seq insts s = OK t ==>
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  Induct >> simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  `s.vs_alloca_next <= v.vs_alloca_next` by
    (Cases_on `h.inst_opcode = ALLOCA`
     >- (irule venomMemPropsTheory.step_inst_alloca_alloca_next_mono >>
         qexistsl_tac [`ARB`, `0`, `h`] >>
         simp[venomExecSemanticsTheory.step_inst_non_invoke,
              venomInstTheory.is_alloca_op_def]) >>
     `v.vs_alloca_next = s.vs_alloca_next` by
       metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_next] >> simp[]) >>
  first_x_assum drule >> simp[]
QED
