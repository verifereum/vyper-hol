(* Static bulk-array children can be re-executed with stale local temporaries. *)
Theory abiDecoderBulkReentry
Ancestors
  abiDecoderBulkExecute abiDecoderBulk abiDecoderArrayInitReentry abiDecoderReentry
  abiDecoderReentrySequence abiDecoderVarSequence abiDecoderVarExtend abiDecoderTypedContract
  abiDecoderCoherence abiDecoderArrayInitExec abiDecoderContract abiDecoderFrame
  abiDecoderFrameCompose abiDecoderLoop abiDecoderAllocation abiDecoderProtectedScratch fragExec
  instIdxIndep exprLoweringProps emitHelperProps compileEnv venomState valueEncoding words list
  arithmetic

Theorem abi_decoder_bulk_reentry_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  drule_all abi_decoder_typed_bulk_fields >> strip_tac >>
  rename1 `run_inst_seq _ (abi_decoder_prune_vars st.cs_next_var initial) = OK clean` >>
  drule_all abi_decoder_sequence_reentry >> strip_tac >>
  rename1 `abi_decoder_vars_extend initial.vs_vars clean actual` >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  qexists_tac `actual` >> gvs[abi_decoder_prune_vars_def]
QED

Theorem abi_decoder_bulk_reentry_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\actual. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
      fresh_vars_wrt limit_st actual /\
      (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
        eval_operand op actual = SOME w) /\
      abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial actual /\
      actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
      actual.vs_halted = initial.vs_halted) (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >> qexists_tac `actual` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_bulk_reentry_execute:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\ fn_has_code st st' fn /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial t /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  strip_tac >> drule_all abi_decoder_bulk_reentry_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  `abi_decoder_budget first last b cap t` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `t:venom_state`]
       abi_decoder_budget_transport) >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decoder_bulk_reentry_protected:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),st') /\ ~dec_info_needs_clamp ei /\ fn_has_code st st' fn /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial t /\
    abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
    (!other protected. other IN abi_decoder_ids first last /\
      FLOOKUP initial.vs_allocas other = SOME (protected,32) ==>
      FLOOKUP t.vs_allocas other = SOME (protected,32) /\ mload protected t = mload protected initial) /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx fn initial t
Proof
  strip_tac >> drule_all abi_decoder_bulk_reentry_execute >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_output_separated >> disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `t:venom_state`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    abi_decoder_bulk_scratch_preservation) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)] initial t`
    by (irule abi_decoder_frame_from_output >> simp[]) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
