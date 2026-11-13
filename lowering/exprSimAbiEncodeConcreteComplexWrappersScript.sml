Theory exprSimAbiEncodeConcreteComplexWrappers
Ancestors
  abiEncoderWindowComplex abiEncoderWindowCursor abiEncoderWindowPhase
  abiEncoderWindowStructuralMembers
  abiEncoderWindowSequence abiEncoderWindowContract abiEncoderWindowMembers
  abiEncoderRegisteredEffect abiEncoderWindowLookup abiEncoderProps
  exprSimAbiEncodeConcreteCompose emitHelperProps freshWrites
  abiDecodeRanges fragExec venomState compileEnv words pred_set list valueEncodingProps
  exprLoweringProps abiEncoderInput abiEncoderPrimitiveEffect allocaSiteResource
  context emitHelper rich_list arithmetic venomMemDefs

Theorem abi_encode_complex_finish_load_concrete:
  window_phase ctx func st load ids [(d,LENGTH (enc at av))] s u /\
  ids SUBSET window_alloca_sites func (frag_ids st en) /\
  st.cs_next_var <= load.cs_next_var /\
  mem_bytes_at d (LENGTH (enc at av)) u.vs_memory = enc at av /\
  eval_operand dp u = SOME (n2w slot) /\ slot < dimword (:256) /\
  mem_word_at slot u.vs_memory = n2w (LENGTH (enc at av)) /\
  emit_op MLOAD [dp] load = (out,en) /\ fn_has_code load en func /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
  (!x. ~not_fresh_at en x ==> lookup_var x u = lookup_var x s) ==>
  ?raw. window_pure_seq load en u raw /\
    window_strong_result ctx func st en out at av d s
      (raw with vs_inst_idx := LENGTH en.cs_current_insts) /\
    (!x. ~not_fresh_at en x ==>
      lookup_var x (raw with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule_all window_cursor_load_sequence >> strip_tac >>
  rename1 `window_pure_seq load en u raw` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at en) i.inst_outputs)
    (emitted_insts load en)` by
    (irule abi_window_emit_register_bounds >>
     qexistsl_tac [`[dp]`, `MLOAD`, `out`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==>
    lookup_var x (raw with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x u` by
    metis_tac[window_seq_high_vars, window_pure_seq_def] >>
  `window_phase ctx func load en {} [] u
    (raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    metis_tac[window_pure_seq_phase] >>
  `eval_operand out (raw with vs_inst_idx := LENGTH en.cs_current_insts) =
    SOME (mload slot u)` by
    (Cases_on `out` >> fs[eval_operand_def, lookup_var_def] >>
     metis_tac[window_pure_seq_def, window_seq_labels]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func load en {} [] u t` >>
  `abi_encoder_registered_effect {} [] u t` by metis_tac[window_phase_effect] >>
  `mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av` by
    (irule EQ_TRANS >> qexists_tac `mem_bytes_at d (LENGTH (enc at av)) u.vs_memory` >>
     conj_tac >- (irule abi_encoder_window_effect_bytes >>
       qexistsl_tac [`{}`, `[]`] >> simp[]) >> asm_rewrite_tac[]) >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_x_assum `abi_encoder_registered_effect {} [] u t` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> simp[] >> metis_tac[]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc at av))]`, `load`, `{}`, `[]`, `u`] >>
     asm_rewrite_tac[EVERY_DEF, EMPTY_SUBSET]) >>
  qexists_tac `raw` >> asm_rewrite_tac[] >>
  reverse conj_tac >- (fs[Abbr `t`] >> metis_tac[]) >>
  `window_strong_result ctx func st en out at av d s t` suffices_by
    simp_tac bool_ss [Abbr `t`] >>
  irule window_complex_phase_result >> asm_rewrite_tac[] >>
  qpat_x_assum `mem_word_at slot _ = _` mp_tac >>
  asm_rewrite_tac[mem_word_at_eq_mload] >> disch_then SUBST1_TAC >> REFL_TAC
QED

Theorem abi_encode_complex_initialize_concrete_sizes:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?raw slot. window_seq st ready s raw /\
    window_phase ctx func st ready {st.cs_next_id} [] s
      (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) ready
      (raw with vs_inst_idx := LENGTH ready.cs_current_insts) /\
    mem_word_at slot raw.vs_memory = n2w (window_member_head_size infos) /\
    st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
    (!x. ~not_fresh_at ready x ==>
      lookup_var x (raw with vs_inst_idx := LENGTH ready.cs_current_insts) = lookup_var x s) /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP raw.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `cs_extends ready en` by fs[ci_mono_def] >>
  `emit_op ALLOCA [Lit 32w] st = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  `ci_mono st mid /\ ci_mono mid ready` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends st mid /\ cs_extends mid ready` by fs[ci_mono_def] >>
  `fn_has_code st mid func /\ fn_has_code mid ready func /\ fn_has_code ready en func` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `fn_has_code st mid func` mp_tac >>
     simp_tac bool_ss [fn_has_code_def] >> strip_tac >>
     gvs[IS_PREFIX_APPEND] >> irule lookup_block_fn_insts >>
     goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (drule emitted_insts_emit_op >> drule inst_extends_emit_op >> strip_tac >> strip_tac >>
     `st.cs_next_id < en.cs_next_id` by
       (qpat_x_assum `emit_op ALLOCA _ _ = _` mp_tac >>
        simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
        strip_tac >> gvs[ci_mono_def] >> decide_tac) >>
     simp[window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[window_pre_sites] >>
  drule_all window_emit_alloca32_sequence >> strip_tac >>
  rename1 `window_seq st mid s a` >>
  rename1 `FLOOKUP a.vs_allocas st.cs_next_id = SOME (slot,32)` >>
  `window_phase ctx func st mid {st.cs_next_id} [] s
    (a with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (irule window_seq_phase >> asm_rewrite_tac[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st mid {st.cs_next_id} [] s t` >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32)` by simp[Abbr `t`] >>
  `slot < dimword (:256) /\ regions_disjoint (sb,cap) (slot,32) /\
    regions_disjoint (d,LENGTH (enc at (ListV avs))) (slot,32)` by
    (drule_all window_complex_cursor_protected >> simp[Abbr `t`]) >>
  `window_seq mid ready a (mstore slot (n2w (window_member_head_size infos)) a) /\
    abi_encoder_registered_effect {st.cs_next_id} [] a
      (mstore slot (n2w (window_member_head_size infos)) a) /\
    mem_word_at slot (mstore slot (n2w (window_member_head_size infos)) a).vs_memory =
      n2w (window_member_head_size infos)` by
    (irule window_cursor_store_sequence >> asm_rewrite_tac[] >>
     qexistsl_tac [`buf.buf_operand`, `Lit (n2w (window_member_head_size infos))`] >>
     simp[eval_operand_def]) >>
  qmatch_asmsub_abbrev_tac `window_seq mid ready a raw` >>
  `window_seq st ready s raw` by metis_tac[window_seq_chain] >>
  `alloca_inv raw` by
    (simp[Abbr `raw`] >> metis_tac[abi_encoder_primitive_alloca_inv]) >>
  `alloca_room ctx func raw` by
    (irule alloca_room_fields >> qexists_tac `a` >>
     simp[Abbr `raw`, mstore_def, write_memory_with_expansion_def]) >>
  `window_alloca_growth a raw` by
    (irule window_alloca_growth_fields >>
     simp[Abbr `raw`, mstore_def, write_memory_with_expansion_def]) >>
  `window_alloca_growth s raw` by
    (irule window_alloca_growth_trans >> qexists_tac `a` >> asm_rewrite_tac[] >>
     simp[Abbr `raw`, mstore_def, write_memory_with_expansion_def]) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s raw` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `a` >> asm_rewrite_tac[]) >>
  `cs_extends st ready` by metis_tac[cs_extends_trans] >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  `fn_has_code st ready func` by
    (drule_all fn_has_code_split >> metis_tac[]) >>
  `raw.vs_halted = s.vs_halted /\ raw.vs_current_bb = s.vs_current_bb` by
    simp[Abbr `raw`, mstore_def, write_memory_with_expansion_def] >>
  `window_phase ctx func st ready {st.cs_next_id} [] s
    (raw with vs_inst_idx := LENGTH ready.cs_current_insts)` by
    (irule window_seq_phase >> asm_rewrite_tac[]) >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st ready {st.cs_next_id} [] s u` >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id < ready.cs_next_id` by
    (fs[ci_mono_def] >>
     qpat_x_assum `emit_op ALLOCA _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
     qpat_x_assum `_ = mid` (mp_tac o Q.AP_TERM `\st:compile_state. st.cs_next_id`) >>
     simp_tac (srw_ss()) [] >> decide_tac) >>
  `DISJOINT {st.cs_next_id} (window_alloca_sites func (frag_ids ready en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap u.vs_memory` by
    (irule window_alloca_growth_source >> qexistsl_tac [`{st.cs_next_id}`, `[]`, `s`] >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF, IN_SING] >>
     (conj_tac >- metis_tac[window_pre_sites]) >>
     `window_alloca_growth s u /\ abi_encoder_registered_effect {st.cs_next_id} [] s u` by
       metis_tac[window_phase_effect, window_phase_resources] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     asm_rewrite_tac[]) >>
  `eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
    (ListV avs) sb cap d u` by
    (irule window_member_remaining_pre >> asm_rewrite_tac[] >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `s`, `st`] >> simp[]) >>
  `mid.cs_next_var <= ready.cs_next_var` by fs[ci_mono_def] >>
  `?x. buf.buf_operand = Var x /\ not_fresh_at ready x` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qexists_tac `STRING #"%" (toString st.cs_next_var)` >>
     asm_rewrite_tac[] >> irule not_fresh_at_mono >>
     qexists_tac `mid` >> asm_rewrite_tac[] >> metis_tac[]) >>
  `window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
    (LENGTH (enc at (ListV avs))) ready u` by
    (simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >>
     simp[Abbr `u`, Abbr `raw`, eval_operand_def, lookup_var_def,
       mstore_def, write_memory_with_expansion_def] >>
     qpat_x_assum `eval_operand buf.buf_operand a = _` mp_tac >>
     asm_rewrite_tac[eval_operand_def, lookup_var_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ EVERY (not_fresh_at ready) i.inst_outputs)
    (emitted_insts st ready)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
       (irule emitted_insts_append >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [EVERY_DEF, venomInstTheory.mk_inst_def] >>
     irule not_fresh_at_mono >> qexists_tac `mid` >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `!x. ~not_fresh_at ready x ==> lookup_var x u = lookup_var x s` by
    (simp_tac bool_ss [Abbr `u`] >> metis_tac[window_seq_high_vars]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
    !i b sz. i IN R /\ FLOOKUP raw.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP raw.vs_allocas i = SOME (b,sz) ==> sz = 32` by
       (simp_tac (srw_ss()) [Abbr `raw`, mstore_def, write_memory_with_expansion_def] >>
        asm_rewrite_tac[] >> simp_tac (srw_ss()) []) >>
     qpat_assum `abi_encoder_registered_effect _ _ s raw`
       (mp_then Any mp_tac window_registered_sizes_transport) >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  qpat_x_assum `!R. _` (mk_asm "sizes") >>
  qexistsl_tac [`raw`, `slot`] >>
  `raw with vs_inst_idx := LENGTH ready.cs_current_insts = u` by simp[Abbr `u`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_x_assum `window_member_cursor _ _ _ _ _ _ _ _ _ _` mp_tac >>
      asm_rewrite_tac[]) >>
  asm "sizes" ACCEPT_TAC
QED
