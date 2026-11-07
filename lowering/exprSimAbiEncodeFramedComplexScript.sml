Theory exprSimAbiEncodeFramedComplex
Ancestors
  exprSimAbiEncodeFramedStructuralMembers exprSimAbiEncodeFramedPhases
  exprSimAbiEncodeExecFrame abiEncoderWindowComplex abiEncoderWindowMembers
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderWindow
  abiEncoderRegisteredEffect abiEncoderInput abiEncoderProps valueEncodingProps
  exprLoweringProps abiEncoderWindowStructuralMembers
  compileEnv emitHelper fragExec venomState venomMemDefs
  list rich_list arithmetic words finite_map pred_set

Theorem abi_encode_framed_complex_finish_load:
  window_phase ctx func st load ids [(d,LENGTH (enc at av))] s u /\
  ids SUBSET window_alloca_sites func (frag_ids st en) /\
  st.cs_next_var <= load.cs_next_var /\
  mem_bytes_at d (LENGTH (enc at av)) u.vs_memory = enc at av /\
  eval_operand dp u = SOME (n2w slot) /\ slot < dimword (:256) /\
  mem_word_at slot u.vs_memory = n2w (LENGTH (enc at av)) /\
  emit_op MLOAD [dp] load = (out,en) /\ fn_has_code load en func /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
  abi_encode_exec_frame func s u ==>
  ?t. window_strong_result ctx func st en out at av d s t /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule_all abi_encode_framed_cursor_load_phase_observed >> strip_tac >>
  `abi_encoder_registered_effect {} [] u t` by metis_tac[window_phase_effect] >>
  `mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av` by
    (irule EQ_TRANS >> qexists_tac `mem_bytes_at d (LENGTH (enc at av)) u.vs_memory` >>
     conj_tac
     >- (irule abi_encoder_window_effect_bytes >>
         qexistsl_tac [`{}`, `[]`] >> simp[]) >>
     asm_rewrite_tac[]) >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_x_assum `abi_encoder_registered_effect {} [] u t` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> simp[] >> metis_tac[]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc at av))]`, `load`, `{}`, `[]`, `u`] >>
     asm_rewrite_tac[EVERY_DEF, EMPTY_SUBSET]) >>
  qexists_tac `t` >> reverse conj_tac
  >- (irule abi_encode_exec_frame_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  irule window_complex_phase_result >> asm_rewrite_tac[] >>
  qpat_x_assum `mem_word_at slot _ = _` mp_tac >>
  asm_rewrite_tac[mem_word_at_eq_mload] >> disch_then SUBST1_TAC >> REFL_TAC
QED

Theorem abi_encode_framed_complex_emit_alloca_shape[local]:
  emit_op ALLOCA [Lit 32w] st = (dp,mid) ==>
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id = SUC st.cs_next_id /\
  ?x. dp = Var x /\ not_fresh_at mid x
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[not_fresh_at_def]
QED

Theorem abi_encode_framed_complex_allocate_cursor:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  emit_op ALLOCA [Lit 32w] st = (dp,mid) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) ==>
  ?t slot. window_phase ctx func st mid {st.cs_next_id} [] s t /\
    abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
      (ListV avs) sb cap d t /\
    window_member_cursor infos dp st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) mid t /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[window_pre_sites] >>
  drule_all abi_encode_framed_alloca32_phase_observed >> strip_tac >>
  drule abi_encode_framed_complex_emit_alloca_shape >> strip_tac >>
  `b < dimword (:256) /\ regions_disjoint (sb,cap) (b,32) /\
   regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,32)` by
    metis_tac[window_complex_cursor_protected] >>
  `DISJOINT {st.cs_next_id} (window_alloca_sites func (frag_ids mid en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def, frag_ids_def] >> decide_tac) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func mid en dst src (AbiComplex infos) at
     (ListV avs) sb cap d t` by
    (irule window_member_remaining_pre >> asm_rewrite_tac[] >>
     (conj_tac >- fs[abi_encoder_window_pre_def]) >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `s`, `st`] >> simp[]) >>
  qexistsl_tac [`t`, `b`] >> asm_rewrite_tac[] >>
  simp[window_member_cursor_def] >> metis_tac[]
QED

Theorem abi_encode_framed_complex_initialize_store:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  window_member_cursor infos dp site slot sb cap d
    (LENGTH (enc at (ListV avs))) st s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  emit_void MSTORE [dp; Lit (n2w (window_member_head_size infos))] st = ((),ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func ==>
  ?u. window_phase ctx func st ready {site} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos dp site slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    abi_encode_exec_frame func s u
Proof
  strip_tac >>
  `eval_operand dp s = SOME (n2w slot) /\
   FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site < st.cs_next_id /\
   slot < dimword (:256) /\ regions_disjoint (sb,cap) (slot,32)` by
    fs[window_member_cursor_def] >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `eval_operand (Lit (n2w (window_member_head_size infos))) s =
     SOME (n2w (window_member_head_size infos))` by simp[eval_operand_def] >>
  drule_all abi_encode_framed_cursor_store_phase_observed >> strip_tac >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func st ready {site} [] s u` >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  `DISJOINT {site} (window_alloca_sites func (frag_ids ready en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def, frag_ids_def] >> decide_tac) >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap u.vs_memory` by
    (irule window_alloca_growth_source >> qexistsl_tac [`{site}`, `[]`, `s`] >>
     simp[] >>
     `abi_encoder_registered_effect {site} [] s u /\ window_alloca_growth s u` by
       metis_tac[window_phase_effect, window_phase_resources] >>
     asm_rewrite_tac[] >> fs[abi_encoder_window_pre_def]) >>
  `eval_operand src u = SOME (n2w sb) /\ eval_operand dst u = SOME (n2w d)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[window_phase_operand]) >>
  `abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
     (ListV avs) sb cap d u` by
    (irule window_member_remaining_pre >> asm_rewrite_tac[] >>
     qexistsl_tac [`{site}`, `[]`, `s`, `st`] >> simp[]) >>
  qexists_tac `u` >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_member_cursor_phase >>
      qexistsl_tac [`ctx`, `func`, `{site}`, `[]`, `s`, `st`] >> simp[]) >>
  simp[Abbr `u`, mstore_mem_word_at_same]
QED

Theorem abi_encode_framed_complex_initialize_phase_sizes:
  abi_encoder_window_pre ctx func st en dst src (AbiComplex infos) at
    (ListV avs) sb cap d s /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  compile_alloc_buffer 32 st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))]
    mid = ((),ready) /\ ci_mono ready en ==>
  ?u slot. window_phase ctx func st ready {st.cs_next_id} [] s u /\
    abi_encoder_window_pre ctx func ready en dst src (AbiComplex infos) at
      (ListV avs) sb cap d u /\
    window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
      (LENGTH (enc at (ListV avs))) ready u /\
    mem_word_at slot u.vs_memory = n2w (window_member_head_size infos) /\
    st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    abi_encode_exec_frame func s u
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
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `fn_has_code st mid func` mp_tac >>
     simp_tac bool_ss [fn_has_code_def] >> strip_tac >> gvs[IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  `fn_has_code mid en func` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (drule abi_encode_framed_complex_emit_alloca_shape >> strip_tac >>
     `st.cs_next_id < en.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
     simp[window_alloca_sites_def, frag_ids_def] >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
  drule_all abi_encode_framed_complex_allocate_cursor >> strip_tac >>
  drule_all abi_encode_framed_complex_initialize_store >> strip_tac >>
  `window_phase ctx func st ready {st.cs_next_id} [] s u` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >>
     simp[] >> metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND]) >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >>
     strip_tac >> rpt gen_tac >> simp[] >> strip_tac >> gvs[]) >>
  qpat_assum `window_phase _ _ st ready _ _ s u` (mp_tac o MATCH_MP window_phase_effect) >> strip_tac >>
  drule window_registered_sizes_transport >>
  disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]
QED
