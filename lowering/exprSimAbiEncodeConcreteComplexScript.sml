Theory exprSimAbiEncodeConcreteComplex
Ancestors
  valueEncodingDefs
  exprSimAbiEncodeConcreteStructuralMembers exprSimAbiEncodeConcreteWrappers
  exprSimAbiEncodeConcreteCompose exprSimAbiEncodeConcreteComplexWrappers abiEncoderWindowComplex
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers
  abiEncoderWindowContract abiEncoderWindowPhase abiEncoderWindowSequence
  abiEncoderWindowLookup abiEncoderRegisteredEffect abiEncoderProps
  abiEncoderOpenInput abiEncoderWindow abiEncoderInput contractABI
  valueEncoding valueEncodingProps emitHelperProps freshWrites exprLoweringProps
  abiDecodeRanges abiEncoderAppend fragExec venomState compileEnv list rich_list words pred_set arithmetic

Theorem abi_encode_complex_concrete_contract:
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> abi_encode_concrete_contract ei) ==>
  abi_encode_concrete_contract (AbiComplex infos)
Proof
  strip_tac >> simp_tac bool_ss [abi_encode_concrete_contract_def] >>
  rpt gen_tac >> strip_tac >>
  `abi_encoder_window_input (AbiComplex infos) at av sb cap s.vs_memory` by
    fs[abi_encoder_window_pre_def] >>
  `?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> metis_tac[]) >>
  gvs[] >> Cases_on `infos`
  >- suspend "empty" >>
  rename1 `h::rest` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) (h::rest)`
  >- suspend "dynamic" >>
  suspend "static"
QED

Resume abi_encode_complex_concrete_contract[empty]:
  gvs[Once abiEncoderTheory.compile_abi_encode_child_def, comp_return_def] >>
  `enc at (ListV avs) = []` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> strip_tac >>
     gvs[abi_encoder_tuple_type_def, enc_def, LET_THM, REV_DEF]) >>
  `s.vs_inst_idx = LENGTH en.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `s with vs_inst_idx := LENGTH en.cs_current_insts = s` by
    (qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
  qexists_tac `s` >> simp_tac bool_ss [abi_encode_concrete_result_def] >>
  simp[inst_extends_def, emitted_insts_def, run_inst_seq_def] >>
  irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, LENGTH, mem_bytes_at_def, eval_operand_def] >>
  metis_tac[window_pre_sites, window_phase_refl, abi_encoder_window_pre_def]
QED

Resume abi_encode_complex_concrete_contract[static]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,mid)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >> strip_tac >> gvs[] >>
  `~EXISTS (\(_,_,_,dyn). dyn) infos` by
    (qpat_assum `EVERY _ infos` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `window_member_cursor infos (Lit 0w) 0 0 sb cap d
      (LENGTH (enc at (ListV avs))) st s` by simp[window_member_cursor_def] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at 0 s.vs_memory = n2w (window_member_head_size infos)` by simp[] >>
  drule_all abi_encode_complex_initialized_concrete_sizes >> strip_tac >>
  qpat_x_assum `!R. _` (mk_asm "sizes") >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP r.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (asm "sizes" (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     (impl_tac >- metis_tac[window_pre_sites]) >> simp_tac bool_ss []) >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all window_complex_dynamic_layout >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    metis_tac[window_complex_structural_members, abi_encoder_structural_list_layout] >>
  `SUM (MAP2 abi_member_tail_size ats avs) = 0` by
    (`!ts vs. ~any_dynamic ts /\ LENGTH ts = LENGTH vs ==>
       SUM (MAP2 abi_member_tail_size ts vs) = 0` suffices_by metis_tac[] >>
     Induct >> Cases_on `vs` >> simp[is_dynamic_def, abi_member_tail_size_def]) >>
  `LENGTH (enc at (ListV avs)) = window_member_head_size infos` by
    (`enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
       (fs[abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
     drule abi_encoder_open_tuple_length >>
     asm_rewrite_tac[] >> simp_tac bool_ss [head_lengths_acc] >> decide_tac) >>
  `~any_dynamic ats` by metis_tac[] >>
  qexists_tac `r` >> simp_tac bool_ss [abi_encode_concrete_result_def] >>
  asm_rewrite_tac[] >> irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >>
  qpat_x_assum `window_phase _ _ _ _ _ _ _ _` mp_tac >>
  pure_asm_rewrite_tac[] >> simp_tac (srw_ss()) [UNION_EMPTY] >>
  metis_tac[]
QED

Resume abi_encode_complex_concrete_contract[dynamic]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,mid)` >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `emit_void MSTORE [buf.buf_operand; Lit (n2w (SUM (MAP (\(_,az,_,_). az) infos)))] mid` >>
  rename1 `emit_void _ _ mid = (unitval,ready)` >>
  Cases_on `unitval` >> simp_tac bool_ss [LET_THM] >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 buf.buf_operand ready` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,load)` >>
  simp_tac bool_ss [LET_THM] >>
  strip_tac >> gvs[] >>
  `ci_mono ready load` by metis_tac[ci_mono_compile_abi_encode, pairTheory.SND] >>
  `ci_mono load en` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono ready en` by
    (fs[ci_mono_def] >> irule cs_extends_trans >> qexists_tac `load` >> asm_rewrite_tac[]) >>
  `emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))] mid = ((),ready)` by
    fs[window_member_head_size_def] >>
  drule_all abi_encode_complex_initialize_concrete_sizes >> strip_tac >>
  qpat_x_assum `!R. _` (mk_asm "setup_sizes") >>
  qmatch_asmsub_abbrev_tac `window_member_cursor infos _ _ _ _ _ _ _ ready u` >>
  `abi_encoder_window_pre ctx func ready load dst src (AbiComplex infos) at
     (ListV avs) sb cap d u` by
    (qpat_assum `abi_encoder_window_pre _ _ ready en _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >> asm_rewrite_tac[] >>
     `cs_extends ready load /\ cs_extends load en /\ load.cs_next_id <= en.cs_next_id` by
       fs[ci_mono_def] >>
     (conj_tac >- metis_tac[fn_has_code_split]) >>
     rpt gen_tac >> strip_tac >>
     `inst.inst_id IN frag_ids ready en` by
       (qpat_x_assum `inst.inst_id IN frag_ids ready load` mp_tac >>
        simp_tac (srw_ss()) [NoAsms, frag_ids_def] >> decide_tac) >>
     qpat_x_assum `!inst b sz. _` drule_all >> simp_tac bool_ss []) >>
  `ready.cs_blocks = load.cs_blocks` by
    (`ready.cs_blocks = st.cs_blocks` by fs[window_seq_def] >>
     qpat_assum `ci_mono ready load` mp_tac >>
     qpat_assum `ci_mono load en` mp_tac >>
     simp_tac bool_ss [ci_mono_def, cs_extends_def] >> rpt strip_tac >>
     `?xs ys. load.cs_blocks = xs ++ ready.cs_blocks /\ ready.cs_blocks = ys ++ load.cs_blocks` by
       metis_tac[] >>
     qpat_x_assum `load.cs_blocks = _ ++ ready.cs_blocks` mp_tac >>
     qpat_x_assum `ready.cs_blocks = _ ++ load.cs_blocks` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[APPEND_ASSOC, APPEND_EQ_SELF, APPEND_eq_NIL]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==> mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)` by
    simp[Abbr `u`] >>
  drule_all abi_encode_complex_initialized_concrete_sizes >> strip_tac >>
  qpat_x_assum `!R. _` (mk_asm "member_sizes") >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func ready load _ _ u t` >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (asm "setup_sizes" (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     (impl_tac >- metis_tac[window_pre_sites]) >>
     simp_tac (srw_ss()) [Abbr `u`] >> disch_tac >>
     asm "member_sizes" (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     qpat_assum `Abbrev (t = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     pure_rewrite_tac [venom_state_accfupds, combinTheory.K_THM] >>
     asm_rewrite_tac[]) >>
  `ready.cs_next_var <= load.cs_next_var /\ ready.cs_next_id <= load.cs_next_id /\
    st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id /\
    load.cs_next_id <= en.cs_next_id` by
    (fs[ci_mono_def] >>
     `ci_mono st mid /\ ci_mono mid ready` by
       metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, pairTheory.SND] >>
     fs[ci_mono_def]) >>
  `window_member_cursor infos buf.buf_operand st.cs_next_id slot sb cap d
     (LENGTH (enc at (ListV avs))) load t` by
    (irule window_member_cursor_phase >> goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `eval_operand buf.buf_operand t = SOME (n2w slot) /\ slot < dimword (:256)` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ load t` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready load) SUBSET window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def, SUBSET_DEF, frag_ids_def] >>
     rpt strip_tac >> decide_tac) >>
  qpat_x_assum `window_phase _ _ ready load _ _ _ _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `window_phase ctx func st load (window_alloca_sites func (frag_ids st en))
     [(d,LENGTH (enc at (ListV avs)))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `ready`,
       `window_alloca_sites func (frag_ids ready load) UNION {st.cs_next_id}`,
       `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
     asm_rewrite_tac[] >> simp[EVERY_DEF, UNION_SUBSET, INSERT_SUBSET]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `~not_fresh_at load x /\ ~not_fresh_at ready x` by
       metis_tac[not_fresh_at_mono, ci_mono_def, LESS_EQ_TRANS] >> metis_tac[]) >>
  `fn_has_code load en func` by
    (`fn_has_code ready en func` by
       (qpat_assum `abi_encoder_window_pre _ _ ready en _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [abi_encoder_window_pre_def] >> metis_tac[]) >>
     `cs_extends ready load /\ cs_extends load en` by fs[ci_mono_def] >>
     metis_tac[fn_has_code_split]) >>
  `st.cs_next_var <= load.cs_next_var` by decide_tac >>
  `mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs) /\
   mem_word_at slot t.vs_memory = n2w (LENGTH (enc at (ListV avs)))` by
    (qpat_assum `Abbrev (t = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     pure_rewrite_tac [venom_state_accfupds, combinTheory.K_THM] >>
     conj_tac >- asm_rewrite_tac[] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids st en) SUBSET window_alloca_sites func (frag_ids st en)` by
    simp_tac bool_ss [SUBSET_REFL] >>
  drule_all abi_encode_complex_finish_load_concrete >> strip_tac >>
  rename1 `window_pure_seq load en t last_raw` >>
  `inst_extends st ready /\ inst_extends load en` by
    metis_tac[window_seq_def, window_pure_seq_def] >>
  `emitted_insts st load = emitted_insts st ready ++ emitted_insts ready load` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?body_raw. run_inst_seq (emitted_insts st load) s = OK body_raw /\
    (body_raw with vs_inst_idx := LENGTH load.cs_current_insts) = t` by
    (asm_rewrite_tac[] >>
     qpat_assum `Abbrev (u = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (t = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule abi_encode_run_append_normalized >>
     reverse conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`LENGTH ready.cs_current_insts`, `raw`] >>
     asm_rewrite_tac[] >> metis_tac[window_seq_def]) >>
  `emitted_insts st en = emitted_insts st load ++ emitted_insts load en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?final_raw. run_inst_seq (emitted_insts st en) s = OK final_raw /\
    (final_raw with vs_inst_idx := LENGTH en.cs_current_insts) =
    (last_raw with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >>
     reverse conj_tac
     >- (qpat_assum `window_pure_seq load en t last_raw` mp_tac >>
         simp_tac (srw_ss()) [NoAsms, window_pure_seq_def, window_seq_def, EVERY_MEM] >> metis_tac[]) >>
     qexistsl_tac [`LENGTH load.cs_current_insts`, `body_raw`] >>
     asm_rewrite_tac[] >>
     qpat_assum `window_pure_seq load en t last_raw` mp_tac >>
     simp_tac (srw_ss()) [NoAsms, window_pure_seq_def, window_seq_def, EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `final_raw` >> simp_tac bool_ss [abi_encode_concrete_result_def] >>
  asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[inst_extends_trans]) >>
  simp_tac bool_ss [EVERY_APPEND] >>
  qpat_x_assum `EVERY _ (emitted_insts ready load)` mp_tac >>
  qpat_x_assum `window_seq st ready s raw` mp_tac >>
  qpat_x_assum `window_pure_seq load en t last_raw` mp_tac >>
  simp_tac (srw_ss()) [NoAsms, window_pure_seq_def, window_seq_def, EVERY_MEM] >>
  metis_tac[]
QED
Finalise abi_encode_complex_concrete_contract
