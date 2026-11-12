(* Same-witness memory safety for complex encoder cursor phases. *)
Theory abiEncoderWindowComplexMem
Ancestors
  abiEncoderWindowComplex abiEncoderWindowMembersMem abiEncoderWindowStructuralMembers
  abiEncoderWindowMembers abiEncoderWindowContract abiEncoderWindowPhase
  abiEncoderWindow abiEncoderInput abiEncoderRegisteredEffect windowPhaseMem memContinuation
  allocaSiteResource exprLoweringProps venomMemDefs venomState finite_map pred_set
  compileEnv loweringStateRelDefs emitHelper valueEncoding valueEncodingDefs valueEncodingProps contractABI abiEncoderMembersDefs
  abiCanonicalWindows abiDecodeRanges list rich_list arithmetic words

Theorem window_complex_allocate_cursor_mem:
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
      (LENGTH (enc at (ListV avs))) mid t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[window_pre_sites] >>
  drule_all window_emit_alloca32_phase_mem >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id = SUC st.cs_next_id /\
    ?x. dp = Var x /\ not_fresh_at mid x` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >> simp[not_fresh_at_def]) >>
  `b < dimword (:256) /\ regions_disjoint (sb,cap) (b,32) /\
   regions_disjoint (d,LENGTH (enc at (ListV avs))) (b,32)` by
    metis_tac[window_complex_cursor_protected] >>
  `DISJOINT {st.cs_next_id} (window_alloca_sites func (frag_ids mid en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
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

Theorem window_complex_initialize_store_mem:
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
    mem_cont_sim ctx func s u
Proof
  strip_tac >>
  `eval_operand dp s = SOME (n2w slot) /\
   FLOOKUP s.vs_allocas site = SOME (slot,32) /\ site < st.cs_next_id /\
   slot < dimword (:256) /\ regions_disjoint (sb,cap) (slot,32)` by
    fs[window_member_cursor_def] >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    fs[abi_encoder_window_pre_def] >>
  `slot+32 <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `eval_operand (Lit (n2w (window_member_head_size infos))) s =
     SOME (n2w (window_member_head_size infos))` by simp[eval_operand_def] >>
  drule_all window_cursor_store_phase_mem >> strip_tac >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func s u` >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  `DISJOINT {site} (window_alloca_sites func (frag_ids ready en))` by
    (simp[DISJOINT_DEF, EXTENSION, window_alloca_sites_def,
      abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) sb cap u.vs_memory` by
    (irule window_alloca_growth_source >> qexistsl_tac [`{site}`, `[]`, `s`] >> simp[] >>
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

Theorem window_complex_initialize_phase_mem:
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
    mem_cont_sim ctx func s u
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
     metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `fn_has_code st mid func` mp_tac >>
     simp_tac bool_ss [fragExecTheory.fn_has_code_def] >> strip_tac >>
     gvs[IS_PREFIX_APPEND] >>
     irule fragExecTheory.lookup_block_fn_insts >>
     goal_assum (drule_at Any) >> simp[MEM_APPEND]) >>
  `fn_has_code mid en func` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans]) >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (`mid.cs_next_id = SUC st.cs_next_id` by
       (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
        simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_var_def, fresh_id_def, emit_def] >>
        rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
     `st.cs_next_id < en.cs_next_id` by
       (fs[ci_mono_def] >> decide_tac) >>
     simp[window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def]) >>
  drule_all window_complex_allocate_cursor_mem >> strip_tac >>
  drule_all window_complex_initialize_store_mem >> strip_tac >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >> conj_tac
  >- (irule window_phase_chain >>
      qexistsl_tac [`{st.cs_next_id}`, `[]`, `mid`, `{st.cs_next_id}`, `[]`, `t`] >>
      simp[] >> metis_tac[ci_mono_def]) >>
  metis_tac[mem_cont_sim_trans]
QED

Theorem window_complex_initialize_phase_sizes_mem:
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
    mem_cont_sim ctx func s u
Proof
  strip_tac >> drule_all window_complex_initialize_phase_mem >> strip_tac >>
  qexistsl_tac [`u`, `slot`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_tac >>
  `!i b sz. i IN {st.cs_next_id} /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >>
     strip_tac >> rpt gen_tac >> simp[] >> strip_tac >> gvs[]) >>
  drule window_phase_effect >> strip_tac >>
  drule window_registered_sizes_transport >>
  disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]
QED

Theorem window_complex_finish_load_mem:
  window_phase ctx func st load ids [(d,LENGTH (enc at av))] s u /\
  mem_cont_sim ctx func s u /\
  ids SUBSET window_alloca_sites func (frag_ids st en) /\
  st.cs_next_var <= load.cs_next_var /\
  mem_bytes_at d (LENGTH (enc at av)) u.vs_memory = enc at av /\
  eval_operand dp u = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= u.vs_alloca_next /\
  mem_word_at slot u.vs_memory = n2w (LENGTH (enc at av)) /\
  emit_op MLOAD [dp] load = (out,en) /\ fn_has_code load en func /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
  ?t. window_strong_result ctx func st en out at av d s t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule window_phase_control >> strip_tac >>
  drule_all window_cursor_load_phase_mem >> strip_tac >>
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
     simp_tac bool_ss [abi_encoder_registered_effect_def] >>
     simp[] >> metis_tac[]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`ids`, `[(d,LENGTH (enc at av))]`, `load`, `{}`, `[]`, `u`] >>
     asm_rewrite_tac[EVERY_DEF, EMPTY_SUBSET]) >>
  qexists_tac `t` >> conj_tac
  >- (irule window_complex_phase_result >> asm_rewrite_tac[] >>
      qpat_x_assum `mem_word_at slot _ = _` mp_tac >>
      asm_rewrite_tac[mem_word_at_eq_mload] >> disch_then SUBST1_TAC >> REFL_TAC) >>
  metis_tac[mem_cont_sim_trans]
QED

Theorem window_complex_pre_prefix[local]:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  ci_mono st mid /\ ci_mono mid en ==>
  abi_encoder_window_pre ctx func st mid dst src ei at av sb cap d s
Proof
  simp_tac bool_ss [abi_encoder_window_pre_def, ci_mono_def] >> strip_tac >>
  asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[fragExecTheory.fn_has_code_split]) >>
  rpt gen_tac >> strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `inst.inst_id IN frag_ids st mid` mp_tac >>
     simp_tac (srw_ss()) [NoAsms, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  qpat_x_assum `!inst b sz. _` drule_all >> simp_tac bool_ss []
QED

Theorem window_complex_dynamic_finish_mem[local]:
  window_phase ctx func st ready {st.cs_next_id} [] s u /\
  mem_cont_sim ctx func s u /\
  window_phase ctx func ready load
    (window_alloca_sites func (frag_ids ready load) UNION {st.cs_next_id})
    [(d,LENGTH (enc at (ListV avs)))] u t /\
  mem_cont_sim ctx func u t /\
  window_member_cursor infos dp st.cs_next_id slot sb cap d
    (LENGTH (enc at (ListV avs))) ready u /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  mem_word_at slot t.vs_memory = n2w (LENGTH (enc at (ListV avs))) /\
  mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs) /\
  ci_mono st ready /\ ci_mono ready load /\ ci_mono load en /\
  st.cs_next_id IN window_alloca_sites func (frag_ids st en) /\
  emit_op MLOAD [dp] load = (out,en) /\ fn_has_code load en func /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
  ?v. window_strong_result ctx func st en out at (ListV avs) d s v /\
      mem_cont_sim ctx func s v
Proof
  strip_tac >>
  `ready.cs_next_var <= load.cs_next_var /\ ready.cs_next_id <= load.cs_next_id /\
   st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id /\
   load.cs_next_id <= en.cs_next_id` by fs[ci_mono_def] >>
  `window_member_cursor infos dp st.cs_next_id slot sb cap d
     (LENGTH (enc at (ListV avs))) load t` by
    metis_tac[window_member_cursor_phase] >>
  `eval_operand dp t = SOME (n2w slot) /\ slot < dimword (:256) /\
   FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32)` by
    fs[window_member_cursor_def] >>
  `alloca_inv t` by metis_tac[window_phase_resources] >>
  `slot+32 <= t.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `window_alloca_sites func (frag_ids ready load) SUBSET
     window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def, SUBSET_DEF,
       abiEncoderPropsTheory.frag_ids_def] >> rpt strip_tac >> decide_tac) >>
  `window_phase ctx func st load (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc at (ListV avs)))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `ready`,
       `window_alloca_sites func (frag_ids ready load) UNION {st.cs_next_id}`,
       `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
     asm_rewrite_tac[] >> simp[EVERY_DEF, UNION_SUBSET, INSERT_SUBSET]) >>
  `mem_cont_sim ctx func s t` by metis_tac[mem_cont_sim_trans] >>
  irule window_complex_finish_load_mem >> goal_assum (drule_at Any) >>
  asm_rewrite_tac[SUBSET_REFL] >>
  qexistsl_tac [`dp`, `window_alloca_sites func (frag_ids st en)`, `load`, `slot`] >>
  asm_rewrite_tac[SUBSET_REFL] >> decide_tac
QED

Theorem window_complex_strong_contract_mem:
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==>
    !dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) ==>
  !dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src (AbiComplex infos) at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
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

Resume window_complex_strong_contract_mem[empty]:
  gvs[Once abiEncoderTheory.compile_abi_encode_child_def, comp_return_def] >>
  `enc at (ListV avs) = []` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> strip_tac >>
     gvs[abi_encoder_tuple_type_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >> simp_tac bool_ss [mem_cont_sim_refl, AND_CLAUSES] >>
  irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, LENGTH, mem_bytes_at_def, eval_operand_def] >>
  metis_tac[window_pre_sites, window_phase_refl, abi_encoder_window_pre_def]
QED

Resume window_complex_strong_contract_mem[static]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,en)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >> strip_tac >> gvs[] >>
  `~EXISTS (\(_,_,_,dyn). dyn) infos` by
    (qpat_assum `EVERY _ infos` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `window_member_cursor infos (Lit 0w) 0 0 sb cap d
      (LENGTH (enc at (ListV avs))) st s` by simp[window_member_cursor_def] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at 0 s.vs_memory = n2w (window_member_head_size infos)` by simp[] >>
  drule_all window_complex_initialized_run_mem >> strip_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (`!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by metis_tac[window_pre_sites] >>
     qpat_x_assum `!R. (!i b sz. _) ==> _`
       (qspec_then `window_alloca_sites func (frag_ids st en)` mp_tac) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `!R. (!i b sz. _) ==> _` kall_tac >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all window_complex_dynamic_layout >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    metis_tac[window_complex_structural_members, abiEncoderOpenInputTheory.abi_encoder_structural_list_layout] >>
  `SUM (MAP2 abi_member_tail_size ats avs) = 0` by
    (`!ts vs. ~any_dynamic ts /\ LENGTH ts = LENGTH vs ==>
       SUM (MAP2 abi_member_tail_size ts vs) = 0` suffices_by metis_tac[] >>
     Induct >> Cases_on `vs` >> simp[is_dynamic_def, abi_member_tail_size_def]) >>
  `LENGTH (enc at (ListV avs)) = window_member_head_size infos` by
    (`enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
       (fs[abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
     drule abiEncoderOpenInputTheory.abi_encoder_open_tuple_length >>
     asm_rewrite_tac[] >> simp_tac bool_ss [head_lengths_acc] >> decide_tac) >>
  `~any_dynamic ats` by metis_tac[] >>
  qexists_tac `t` >> asm_rewrite_tac[] >> irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >>
  qpat_x_assum `window_phase _ _ _ _ _ _ _ _` mp_tac >>
  pure_asm_rewrite_tac[] >> simp_tac (srw_ss()) [UNION_EMPTY]
QED

Resume window_complex_strong_contract_mem[dynamic]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_alloc_buffer 32 st` >>
  rename1 `compile_alloc_buffer 32 st = (buf,allocated)` >>
  Cases_on `emit_void MSTORE [buf.buf_operand; Lit (n2w (window_member_head_size infos))] allocated` >>
  rename1 `emit_void MSTORE _ allocated = (unit,ready)` >> Cases_on `unit` >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 buf.buf_operand ready` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,load)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >> strip_tac >>
  fs[LET_THM] >> gvs[pairTheory.UNCURRY_DEF] >>
  `ci_mono ready load /\ ci_mono load st'` by
    metis_tac[cj 3 ci_mono_compile_abi_encode, ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono ready st'` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  drule_all window_complex_initialize_phase_sizes_mem >> strip_tac >>
  `abi_encoder_window_pre ctx func ready load dst src (AbiComplex infos) at
     (ListV avs) sb cap d u` by metis_tac[window_complex_pre_prefix] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
     mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)` by asm_rewrite_tac[] >>
  drule_all window_complex_initialized_run_mem >> strip_tac >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (`!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
        FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32` by metis_tac[window_pre_sites] >>
     qpat_x_assum `!R. _ ==> !i b sz. _ /\ FLOOKUP u.vs_allocas i = _ ==> _`
       (qspec_then `window_alloca_sites func (frag_ids st st')` mp_tac) >>
     asm_rewrite_tac[] >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `window_alloca_sites func (frag_ids st st')` mp_tac) >>
     asm_rewrite_tac[]) >>
  rpt (qpat_x_assum `!R. (!i b sz. _) ==> _` kall_tac) >>
  `ci_mono st allocated /\ ci_mono allocated ready` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono st ready` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, LESS_EQ_TRANS]) >>
  `fn_has_code load st' func` by
    (qpat_assum `ci_mono ready load` mp_tac >>
     qpat_assum `ci_mono load st'` mp_tac >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >>
     `fn_has_code ready st' func` by metis_tac[abi_encoder_window_pre_def] >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  qpat_x_assum `window_phase _ _ ready load _ _ _ _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `mem_word_at slot t.vs_memory = n2w (LENGTH (enc at (ListV avs)))` by
    metis_tac[] >>
  drule_all window_complex_dynamic_finish_mem >> simp[]
QED
Finalise window_complex_strong_contract_mem
