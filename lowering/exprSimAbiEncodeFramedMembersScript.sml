Theory exprSimAbiEncodeFramedMembers
Ancestors
  exprSimAbiEncodeFramedArrayBody exprSimAbiEncodeFramedPhases
  exprSimAbiEncodeExecFrame abiEncoderWindowMembers abiEncoderWindowChild
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderWindow
  abiEncoderProps abiEncoderRegisteredEffect abiEncoderInput
  compileEnv emitHelper fragExec venomState venomMemDefs
  list rich_list arithmetic words finite_map pred_set freshWrites
  abiEncoderChildCode abiEncoderAppend abiEncoderAddressReach abiEncoderChildContext

Theorem abi_encode_framed_member_source_prepare:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\
  emit_op ADD [src;Lit (n2w so)] st = (child_src,ready) /\
  fn_has_code st ready func /\ fn_has_code ready en func /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id ==>
  ?t. window_phase ctx func st ready {} [] s t /\
    window_members_inv ctx func infos at ats avs k src dst dp site slot
      sb cap d ready en t /\
    eval_operand child_src t = SOME (n2w (sb+so)) /\
    (!x. child_src = Var x ==> not_fresh_at ready x) /\
    abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\ alloca_inv s /\ alloca_room ctx func s /\
   ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  `eval_operand (Lit (n2w so)) s = SOME (n2w so)` by simp[eval_operand_def] >>
  drule_all abi_encode_framed_emit_add_phase >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[window_members_inv_pure_phase]) >>
  fs[word_add_n2w]
QED

Theorem abi_encode_framed_static_child_run:
  abi_encode_framed_contract ei /\
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+ho))) src
    ei at av sb cap (d+ho) s /\
  eval_operand dst s = SOME (n2w d) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en))
        [(d+ho,LENGTH (enc at av))] s t /\
      mem_bytes_at (d+ho) (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all window_static_child_context >> strip_tac >>
  `?t. window_phase ctx func st ready {} [] s t /\
    eval_operand head t = SOME (n2w (d+ho)) /\
    (!x. head = Var x ==> not_fresh_at ready x) /\ t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame func s t` by
    (`alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
     `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all abi_encode_framed_emit_add_phase >> simp[word_add_n2w]) >>
  `abi_encoder_window_pre ctx func ready en head src ei at av sb cap (d+ho) t` by
    (irule window_static_child_pre >>
     asm_rewrite_tac[] >> qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `abi_encode_framed_contract ei` mp_tac >>
  rewrite_tac[abi_encode_framed_contract_def] >>
  disch_then drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ t u` >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  qexists_tac `u` >>
  `window_phase ctx func ready en (window_alloca_sites func (frag_ids ready en))
     [(d+ho,LENGTH (enc at av))] t u` by metis_tac[window_phase_strong_result] >>
  (conj_tac >-
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `ready`,
       `window_alloca_sites func (frag_ids ready en)`, `[(d+ho,LENGTH (enc at av))]`, `t`] >>
     asm_rewrite_tac[] >> simp[] >> irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac)) >>
  `mem_bytes_at (d+ho) (LENGTH (enc at av)) u.vs_memory = enc at av /\
   eval_operand out u = SOME (n2w (LENGTH (enc at av)))` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  Cases_on `i IN window_alloca_sites func (frag_ids ready en)`
  >- metis_tac[window_strong_result_sizes] >>
  `FLOOKUP t.vs_allocas i = SOME (b,sz)` by
    (drule window_strong_result_effect >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `window_phase _ _ st ready _ _ s t` mp_tac >>
     rewrite_tac[window_phase_def] >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Theorem abi_encode_framed_member_static_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
    LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (gvs[] >> decide_tac) >>
  drule_all window_members_inv_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d)` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all abi_encode_framed_static_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_member_prefix_static_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_member_static_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_members_inv_def] >> metis_tac[]
QED

Theorem abi_encode_framed_member_pure_word[local]:
  window_phase ctx func st en {} [] s t ==>
  mem_word_at p t.vs_memory = mem_word_at p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
     simp[] >> metis_tac[window_phase_effect]) >>
  simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes] >> asm_rewrite_tac[]
QED

Theorem abi_encode_framed_member_pure_chain[local]:
  window_phase ctx func st mid {} [] s t /\
  window_phase ctx func mid en {} [] t u /\
  st.cs_next_var <= mid.cs_next_var ==>
  window_phase ctx func st en {} [] s u
Proof
  strip_tac >> irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `mid`, `{}`, `[]`, `t`] >> simp[]
QED

Theorem abi_encode_framed_member_emit_counter[local]:
  emit_op opc operands st = (out,en) ==>
  en.cs_next_var = st.cs_next_var+1
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_encode_framed_child_prefix_run:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  fn_has_code st en func /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ mem_word_at slot s.vs_memory = n2w off /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/
         SND (SND ops) = Var x ==> not_fresh_at en x) /\
    t.vs_labels = s.vs_labels /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all window_child_prefix_context >> strip_tac >> gvs[] >>
  `st.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
   b.cs_next_var <= en.cs_next_var` by
    (imp_res_tac abi_encode_framed_member_emit_counter >> decide_tac) >>
  `?t1. window_phase ctx func st a {} [] s t1 /\
     eval_operand head t1 = SOME (n2w (d+ho)) /\
     (!x. head = Var x ==> not_fresh_at a x) /\ t1.vs_labels = s.vs_labels /\
     abi_encode_exec_frame func s t1` by
    (`eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all abi_encode_framed_emit_add_phase >> simp[word_add_n2w]) >>
  `eval_operand dp t1 = SOME (n2w slot) /\
   eval_operand dst t1 = SOME (n2w d)` by
    (conj_tac >> irule window_phase_eval >>
     qexistsl_tac [`ctx`, `a`, `func`, `{}`, `[]`, `s`, `st`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `alloca_inv t1 /\ alloca_room ctx func t1 /\ ~t1.vs_halted /\
   t1.vs_current_bb = a.cs_current_bb /\
   t1.vs_inst_idx = LENGTH a.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `mload slot t1 = n2w off` by
    metis_tac[abi_encode_framed_member_pure_word, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `?t2. window_phase ctx func a b {} [] t1 t2 /\
     eval_operand offset t2 = SOME (n2w off) /\
     (!x. offset = Var x ==> not_fresh_at b x) /\ t2.vs_labels = t1.vs_labels /\
     abi_encode_exec_frame func t1 t2` by
    (drule_all abi_encode_framed_cursor_load_phase_observed >> asm_rewrite_tac[] >> metis_tac[]) >>
  `eval_operand dst t2 = SOME (n2w d)` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `b`, `func`, `{}`, `[]`, `t1`, `a`] >>
     asm_rewrite_tac[] >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `alloca_inv t2 /\ alloca_room ctx func t2 /\ ~t2.vs_halted /\
   t2.vs_current_bb = b.cs_current_bb /\
   t2.vs_inst_idx = LENGTH b.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `?t3. window_phase ctx func b en {} [] t2 t3 /\
     eval_operand child t3 = SOME (n2w (d+off)) /\
     (!x. child = Var x ==> not_fresh_at en x) /\ t3.vs_labels = t2.vs_labels /\
     abi_encode_exec_frame func t2 t3` by
    (drule_all abi_encode_framed_emit_add_phase >> simp[word_add_n2w]) >>
  `window_phase ctx func a en {} [] t1 t3` by
    (irule abi_encode_framed_member_pure_chain >> qexistsl_tac [`b`, `t2`] >> simp[]) >>
  `eval_operand head t3 = SOME (n2w (d+ho))` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `en`, `func`, `{}`, `[]`, `t1`, `a`] >> simp[]) >>
  `eval_operand offset t3 = SOME (n2w off)` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `en`, `func`, `{}`, `[]`, `t2`, `b`] >> simp[]) >>
  `abi_encode_exec_frame func s t2` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t1` >> asm_rewrite_tac[]) >>
  `abi_encode_exec_frame func s t3` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t2` >> asm_rewrite_tac[]) >>
  qexists_tac `t3` >> asm_rewrite_tac[] >>
  (conj_tac >- (irule abi_encode_framed_member_pure_chain >>
    qexistsl_tac [`a`, `t1`] >> simp[])) >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]
QED

Theorem abi_encode_framed_member_pre_end[local]:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  mid.cs_next_id <= en.cs_next_id /\ fn_has_code st mid func ==>
  abi_encoder_window_pre ctx func st mid dst src ei at av sb cap d s
Proof
  pure_rewrite_tac [abi_encoder_window_pre_def] >> strip_tac >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids st mid` mp_tac >>
     simp_tac (srw_ss()) [frag_ids_def] >> decide_tac) >> metis_tac[]
QED

Theorem abi_encode_framed_dynamic_child_call:
  abi_encode_framed_contract ei /\
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ mem_word_at slot s.vs_memory = n2w off ==>
  ?ops ready len child_end prepared actual.
    abi_encode_child_prefix dst ho dp st = (ops,ready) /\
    compile_abi_encode_to_buf (SND (SND ops)) src ei ready = (len,child_end) /\
    abi_encode_child_suffix (FST ops) dp (FST (SND ops)) len child_end = (out,en) /\
    fn_has_code child_end en func /\
    st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= child_end.cs_next_var /\
    st.cs_next_id <= ready.cs_next_id /\ child_end.cs_next_id <= en.cs_next_id /\
    (!x. len = Var x ==> not_fresh_at child_end x) /\
    window_phase ctx func st ready {} [] s prepared /\
    eval_operand (FST ops) prepared = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) prepared = SOME (n2w off) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x ==>
         not_fresh_at ready x) /\
    window_strong_result ctx func ready child_end len at av (d+off) prepared actual /\
    eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) actual = SOME (n2w off) /\
    window_phase ctx func st child_end
      (window_alloca_sites func (frag_ids ready child_end))
      [(d+off,LENGTH (enc at av))] s actual /\
    abi_encode_exec_frame func s actual
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_framed_child_prefix_run >> strip_tac >>
  rename1 `window_phase ctx func st prepared {} [] s prep` >>
  `cs_extends child_end en` by
    (drule abi_encode_child_suffix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `cs_extends prepared child_end` by metis_tac[cs_extends_abi_encode] >>
  `cs_extends st prepared` by
    (drule abi_encode_child_prefix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `fn_has_code prepared en func` by
    metis_tac[cs_extends_trans, fn_has_code_split] >>
  `abi_encoder_window_pre ctx func prepared en (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (irule window_static_child_pre >> asm_rewrite_tac[] >> simp[] >>
     qexistsl_tac [`Lit (n2w (d+off))`, `s`, `st`] >> simp[]) >>
  `abi_encoder_window_pre ctx func prepared child_end (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (irule abi_encode_framed_member_pre_end >> asm_rewrite_tac[] >> qexists_tac `en` >> simp[]) >>
  qpat_x_assum `abi_encode_framed_contract ei` mp_tac >>
  rewrite_tac[abi_encode_framed_contract_def] >>
  disch_then drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ prep actual` >>
  `abi_encode_exec_frame func s actual` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `prep` >> asm_rewrite_tac[]) >>
  `window_phase ctx func prepared child_end
    (window_alloca_sites func (frag_ids prepared child_end))
    [(d+off,LENGTH (enc at av))] prep actual` by
    metis_tac[window_phase_strong_result] >>
  `(?x. FST ops = Var x) /\ (?x. FST (SND ops) = Var x)` by
    (drule window_child_prefix_variables >> strip_tac >> asm_rewrite_tac[] >> simp[]) >>
  `eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
   eval_operand (FST (SND ops)) actual = SOME (n2w off)` by
    metis_tac[window_phase_eval_var] >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`, `prep`, `actual`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- simp[]) >> (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
  (conj_tac >- (Cases_on `child_len` >>
    fs[not_fresh_at_def, abiDecoderReentryTheory.abi_decoder_operand_live_def,
      abiDecoderReentryTheory.abi_decoder_older_vars_def])) >>
  (conj_tac >- metis_tac[]) >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `prepared`,
    `window_alloca_sites func (frag_ids prepared child_end)`,
    `[(d+off,LENGTH (enc at av))]`, `prep`] >> simp[]
QED

Theorem abi_encode_framed_child_suffix_run:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  (h+32 <= slot \/ slot+32 <= h) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {site} [(h,32)] s t /\
    mem_word_at h t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+n) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w n) /\ abi_encode_exec_frame func s t
Proof
  strip_tac >> drule_all abi_encode_framed_child_suffix_steps >> strip_tac >>
  `window_phase ctx func a en {site} [] t1 t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `b`, `{site}`, `[]`, `t2`] >> simp[]) >>
  `window_phase ctx func st en {site} [(h,32)] s t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[(h,32)]`, `a`, `{site}`, `[]`, `t1`] >> simp[]) >>
  `mem_word_at h t2.vs_memory = n2w off` by
    (`mem_word_at h t2.vs_memory = mem_word_at h t1.vs_memory` by
       metis_tac[abi_encode_framed_member_pure_word] >>
     asm_rewrite_tac[] >> simp[valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  `mem_word_at h t3.vs_memory = n2w off /\
   mem_word_at slot t3.vs_memory = n2w (off+n)` by
    (asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
     metis_tac[valueEncodingPropsTheory.mstore_mem_word_at_disjoint,
       valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  qexists_tac `t3` >> asm_rewrite_tac[] >>
  metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated]
QED

Theorem abi_encode_framed_dynamic_child_run:
  abi_encode_framed_contract ei /\
  compile_abi_encode_child dst src ei T ho (Var cursor) st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\ not_fresh_at st cursor /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  slot < dimword (:256) /\ d+ho < dimword (:256) /\
  mem_word_at slot s.vs_memory = n2w off /\
  (d+ho+32 <= slot \/ slot+32 <= d+ho) /\
  venomMemDefs$regions_disjoint (d+off,LENGTH (enc at av)) (d+ho,32) /\
  venomMemDefs$regions_disjoint (d+off,LENGTH (enc at av)) (slot,32) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION {site})
        [(d+ho,32);(d+off,LENGTH (enc at av))] s t /\
      mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
      mem_word_at (d+ho) t.vs_memory = n2w off /\
      mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
      FLOOKUP t.vs_allocas site = SOME (slot,32) /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp[] >> metis_tac[]) >>
  drule_all abi_encode_framed_dynamic_child_call >> strip_tac >>
  `eval_operand (Var cursor) actual = SOME (n2w slot)` by
    metis_tac[window_phase_eval_var] >>
  `not_fresh_at child_end cursor` by metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
  `abi_encoder_registered_effect
      (window_alloca_sites func (frag_ids ready child_end))
      [(d+off,LENGTH (enc at av))] s actual` by metis_tac[window_phase_effect] >>
  `FLOOKUP actual.vs_allocas site = SOME (slot,32)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `alloca_inv actual /\ alloca_room ctx func actual /\ ~actual.vs_halted /\
    actual.vs_current_bb = child_end.cs_current_bb /\
    actual.vs_inst_idx = LENGTH child_end.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand len actual = SOME (n2w (LENGTH (enc at av)))` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  `!x. Var cursor = Var x \/ len = Var x ==> not_fresh_at child_end x` by
    (simp[] >> metis_tac[]) >>
  `?t. window_phase ctx func child_end en {site} [(d+ho,32)] actual t /\
    mem_word_at (d+ho) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_encode_exec_frame func actual t` by
    (irule abi_encode_framed_child_suffix_run >> asm_rewrite_tac[] >>
     qexistsl_tac [`Var cursor`, `FST ops`, `len`, `FST (SND ops)`] >> simp[] >> metis_tac[]) >>
  `abi_encode_exec_frame func s t` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `actual` >> asm_rewrite_tac[]) >>
  `window_alloca_sites func (frag_ids ready child_end) SUBSET
    window_alloca_sites func (frag_ids st en)` by
    (irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac) >>
  `window_phase ctx func st en
    (window_alloca_sites func (frag_ids st en) UNION {site})
    [(d+ho,32);(d+off,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`window_alloca_sites func (frag_ids ready child_end)`,
       `[(d+off,LENGTH (enc at av))]`, `child_end`, `{site}`, `[(d+ho,32)]`, `actual`] >>
     simp[] >> metis_tac[LESS_EQ_TRANS, SUBSET_UNION, SUBSET_TRANS]) >>
  `mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory =
    mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{site}`, `[(d+ho,32)]`] >> simp[] >>
     metis_tac[window_phase_effect, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [IN_UNION, IN_SING] >> rpt gen_tac >>
  Cases_on `i = site` >- (gvs[] >> metis_tac[]) >> strip_tac >>
  `i IN window_alloca_sites func (frag_ids st en)` by metis_tac[] >>
  `FLOOKUP actual.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `window_phase _ _ child_end en _ _ actual t` mp_tac >>
     rewrite_tac[window_phase_def] >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  Cases_on `i IN window_alloca_sites func (frag_ids ready child_end)`
  >- metis_tac[window_strong_result_sizes] >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `abi_encoder_registered_effect _ _ s actual` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Theorem abi_encode_framed_member_dynamic_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs k +
        LENGTH (enc (EL k ats) (EL k avs))) /\
      FLOOKUP t.vs_allocas site = SOME (slot,32) /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      abi_encode_exec_frame func s t
Proof
  strip_tac >>
  drule_all window_members_inv_dynamic_cursor >>
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `dp = Var _` SUBST_ALL_TAC >>
  `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  `window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by metis_tac[] >>
  drule_all window_members_inv_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d) /\
    (!x. dst = Var x ==> not_fresh_at st x)` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all abi_encode_framed_dynamic_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_member_prefix_dynamic_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_member_dynamic_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_members_inv_def] >> metis_tac[]
QED

Theorem abi_encode_framed_member_static_step_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    site NOTIN window_alloca_sites func (frag_ids st mid)) /\
  window_alloca_sites func (frag_ids st mid) SUBSET window_alloca_sites func (frag_ids st en) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid))
    (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb cap d mid en t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_members_inv_restrict_end] >>
  drule_all abi_encode_framed_member_static_run >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
   LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (drule_all window_members_inv_output_bounds >> strip_tac >>
     `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >> gvs[] >> decide_tac) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (strip_tac >>
     `site NOTIN window_alloca_sites func (frag_ids st mid)` by metis_tac[] >>
     `d <= d+SUM (MAP abi_member_head_size (TAKE k ats)) /\
      (d+SUM (MAP abi_member_head_size (TAKE k ats))) +
        LENGTH (enc (EL k ats) (EL k avs)) <= d+LENGTH (enc at (ListV avs))` by decide_tac >>
     `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
       (drule_all window_member_static_cursor_frame >> simp[]) >>
     `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
     `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
       fs[window_members_inv_def, window_member_prefix_def] >>
     drule_all window_member_tail_step >> fs[window_members_inv_def]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),
       LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  simp[] >> metis_tac[SUBSET_UNION, SUBSET_TRANS]
QED

Theorem abi_encode_framed_member_dynamic_step_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ abi_encode_framed_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (window_alloca_sites func (frag_ids st mid) UNION {site}) SUBSET
    (window_alloca_sites func (frag_ids st en) UNION {site}) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
    (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid) UNION {site})
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb cap d mid en t /\ abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_members_inv_restrict_end] >>
  drule_all abi_encode_framed_member_dynamic_run >> strip_tac >>
  drule_all window_members_inv_output_bounds >> strip_tac >>
  drule_all window_members_inv_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
    (qpat_assum `window_member_prefix _ _ _ (SUC k) _ _` mp_tac >>
     simp_tac bool_ss [window_member_prefix_def] >> strip_tac >> decide_tac) >>
  `mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (drule_all window_member_tail_step >> disch_then (qspec_then `infos` mp_tac) >>
     asm_rewrite_tac[] >> disch_then SUBST1_TAC >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid) UNION {site}`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [NoAsms, listTheory.EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED

Theorem abi_encode_framed_member_drop_cons[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem abi_encode_framed_member_envelope_frame[local]:
  EVERY (\(b,n). d <= b /\ b+n <= d+len) outs ==>
  !a. EVERY (\(b,n). a < b \/ b+n <= a) [(d,len)] ==>
      EVERY (\(b,n). a < b \/ b+n <= a) outs
Proof
  simp_tac (srw_ss()) [EVERY_MEM] >> strip_tac >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  Cases_on `r` >> first_x_assum drule >> simp[] >> decide_tac
QED

Theorem abi_encode_framed_members_cons_run:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ DROP k infos = (h0,h1,h2,h3)::rest /\
  abi_encode_framed_contract h0 /\
  compile_abi_encode_complex_elems dst src ((h0,h1,h2,h3)::rest)
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?mid u. window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en u /\ DROP (SUC k) infos = rest /\
    compile_abi_encode_complex_elems dst src rest
      (abi_encoder_member_span (TAKE (SUC k) infos))
      (SUM (MAP abi_member_head_size (TAKE (SUC k) ats))) dp mid = (out,en) /\
    window_phase ctx func st mid
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s u /\
    st.cs_next_var <= mid.cs_next_var /\
    window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en) /\
    abi_encode_exec_frame func s u
Proof
  strip_tac >>
  `fn_has_code st en func` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all window_members_cons_context >> strip_tac >>
  `cs_extends ready mid /\ cs_extends mid en` by
    metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode_child,
      cj 3 abiEncoderAppendTheory.cs_appends_abi_encode_mutual, fragExecTheory.cs_appends_def] >>
  `cs_extends st ready` by metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `fn_has_code ready en func` by metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  drule_all abi_encode_framed_member_source_prepare >> strip_tac >>
  `k < LENGTH infos /\ EL k infos = (h0,h1,h2,h3) /\ DROP (SUC k) infos = rest` by
    metis_tac[abi_encode_framed_member_drop_cons] >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _` kall_tac >>
  `abi_encoder_admissible h0` by
    (`abi_encoder_admissible (AbiComplex infos)` by
       (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
     qpat_x_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     simp_tac bool_ss [abiEncoderAdmissibleTheory.abi_encoder_admissible_def,
       abiEncoderAdmissibleTheory.abi_encoder_members_admissible_every] >>
     simp_tac (srw_ss()) [EVERY_MEM] >>
     disch_then (qspec_then `(h0,h1,h2,h3)` mp_tac) >> simp[] >> metis_tac[MEM_EL]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==> site < ready.cs_next_id` by
    (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, window_member_cursor_def] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready mid) SUBSET window_alloca_sites func (frag_ids ready en) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid)) (window_alloca_sites func (frag_ids mid en)) /\
   (EXISTS (\(_,_,_,dyn). dyn) infos ==>
     site NOTIN window_alloca_sites func (frag_ids ready mid) /\
     DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
       (window_alloca_sites func (frag_ids mid en)))` by
    metis_tac[window_member_site_split] >>
  qpat_x_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` kall_tac >>
  qpat_x_assum `cs_extends ready mid` kall_tac >>
  qpat_x_assum `cs_extends mid en` kall_tac >>
  qpat_x_assum `cs_extends st ready` kall_tac >>
  `?u ids outs. window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en u /\ window_phase ctx func ready mid ids outs t u /\
    ids SUBSET (window_alloca_sites func (frag_ids ready en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
    EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs /\
    abi_encode_exec_frame func t u` by
    (reverse (Cases_on `h3`)
     >- (`EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids ready mid)` by metis_tac[] >>
          drule_all abi_encode_framed_member_static_step_run >> strip_tac >>
          qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid)`,
            `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`] >>
          asm_rewrite_tac[] >>
          (conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS]) >>
          drule_all window_members_inv_output_bounds >> strip_tac >>
          drule_all window_members_inv_total_bounds >> strip_tac >>
          `~is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
          simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
          qpat_x_assum `~is_dynamic _ ==> _` drule >> decide_tac) >>
     `EXISTS (\(_,_,_,dyn). dyn) infos` by
       (simp[EXISTS_MEM] >> qexists_tac `(h0,h1,h2,T)` >> simp[] >> metis_tac[MEM_EL]) >>
     `(window_alloca_sites func (frag_ids ready mid) UNION {site}) SUBSET
        (window_alloca_sites func (frag_ids ready en) UNION {site}) /\
      DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
        (window_alloca_sites func (frag_ids mid en))` by
       metis_tac[SUBSET_UNION, SUBSET_TRANS, pred_setTheory.UNION_SUBSET] >>
     drule_all abi_encode_framed_member_dynamic_step_run >> strip_tac >>
     qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid) UNION {site}`,
       `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`] >>
     asm_rewrite_tac[] >>
     drule_all window_members_inv_output_bounds >> strip_tac >>
     drule_all window_members_inv_total_bounds >> strip_tac >>
     `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
     qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac) >>
  `abi_encode_exec_frame func s u` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  `h1 = abi_member_head_size (EL k ats) /\ k < LENGTH ats` by
    (drule_all window_members_inv_source >> strip_tac >>
     qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def, window_member_prefix_def] >> metis_tac[]) >>
  `abi_encoder_member_span (TAKE (SUC k) infos) = abi_encoder_member_span (TAKE k infos) + h2 /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + h1` by
    simp[TAKE_SUC, TAKE1_DROP, abiEncoderInputTheory.abi_encoder_member_span_def,
      MAP_APPEND, SUM_APPEND] >>
  `window_alloca_sites func (frag_ids ready en) SUBSET window_alloca_sites func (frag_ids st en) /\
   window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def,
       SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`mid`, `u`] >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[]) >>
  reverse conj_tac >- decide_tac >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `ready`, `ids`, `outs`, `t`] >>
  simp_tac (srw_ss()) [NoAsms, EMPTY_SUBSET, EVERY_DEF] >>
  asm_rewrite_tac[] >>
  (conj_tac >-
    (drule abi_encode_framed_member_envelope_frame >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF])) >>
  qpat_x_assum `ids SUBSET _` mp_tac >>
  qpat_x_assum `window_alloca_sites func (frag_ids ready en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED
