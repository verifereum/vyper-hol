Theory externalReturnZeroChild
Ancestors
  externalReturnZeroContract abiEncoderWindowChild abiEncoderWindowPhase
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderProps
  abiEncoderWindowStructuralMembers abiEncoderWindowMembers
  abiEncoderChildContext abiEncoderChildCode abiEncoderCounters abiEncoderAppend
  abiDecoderReentry abiEncoderExtendSim fragExec
  freshWrites compileEnv venomState words list finite_map pred_set

Theorem zero_static_child_run:
  zero_strong_contract ei /\
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+ho))) (Lit 0w)
    ei at av 0 0 (d+ho) s /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  eval_operand dst s = SOME (n2w d) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en))
        [(d+ho,LENGTH (enc at av))] s t /\
      mem_bytes_at (d+ho) (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all window_static_child_context >> strip_tac >>
  `?t. window_phase ctx func st ready {} [] s t /\
    eval_operand head t = SOME (n2w (d+ho)) /\
    (!x. head = Var x ==> not_fresh_at ready x) /\ t.vs_labels = s.vs_labels` by
    (`alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
     `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all window_emit_add_phase >> simp[word_add_n2w]) >>
  `abi_encoder_window_pre ctx func ready en head (Lit 0w) ei at av 0 0 (d+ho) t` by
    (irule window_static_child_pre >>
     asm_rewrite_tac[] >> qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >>
     asm_rewrite_tac[]) >>
  `zero_window_pre ctx func ready en head src ei at av sb (d+ho) t` by
    (irule zero_window_pre_actual >> asm_rewrite_tac[] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     irule window_phase_eval >>
     qexistsl_tac [`ctx`, `ready`, `func`, `{}`, `[]`, `s`, `st`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `zero_strong_contract ei` mp_tac >>
  rewrite_tac[zero_strong_contract_def] >> disch_then drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ t u` >>
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
    (qpat_assum `window_phase _ _ st ready _ _ s t`
       (mp_tac o MATCH_MP window_phase_effect) >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Theorem zero_member_child_pre:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,dyn) /\ abi_encoder_admissible ei /\
  off + LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs)) ==>
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) (Lit 0w)
    ei (EL k ats) (EL k avs) 0 0 (d+off) s
Proof
  simp_tac bool_ss [zero_members_inv_def] >> strip_tac >>
  drule_all window_structural_members_inv_source >> strip_tac >>
  `abi_encoder_member_span (TAKE k infos) = 0 /\ child_cap = 0` by decide_tac >>
  irule (SRULE [] (Q.INST [`sb` |-> `0`, `so` |-> `0`] window_member_subwindow_pre)) >>
  simp[eval_operand_def] >>
  (conj_tac >- metis_tac[arithmeticTheory.ADD_CLAUSES]) >>
  qexistsl_tac [`at`, `avs`, `0`, `dst`, `infos`, `Lit 0w`] >>
  fs[window_structural_members_inv_def]
QED

Theorem zero_member_static_run:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ zero_strong_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w child_sb) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      window_member_prefix infos ats avs (SUC k) d t.vs_memory /\
      eval_operand out t = SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d st en s` by fs[zero_members_inv_def] >>
  `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) +
    LENGTH (enc (EL k ats) (EL k avs)) <= LENGTH (enc at (ListV avs))` by
    (gvs[] >> decide_tac) >>
  drule_all zero_member_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d)` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >>
     metis_tac[]) >>
  drule_all zero_static_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_structural_member_prefix_static_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_structural_member_static_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  fs[window_structural_members_inv_def]
QED

Theorem zero_members_inv_restrict_end:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot sb d st en s /\
  fn_has_code st mid func /\ mid.cs_next_id <= en.cs_next_id ==>
  zero_members_inv ctx func infos at ats avs k src dst dp site slot sb d st mid s
Proof
  simp_tac bool_ss [zero_members_inv_def] >> strip_tac >>
  asm_rewrite_tac[] >> metis_tac[window_structural_members_inv_restrict_end]
QED

Theorem zero_members_inv_phase_actual:
  window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d mid en t /\
  zero_members_inv ctx func infos at ats avs j src dst dp site slot sb d st old s /\
  window_phase ctx func st mid ids outs s t /\ st.cs_next_var <= mid.cs_next_var ==>
  zero_members_inv ctx func infos at ats avs k src dst dp site slot sb d mid en t
Proof
  simp_tac bool_ss [zero_members_inv_def] >> strip_tac >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule window_phase_eval >>
      qexistsl_tac [`ctx`, `mid`, `func`, `ids`, `outs`, `s`, `st`] >>
      asm_rewrite_tac[] >> fs[window_phase_def]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem zero_member_static_step_run_sizes:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot sb d st en s /\
  k < LENGTH infos /\ EL k infos = (ei,az,ms,F) /\
  abi_encoder_admissible ei /\ zero_strong_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w child_sb) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids st mid)) /\
  window_alloca_sites func (frag_ids st mid) SUBSET window_alloca_sites func (frag_ids st en) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid)) (window_alloca_sites func (frag_ids mid en)) ==>
  ?t. window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid))
        [(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))] s t /\
      zero_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot sb d mid en t /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `zero_members_inv ctx func infos at ats avs k src dst dp site slot sb d st mid s` by
    metis_tac[zero_members_inv_restrict_end] >>
  drule_all zero_member_static_run >> strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d st en s` by fs[zero_members_inv_def] >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  `SUM (MAP abi_member_head_size (TAKE k ats)) + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by
    (qpat_x_assum `~is_dynamic _ ==> _`
       (fn th => qpat_assum `~is_dynamic _` (mp_tac o MATCH_MP th)) >>
     qpat_x_assum `window_member_head_size _ <= _` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (strip_tac >>
     `site NOTIN window_alloca_sites func (frag_ids st mid)` by metis_tac[] >>
     `d <= d+SUM (MAP abi_member_head_size (TAKE k ats)) /\
      (d+SUM (MAP abi_member_head_size (TAKE k ats))) + LENGTH (enc (EL k ats) (EL k avs)) <=
        d+LENGTH (enc at (ListV avs))` by decide_tac >>
     `mem_word_at slot t.vs_memory = mem_word_at slot s.vs_memory` by
       (drule_all window_structural_member_static_cursor_frame >> simp[]) >>
     `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
       (qpat_assum `window_member_prefix _ _ _ (SUC k) _ _` mp_tac >>
        simp_tac bool_ss [window_member_prefix_def] >> strip_tac >> decide_tac) >>
     `mem_word_at slot s.vs_memory = n2w (window_member_tail infos ats avs k)` by
       (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` mp_tac >>
        simp_tac bool_ss [window_structural_members_inv_def] >> metis_tac[]) >>
     drule_all window_member_tail_step >> simp[]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >> drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >> disch_then (qspec_then `R` mp_tac) >>
     asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_x_assum `!R. _` kall_tac >>
  irule zero_members_inv_phase_actual >> asm_rewrite_tac[] >>
  (conj_tac >-
    (qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`, `k`, `en`,
      `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`,
      `s`, `st`] >> asm_rewrite_tac[])) >>
  irule window_structural_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`,
    `s`, `st`] >> simp[] >> metis_tac[SUBSET_UNION, SUBSET_TRANS]
QED

Theorem zero_child_pre_end[local]:
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

Theorem zero_dynamic_child_call:
  zero_strong_contract ei /\
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) (Lit 0w)
    ei at av 0 0 (d+off) s /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
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
    (!x. FST ops = Var x \/ FST (SND ops) = Var x ==> not_fresh_at ready x) /\
    window_strong_result ctx func ready child_end len at av (d+off) prepared actual /\
    eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) actual = SOME (n2w off) /\
    window_phase ctx func st child_end
      (window_alloca_sites func (frag_ids ready child_end))
      [(d+off,LENGTH (enc at av))] s actual
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all window_child_prefix_run >> strip_tac >>
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
  `abi_encoder_window_pre ctx func prepared en (SND (SND ops)) (Lit 0w)
    ei at av 0 0 (d+off) prep` by
    (irule window_static_child_pre >> asm_rewrite_tac[] >> simp[] >>
     qexistsl_tac [`Lit (n2w (d+off))`, `s`, `st`] >> simp[]) >>
  `abi_encoder_window_pre ctx func prepared child_end (SND (SND ops)) (Lit 0w)
    ei at av 0 0 (d+off) prep` by
    (irule zero_child_pre_end >> asm_rewrite_tac[] >> qexists_tac `en` >> simp[]) >>
  `zero_window_pre ctx func prepared child_end (SND (SND ops)) src
    ei at av sb (d+off) prep` by
    (irule zero_window_pre_actual >> asm_rewrite_tac[] >>
     conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
     irule window_phase_eval >>
     qexistsl_tac [`ctx`, `prepared`, `func`, `{}`, `[]`, `s`, `st`] >> simp[]) >>
  qpat_x_assum `zero_strong_contract ei` mp_tac >>
  rewrite_tac[zero_strong_contract_def] >> disch_then drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ prep actual` >>
  `window_phase ctx func prepared child_end
    (window_alloca_sites func (frag_ids prepared child_end))
    [(d+off,LENGTH (enc at av))] prep actual` by metis_tac[window_phase_strong_result] >>
  `(?x. FST ops = Var x) /\ (?x. FST (SND ops) = Var x)` by
    (drule window_child_prefix_variables >> strip_tac >> asm_rewrite_tac[] >> simp[]) >>
  `eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
   eval_operand (FST (SND ops)) actual = SOME (n2w off)` by
    metis_tac[window_phase_eval_var] >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`, `prep`, `actual`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- simp[]) >> (conj_tac >- simp[]) >> (conj_tac >- simp[]) >>
  (conj_tac >- (Cases_on `child_len` >>
    fs[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def])) >>
  (conj_tac >- metis_tac[]) >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `prepared`,
    `window_alloca_sites func (frag_ids prepared child_end)`,
    `[(d+off,LENGTH (enc at av))]`, `prep`] >> simp[]
QED

Theorem zero_dynamic_child_run:
  zero_strong_contract ei /\
  compile_abi_encode_child dst src ei T ho (Var cursor) st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) (Lit 0w)
    ei at av 0 0 (d+off) s /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
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
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp[] >> metis_tac[]) >>
  drule_all zero_dynamic_child_call >> strip_tac >>
  `eval_operand (Var cursor) actual = SOME (n2w slot)` by
    metis_tac[window_phase_eval_var] >>
  `not_fresh_at child_end cursor` by metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `abi_encoder_registered_effect
      (window_alloca_sites func (frag_ids ready child_end))
      [(d+off,LENGTH (enc at av))] s actual` by metis_tac[window_phase_effect] >>
  `FLOOKUP actual.vs_allocas site = SOME (slot,32)` by
    metis_tac[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated] >>
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
    eval_operand out t = SOME (n2w (LENGTH (enc at av)))` by
    (irule window_child_suffix_run >> asm_rewrite_tac[] >>
     qexistsl_tac [`Var cursor`, `FST ops`, `len`, `FST (SND ops)`] >> simp[] >> metis_tac[]) >>
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
     simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, SUBSET_UNION, SUBSET_TRANS]) >>
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
    (qpat_assum `window_phase _ _ child_end en _ _ actual t`
       (mp_tac o MATCH_MP window_phase_effect) >>
     simp_tac (srw_ss()) [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  Cases_on `i IN window_alloca_sites func (frag_ids ready child_end)`
  >- metis_tac[window_strong_result_sizes] >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `abi_encoder_registered_effect _ _ s actual` mp_tac >>
     simp_tac bool_ss [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Theorem zero_member_dynamic_run:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ zero_strong_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  eval_operand child_src s = SOME (n2w child_sb) /\
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
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d st en s` by fs[zero_members_inv_def] >>
  drule_all window_structural_members_inv_dynamic_cursor >>
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qpat_x_assum `dp = Var _` SUBST_ALL_TAC >>
  `is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  `window_member_tail infos ats avs k + LENGTH (enc (EL k ats) (EL k avs)) <=
    LENGTH (enc at (ListV avs))` by metis_tac[] >>
  drule_all zero_member_child_pre >> strip_tac >>
  `eval_operand dst s = SOME (n2w d) /\ (!x. dst = Var x ==> not_fresh_at st x)` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all zero_dynamic_child_run >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule window_structural_member_prefix_dynamic_step >> asm_rewrite_tac[] >>
  `window_member_prefix infos ats avs k d t.vs_memory` by
    (irule window_structural_member_dynamic_prefix_frame >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [window_structural_members_inv_def] >> metis_tac[]
QED

Theorem zero_member_dynamic_step_run_sizes:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ zero_strong_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  eval_operand child_src s = SOME (n2w child_sb) /\
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
      zero_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
        sb d mid en t /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st mid s` by metis_tac[zero_members_inv_restrict_end] >>
  drule_all zero_member_dynamic_run >> strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d st en s` by
    (qpat_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` mp_tac >>
     simp_tac bool_ss [zero_members_inv_def] >> metis_tac[]) >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(ei,az,ms,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `LENGTH ats = LENGTH avs /\ k < LENGTH ats` by
    (qpat_assum `window_member_prefix _ _ _ (SUC k) _ _` mp_tac >>
     simp_tac bool_ss [window_member_prefix_def] >> strip_tac >> decide_tac) >>
  `mem_word_at slot t.vs_memory = n2w (window_member_tail infos ats avs (SUC k))` by
    (drule_all window_member_tail_step >> disch_then (qspec_then `infos` mp_tac) >>
     asm_rewrite_tac[] >> disch_then SUBST1_TAC >> asm_rewrite_tac[]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >> drule window_phase_effect >> strip_tac >>
     drule window_registered_sizes_transport >>
     disch_then (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_x_assum `!R. _` kall_tac >>
  irule zero_members_inv_phase_actual >> asm_rewrite_tac[] >>
  (conj_tac >-
    (qexistsl_tac [`window_alloca_sites func (frag_ids st mid) UNION {site}`, `k`, `en`,
      `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
        (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`,
      `s`, `st`] >> asm_rewrite_tac[])) >>
  irule window_structural_members_inv_phase_advance >> asm_rewrite_tac[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st mid) UNION {site}`, `k`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, listTheory.EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED
