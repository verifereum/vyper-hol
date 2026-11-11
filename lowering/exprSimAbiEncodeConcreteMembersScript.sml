Theory exprSimAbiEncodeConcreteMembers
Ancestors
  exprSimAbiEncodeConcreteWrappers exprSimAbiEncodeConcreteDynamic
  exprSimAbiEncodeNoBlockStructure exprSimAbiEncodeConcreteCompose
  rich_list emitHelperProps freshWrites
  abiEncoderWindowMembers abiEncoderWindowChild abiEncoderWindowPhase
  abiEncoderWindowContract abiEncoderWindowSequence abiEncoderWindowLookup
  abiEncoderRegisteredEffect abiEncoderProps abiEncoderInputFrame
  abiEncoderAddressReach abiEncoderChildContext abiEncoderAppend
  exprLoweringProps fragExec venomState list words pred_set arithmetic compileEnv

Theorem abi_encode_static_child_phase[local]:
  abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+ho))) src
    ei at av sb cap (d+ho) s /\
  st.cs_blocks = en.cs_blocks /\ eval_operand dst s = SOME (n2w d) ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d+ho,LENGTH (enc at av))] s (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    mem_bytes_at (d+ho) (LENGTH (enc at av)) r.vs_memory = enc at av /\
    eval_operand out (r with vs_inst_idx := LENGTH en.cs_current_insts) = SOME (n2w (LENGTH (enc at av))) /\
    (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP r.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >> drule_all abi_encode_static_child_concrete >> strip_tac >>
  qabbrev_tac `prep = raw with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `fn_has_code st en func` by
    (qpat_assum `abi_encoder_window_pre _ _ st en _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> metis_tac[]) >>
  `fn_has_code st ready func` by
    (drule_all window_static_child_context >> strip_tac >> gvs[]) >>
  `window_phase ctx func st ready {} [] s prep` by
    (simp_tac bool_ss [Abbr `prep`] >> irule window_pure_seq_phase >>
     qpat_assum `abi_encoder_window_pre _ _ st en _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> metis_tac[]) >>
  `window_phase ctx func ready en (window_alloca_sites func (frag_ids ready en))
    [(d+ho,LENGTH (enc at av))] prep t` by metis_tac[window_phase_strong_result] >>
  `st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= en.cs_next_id /\
   st.cs_next_var <= ready.cs_next_var` by
    (drule_all window_static_child_context >> strip_tac >> gvs[]) >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d+ho,LENGTH (enc at av))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `ready`,
       `window_alloca_sites func (frag_ids ready en)`, `[(d+ho,LENGTH (enc at av))]`, `prep`] >>
     asm_rewrite_tac[] >> simp[] >> irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac) >>
  `mem_bytes_at (d+ho) (LENGTH (enc at av)) t.vs_memory = enc at av /\
   eval_operand out t = SOME (n2w (LENGTH (enc at av)))` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  `!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (rpt strip_tac >> Cases_on `i IN window_alloca_sites func (frag_ids ready en)`
     >- metis_tac[window_strong_result_sizes] >>
     `FLOOKUP prep.vs_allocas i = SOME (b,sz)` by
       (drule window_strong_result_effect >>
        simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]) >>
     `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
       (qpat_assum `window_phase _ _ st ready _ _ s prep`
          (mp_tac o MATCH_MP window_phase_effect) >>
        simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
     metis_tac[window_pre_sites]) >>
  qexists_tac `r` >> fs[Abbr `t`] >> metis_tac[]
QED

Theorem abi_encode_member_static_concrete:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  st.cs_blocks = en.cs_blocks /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
        LENGTH (enc (EL k ats) (EL k avs)))] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    window_member_prefix infos ats avs (SUC k) d r.vs_memory /\
    eval_operand out (r with vs_inst_idx := LENGTH en.cs_current_insts) =
      SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
    (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP r.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
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
     simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >>
     metis_tac[]) >>
  drule_all abi_encode_static_child_phase >> strip_tac >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `mem_bytes_at (d+SUM (MAP abi_member_head_size (TAKE k ats)))
    (LENGTH (enc (EL k ats) (EL k avs))) t.vs_memory = enc (EL k ats) (EL k avs)` by
    fs[Abbr `t`] >>
  `window_member_prefix infos ats avs (SUC k) d t.vs_memory` by
    (irule window_member_prefix_static_step >> asm_rewrite_tac[] >>
     `window_member_prefix infos ats avs k d t.vs_memory` by
       (irule window_member_static_prefix_frame >> metis_tac[]) >>
     asm_rewrite_tac[] >>
     qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def] >> metis_tac[]) >>
  qexists_tac `r` >> fs[Abbr `t`] >> metis_tac[]
QED

Theorem abi_encode_member_dynamic_concrete:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) /\
  st.cs_blocks = en.cs_blocks /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en) UNION {site})
      [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
       (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    window_member_prefix infos ats avs (SUC k) d r.vs_memory /\
    mem_word_at slot r.vs_memory = n2w (window_member_tail infos ats avs k +
      LENGTH (enc (EL k ats) (EL k avs))) /\
    FLOOKUP r.vs_allocas site = SOME (slot,32) /\
    eval_operand out (r with vs_inst_idx := LENGTH en.cs_current_insts) =
      SOME (n2w (LENGTH (enc (EL k ats) (EL k avs)))) /\
    (!i b sz. i IN (window_alloca_sites func (frag_ids st en) UNION {site}) /\
      FLOOKUP r.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
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
  drule_all abi_encode_dynamic_child_concrete >> strip_tac >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `mem_bytes_at (d+window_member_tail infos ats avs k)
     (LENGTH (enc (EL k ats) (EL k avs))) t.vs_memory = enc (EL k ats) (EL k avs) /\
   mem_word_at (d+SUM (MAP abi_member_head_size (TAKE k ats))) t.vs_memory =
     n2w (window_member_tail infos ats avs k)` by
    (simp_tac (srw_ss()) [Abbr `t`] >> asm_rewrite_tac[]) >>
  `window_member_prefix infos ats avs (SUC k) d t.vs_memory` by
    (irule window_member_prefix_dynamic_step >> asm_rewrite_tac[] >>
     `window_member_prefix infos ats avs k d t.vs_memory` by
       (irule window_member_dynamic_prefix_frame >> metis_tac[]) >>
     asm_rewrite_tac[] >>
     qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_members_inv_def] >> metis_tac[]) >>
  `t.vs_memory = r.vs_memory` by simp_tac (srw_ss()) [Abbr `t`] >>
  qexists_tac `r` >>
  qpat_x_assum `Abbrev (t = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_encode_member_static_step_concrete:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,F) /\ abi_encoder_admissible ei /\ abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst child_src ei F
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  st.cs_blocks = mid.cs_blocks /\
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
  ?r. inst_extends st mid /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st mid) /\
    run_inst_seq (emitted_insts st mid) s = OK r /\
    window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid))
      [(d+SUM (MAP abi_member_head_size (TAKE k ats)),
        LENGTH (enc (EL k ats) (EL k avs)))] s
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    (!x. ~not_fresh_at mid x ==> lookup_var x
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_members_inv_restrict_end] >>
  drule_all abi_encode_member_static_concrete >> strip_tac >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `t.vs_memory = r.vs_memory /\ t.vs_allocas = r.vs_allocas` by
    simp_tac (srw_ss()) [Abbr `t`] >>
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
     drule_all window_member_tail_step >>
     fs[window_members_inv_def]) >>
  `window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en t` by
    (irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st mid)`, `k`,
       `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),
          LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
     simp[] >> metis_tac[SUBSET_UNION, SUBSET_TRANS]) >>
  qexists_tac `r` >>
  qpat_x_assum `Abbrev (t = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_member_dynamic_step_concrete:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ k < LENGTH infos /\
  EL k infos = (ei,az,ms,T) /\ abi_encoder_admissible ei /\ abi_encode_concrete_contract ei /\
  compile_abi_encode_child dst child_src ei T
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,mid) /\
  st.cs_blocks = mid.cs_blocks /\
  eval_operand child_src s = SOME (n2w (sb+abi_encoder_member_span (TAKE k infos))) /\
  (!x. child_src = Var x ==> not_fresh_at st x) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
  mid.cs_next_id <= en.cs_next_id /\
  (window_alloca_sites func (frag_ids st mid) UNION {site}) SUBSET
    (window_alloca_sites func (frag_ids st en) UNION {site}) /\
  DISJOINT (window_alloca_sites func (frag_ids st mid) UNION {site})
    (window_alloca_sites func (frag_ids mid en)) ==>
  ?r. inst_extends st mid /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st mid) /\
    run_inst_seq (emitted_insts st mid) s = OK r /\
    window_phase ctx func st mid (window_alloca_sites func (frag_ids st mid) UNION {site})
      [(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
       (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))] s
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    (!x. ~not_fresh_at mid x ==> lookup_var x
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) = lookup_var x s)
Proof
  strip_tac >>
  `window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st mid s` by metis_tac[window_members_inv_restrict_end] >>
  drule_all abi_encode_member_dynamic_concrete >> strip_tac >>
  qabbrev_tac `t = r with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `t.vs_memory = r.vs_memory /\ t.vs_allocas = r.vs_allocas` by
    simp_tac (srw_ss()) [Abbr `t`] >>
  `window_member_prefix infos ats avs (SUC k) d t.vs_memory` by metis_tac[] >>
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
  `window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en t` by
    (irule window_members_inv_phase_advance >> asm_rewrite_tac[] >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st mid) UNION {site}`, `k`,
       `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`, `s`, `st`] >>
     asm_rewrite_tac[] >>
     simp_tac (srw_ss()) [NoAsms, listTheory.EVERY_DEF] >>
     qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac) >>
  qexists_tac `r` >>
  qpat_x_assum `Abbrev (t = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_member_drop_cons[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem abi_encode_members_cons_concrete:
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ DROP k infos = (h0,h1,h2,h3)::rest /\
  abi_encode_concrete_contract h0 /\ st.cs_blocks = en.cs_blocks /\
  compile_abi_encode_complex_elems dst src ((h0,h1,h2,h3)::rest)
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?mid r. window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    DROP (SUC k) infos = rest /\
    compile_abi_encode_complex_elems dst src rest
      (abi_encoder_member_span (TAKE (SUC k) infos))
      (SUM (MAP abi_member_head_size (TAKE (SUC k) ats))) dp mid = (out,en) /\
    window_phase ctx func st mid
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    st.cs_next_var <= mid.cs_next_var /\ mid.cs_blocks = en.cs_blocks /\
    window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en) /\
    inst_extends st mid /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st mid) /\
    run_inst_seq (emitted_insts st mid) s = OK r /\
    (!x. ~not_fresh_at mid x ==> lookup_var x
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) = lookup_var x s)
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
  `ready.cs_blocks = mid.cs_blocks /\ mid.cs_blocks = en.cs_blocks` by
    metis_tac[abi_encode_no_block_split, cs_extends_trans] >>
  drule_all abi_encode_member_source_concrete >> strip_tac >>
  rename1 `window_pure_seq st ready s raw` >>
  `k < LENGTH infos /\ EL k infos = (h0,h1,h2,h3) /\ DROP (SUC k) infos = rest` by
    metis_tac[abi_encode_member_drop_cons] >>
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
  `?r ids outs. inst_extends ready mid /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts ready mid) /\
    run_inst_seq (emitted_insts ready mid)
      (raw with vs_inst_idx := LENGTH ready.cs_current_insts) = OK r /\
    window_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb cap d mid en (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    window_phase ctx func ready mid ids outs
      (raw with vs_inst_idx := LENGTH ready.cs_current_insts)
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) /\
    (!x. ~not_fresh_at mid x ==> lookup_var x
      (r with vs_inst_idx := LENGTH mid.cs_current_insts) =
      lookup_var x (raw with vs_inst_idx := LENGTH ready.cs_current_insts)) /\
    ids SUBSET (window_alloca_sites func (frag_ids ready en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
    EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs` by
    (reverse (Cases_on `h3`)
     >- (`EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids ready mid)` by metis_tac[] >>
         drule_all abi_encode_member_static_step_concrete >> strip_tac >>
         qexistsl_tac [`r`, `window_alloca_sites func (frag_ids ready mid)`,
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
        (window_alloca_sites func (frag_ids ready en) UNION {site})` by
       metis_tac[SUBSET_UNION, SUBSET_TRANS, UNION_SUBSET] >>
     `DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
       (window_alloca_sites func (frag_ids mid en))` by metis_tac[] >>
     drule_all abi_encode_member_dynamic_step_concrete >> strip_tac >>
     qexistsl_tac [`r`, `window_alloca_sites func (frag_ids ready mid) UNION {site}`,
       `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
         (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`] >>
     asm_rewrite_tac[] >>
     drule_all window_members_inv_output_bounds >> strip_tac >>
     drule_all window_members_inv_total_bounds >> strip_tac >>
     `is_dynamic (EL k ats)` by metis_tac[window_members_inv_source] >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
     qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac) >>
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
  `window_phase ctx func st mid
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s
      (r with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `ready`, `ids`, `outs`,
       `raw with vs_inst_idx := LENGTH ready.cs_current_insts`] >>
     simp_tac (srw_ss()) [NoAsms, EMPTY_SUBSET, EVERY_DEF] >>
     asm_rewrite_tac[] >>
     (conj_tac >-
       (qpat_x_assum `EVERY _ outs` mp_tac >>
        simp_tac (srw_ss()) [EVERY_MEM] >> strip_tac >>
        rpt gen_tac >> strip_tac >> qx_gen_tac `p` >> strip_tac >>
        Cases_on `p` >> first_x_assum drule >> simp[] >> decide_tac)) >>
     qpat_x_assum `ids SUBSET _` mp_tac >>
     qpat_x_assum `window_alloca_sites func (frag_ids ready en) SUBSET _` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]) >>
  `inst_extends st ready /\ run_inst_seq (emitted_insts st ready) s = OK raw /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    (qpat_assum `window_pure_seq st ready s raw` mp_tac >>
     simp_tac bool_ss [window_pure_seq_def, window_seq_def, EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts st mid = emitted_insts st ready ++ emitted_insts ready mid` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?rr. run_inst_seq (emitted_insts st mid) s = OK rr /\
    (rr with vs_inst_idx := LENGTH mid.cs_current_insts) =
    (r with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >> simp[] >>
     qexists_tac `LENGTH ready.cs_current_insts` >> asm_rewrite_tac[]) >>
  qexistsl_tac [`mid`, `rr`] >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- decide_tac) >>
  (conj_tac >- metis_tac[inst_extends_trans]) >>
  (conj_tac >- simp[]) >>
  rpt strip_tac >>
  `~not_fresh_at ready x` by metis_tac[not_fresh_at_mono] >>
  `lookup_var x (raw with vs_inst_idx := LENGTH ready.cs_current_insts) = lookup_var x s` by
    (irule window_seq_high_vars >> qexistsl_tac [`ready`, `st`] >>
     simp[] >> conj_tac
     >- (irule abi_window_emit_register_bounds >>
         qexistsl_tac [`[src;Lit (n2w (abi_encoder_member_span (TAKE k infos)))]`, `ADD`, `child_src`] >> simp[]) >>
     metis_tac[window_pure_seq_def]) >>
  metis_tac[]
QED

Theorem abi_encode_members_remaining_concrete:
  !rest ctx func infos at ats avs k src dst dp site slot sb cap d st en s out.
  window_members_inv ctx func infos at ats avs k src dst dp site slot
    sb cap d st en s /\ DROP k infos = rest /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> abi_encode_concrete_contract ei) /\
  st.cs_blocks = en.cs_blocks /\
  compile_abi_encode_complex_elems dst src rest
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?r. inst_extends st en /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en) /\
    run_inst_seq (emitted_insts st en) s = OK r /\
    window_phase ctx func st en
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    window_members_inv ctx func infos at ats avs (LENGTH infos) src dst dp site slot
      sb cap d en en (r with vs_inst_idx := LENGTH en.cs_current_insts) /\
    (!x. ~not_fresh_at en x ==> lookup_var x
      (r with vs_inst_idx := LENGTH en.cs_current_insts) = lookup_var x s)
Proof
  Induct_on `rest`
  >- (rpt gen_tac >>
      simp_tac bool_ss [Once abiEncoderTheory.compile_abi_encode_child_def,
        comp_return_def, pairTheory.PAIR_EQ] >> strip_tac >>
      `k = LENGTH infos` by
        (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [window_members_inv_def, window_member_prefix_def] >>
         strip_tac >> fs[DROP_EQ_NIL] >> decide_tac) >>
      gvs[] >>
      `s.vs_inst_idx = LENGTH en.cs_current_insts` by
        (qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
      `s with vs_inst_idx := LENGTH en.cs_current_insts = s` by
        (qpat_x_assum `s.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
      qexists_tac `s` >> simp[inst_extends_def, emitted_insts_def, run_inst_seq_def] >>
      irule window_phase_refl >>
      qpat_assum `window_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [window_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  `abi_encode_concrete_contract h0` by metis_tac[MEM] >>
  drule_all abi_encode_members_cons_concrete >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st mid) s = OK raw` >>
  `!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> abi_encode_concrete_contract ei` by metis_tac[MEM] >>

  first_x_assum drule_all >> strip_tac >>
  `window_phase ctx func st en
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s
      (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_phase_chain >>
     qexistsl_tac [`window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
       `[(d,LENGTH (enc at (ListV avs)))]`, `mid`,
       `window_alloca_sites func (frag_ids mid en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
       `[(d,LENGTH (enc at (ListV avs)))]`,
       `raw with vs_inst_idx := LENGTH mid.cs_current_insts`] >>
     asm_rewrite_tac[] >>
     qpat_x_assum `window_alloca_sites func (frag_ids mid en) SUBSET _` mp_tac >>
     simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]) >>
  `emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?rr. run_inst_seq (emitted_insts st en) s = OK rr /\
    (rr with vs_inst_idx := LENGTH en.cs_current_insts) =
    (r with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (asm_rewrite_tac[] >> irule abi_encode_run_append_normalized >> simp[] >>
     qexists_tac `LENGTH mid.cs_current_insts` >> asm_rewrite_tac[]) >>
  `mid.cs_next_var <= en.cs_next_var` by
    metis_tac[cj 3 abiEncoderCountersTheory.abi_encoder_counters_mono_mutual,
      abiEncoderCountersTheory.abi_encoder_counters_mono_def, pairTheory.SND] >>
  qexists_tac `rr` >> asm_rewrite_tac[] >>
  (conj_tac >- metis_tac[inst_extends_trans]) >>
  (conj_tac >- simp[]) >>
  rpt strip_tac >>
  `~not_fresh_at mid x` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED
