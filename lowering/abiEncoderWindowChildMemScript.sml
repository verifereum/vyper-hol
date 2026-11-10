(* Safe recursive child executions share their semantic endpoints. *)
Theory abiEncoderWindowChildMem
Ancestors
  abiEncoderWindowChild windowPhaseMem memContinuation abiEncoderWindowPhase
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderChildCode abiEncoderProps
  abiEncoderChildContext abiEncoderAppend abiEncoderWindowArrayBodyMem
  windowTransitionMem instMemFrontier allocaFootprint venomMemDefs
  emitHelperProps freshWrites compileEnv loweringStateRelDefs fragExec venomState words list pred_set arithmetic

Theorem window_static_child_run_mem:
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
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
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\ mem_cont_sim ctx func s t
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all window_static_child_context >> strip_tac >>
  `?t. window_phase ctx func st ready {} [] s t /\
    eval_operand head t = SOME (n2w (d+ho)) /\
    (!x. head = Var x ==> not_fresh_at ready x) /\ t.vs_labels = s.vs_labels /\
    mem_cont_sim ctx func s t` by
    (`alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
     `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all window_emit_add_phase_mem >> simp[word_add_n2w]) >>
  `abi_encoder_window_pre ctx func ready en head src ei at av sb cap (d+ho) t` by
    (irule window_static_child_pre >>
     asm_rewrite_tac[] >> qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >>
     asm_rewrite_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ t u` >>
  `mem_cont_sim ctx func s u` by metis_tac[mem_cont_sim_trans] >>
  suspend "package"
QED

Resume window_static_child_run_mem[package]:
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
       (mp_then Any mp_tac window_phase_effect) >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Finalise window_static_child_run_mem

Theorem window_child_prefix_run_mem:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  fn_has_code st en func /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  mem_word_at slot s.vs_memory = n2w off /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st en {} [] s t /\
    eval_operand (FST ops) t = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+off)) /\
    (!x. FST ops = Var x \/ FST (SND ops) = Var x \/
         SND (SND ops) = Var x ==> not_fresh_at en x) /\
    t.vs_labels = s.vs_labels /\ mem_cont_sim ctx func s t
Proof
  strip_tac >> drule_all window_child_prefix_context >> strip_tac >> gvs[] >>
  `a.cs_next_var = st.cs_next_var+1 /\ b.cs_next_var = a.cs_next_var+1 /\
   en.cs_next_var = b.cs_next_var+1` by
    (conj_tac
     >- (qpat_x_assum `emit_op _ _ st = (_,a)` mp_tac >>
         simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
         strip_tac >> gvs[]) >>
     conj_tac
     >- (qpat_x_assum `emit_op _ _ a = (_,b)` mp_tac >>
         simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
         strip_tac >> gvs[]) >>
     qpat_x_assum `emit_op _ _ b = (_,en)` mp_tac >>
     simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  suspend "prepare"
QED

Resume window_child_prefix_run_mem[prepare]:
  `?t1. window_phase ctx func st a {} [] s t1 /\
     eval_operand head t1 = SOME (n2w (d+ho)) /\
     (!x. head = Var x ==> not_fresh_at a x) /\ t1.vs_labels = s.vs_labels /\
     mem_cont_sim ctx func s t1` by
    (`eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all window_emit_add_phase_mem >> simp[word_add_n2w]) >>
  `eval_operand dp t1 = SOME (n2w slot) /\
   eval_operand dst t1 = SOME (n2w d)` by
    (conj_tac >> irule window_phase_eval >>
     qexistsl_tac [`ctx`, `a`, `func`, `{}`, `[]`, `s`, `st`] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `alloca_inv t1 /\ alloca_room ctx func t1 /\ ~t1.vs_halted /\
   t1.vs_current_bb = a.cs_current_bb /\
   t1.vs_inst_idx = LENGTH a.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `mem_bytes_at slot 32 t1.vs_memory = mem_bytes_at slot 32 s.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
     simp[] >> metis_tac[window_phase_effect]) >>
  `mem_word_at slot t1.vs_memory = mem_word_at slot s.vs_memory` by
    (drule abiEncoderInputFrameTheory.abi_encoder_window_word >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `mload slot t1 = n2w off` by
    metis_tac[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `slot+32 <= t1.vs_alloca_next` by
    (drule window_phase_resources >> simp[window_alloca_growth_def] >> decide_tac) >>
  suspend "load"
QED

Resume window_child_prefix_run_mem[load]:
  `?t2. window_phase ctx func a b {} [] t1 t2 /\
     eval_operand offset t2 = SOME (n2w off) /\
     (!x. offset = Var x ==> not_fresh_at b x) /\ t2.vs_labels = t1.vs_labels /\
     mem_cont_sim ctx func t1 t2` by
    (drule_all window_cursor_load_phase_mem >> asm_rewrite_tac[]) >>
  `eval_operand dst t2 = SOME (n2w d)` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `b`, `func`, `{}`, `[]`, `t1`, `a`] >>
     asm_rewrite_tac[] >> metis_tac[not_fresh_at_mono, LESS_EQ_ADD]) >>
  `alloca_inv t2 /\ alloca_room ctx func t2 /\ ~t2.vs_halted /\
   t2.vs_current_bb = b.cs_current_bb /\
   t2.vs_inst_idx = LENGTH b.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `?t3. window_phase ctx func b en {} [] t2 t3 /\
     eval_operand child t3 = SOME (n2w (d+off)) /\
     (!x. child = Var x ==> not_fresh_at en x) /\ t3.vs_labels = t2.vs_labels /\
     mem_cont_sim ctx func t2 t3` by
    (drule_all window_emit_add_phase_mem >> simp[word_add_n2w]) >>
  `window_phase ctx func a en {} [] t1 t3` by
    (irule window_phase_chain >> qexistsl_tac [`{}`, `[]`, `b`, `{}`, `[]`, `t2`] >> simp[]) >>
  `eval_operand head t3 = SOME (n2w (d+ho))` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `en`, `func`, `{}`, `[]`, `t1`, `a`] >> simp[]) >>
  `eval_operand offset t3 = SOME (n2w off)` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `en`, `func`, `{}`, `[]`, `t2`, `b`] >> simp[]) >>
  `mem_cont_sim ctx func s t3` by metis_tac[mem_cont_sim_trans] >>
  qexists_tac `t3` >> asm_rewrite_tac[] >>
  (conj_tac >- (irule window_phase_chain >>
    qexistsl_tac [`{}`, `[]`, `a`, `{}`, `[]`, `t1`] >> simp[])) >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono, LESS_EQ_ADD, LESS_EQ_TRANS]
QED

Finalise window_child_prefix_run_mem

Theorem window_dynamic_child_call_mem:
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w slot) /\
  (!x. dst = Var x \/ dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next /\
  mem_word_at slot s.vs_memory = n2w off ==>
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
      [(d+off,LENGTH (enc at av))] s actual /\ mem_cont_sim ctx func s actual
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all window_child_prefix_run_mem >> strip_tac >>
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
  suspend "restrict"
QED

Resume window_dynamic_child_call_mem[restrict]:
  `abi_encoder_window_pre ctx func prepared child_end (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (pure_rewrite_tac [abi_encoder_window_pre_def] >>
     qpat_assum `abi_encoder_window_pre _ _ prepared en _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac [abi_encoder_window_pre_def] >> strip_tac >>
     `fn_has_code prepared child_end func` by metis_tac[fn_has_code_split] >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     `inst.inst_id IN frag_ids prepared en` by
       (qpat_x_assum `_ IN frag_ids prepared child_end` mp_tac >>
        simp_tac (srw_ss()) [frag_ids_def] >> decide_tac) >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ prep actual` >>
  `window_phase ctx func prepared child_end
    (window_alloca_sites func (frag_ids prepared child_end))
    [(d+off,LENGTH (enc at av))] prep actual` by
    metis_tac[window_phase_strong_result] >>
  `(?x. FST ops = Var x) /\ (?x. FST (SND ops) = Var x)` by
    (drule window_child_prefix_variables >> strip_tac >> asm_rewrite_tac[] >> simp[]) >>
  `eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
   eval_operand (FST (SND ops)) actual = SOME (n2w off)` by
    metis_tac[window_phase_eval_var] >>
  `mem_cont_sim ctx func s actual` by metis_tac[mem_cont_sim_trans] >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`, `prep`, `actual`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- (Cases_on `child_len` >>
    fs[not_fresh_at_def, abiDecoderReentryTheory.abi_decoder_operand_live_def,
      abiDecoderReentryTheory.abi_decoder_older_vars_def])) >>
  (conj_tac >- metis_tac[]) >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `prepared`,
    `window_alloca_sites func (frag_ids prepared child_end)`,
    `[(d+off,LENGTH (enc at av))]`, `prep`] >> simp[]
QED

Finalise window_dynamic_child_call_mem

Theorem window_dynamic_child_run_mem:
  (!dst src st out st' ctx func s at av sb cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\ mem_cont_sim ctx func s t) /\
  compile_abi_encode_child dst src ei T ho (Var cursor) st = (out,en) /\
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s /\
  eval_operand dst s = SOME (n2w d) /\
  eval_operand (Var cursor) s = SOME (n2w slot) /\
  (!x. dst = Var x ==> not_fresh_at st x) /\ not_fresh_at st cursor /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  site NOTIN window_alloca_sites func (frag_ids st en) /\
  slot < dimword (:256) /\ d+ho < dimword (:256) /\
  d+ho+32 <= s.vs_alloca_next /\
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
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\ mem_cont_sim ctx func s t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp[] >> metis_tac[]) >>
  `slot+32 <= s.vs_alloca_next` by
    (`alloca_inv s` by
       (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >> asm_rewrite_tac[]) >>
     irule alloca_region_below_frontier >>
     conj_tac >- fs[alloca_inv_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all window_dynamic_child_call_mem >> strip_tac >>
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
  `d+ho+32 <= actual.vs_alloca_next` by
    (drule window_phase_resources >> simp[window_alloca_growth_def] >> decide_tac) >>
  suspend "suffix"
QED

Resume window_dynamic_child_run_mem[suffix]:
  `?t. window_phase ctx func child_end en {site} [(d+ho,32)] actual t /\
    mem_word_at (d+ho) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\ mem_cont_sim ctx func actual t` by
    (drule_all window_array_suffix_run_mem >> strip_tac >>
     drule_all window_array_transition_phase_mem >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
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
  `mem_cont_sim ctx func s t` by metis_tac[mem_cont_sim_trans] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [IN_UNION, IN_SING] >> rpt gen_tac >>
  Cases_on `i = site` >- (gvs[] >> metis_tac[]) >> strip_tac >>
  `i IN window_alloca_sites func (frag_ids st en)` by metis_tac[] >>
  `FLOOKUP actual.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `window_phase _ _ child_end en _ _ actual t`
       (mp_then Any mp_tac window_phase_effect) >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  Cases_on `i IN window_alloca_sites func (frag_ids ready child_end)`
  >- metis_tac[window_strong_result_sizes] >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `abi_encoder_registered_effect _ _ s actual` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Finalise window_dynamic_child_run_mem
