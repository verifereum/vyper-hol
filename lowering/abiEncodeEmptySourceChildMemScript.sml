(* Source-free child composition with an endpoint frame. *)
Theory abiEncodeEmptySourceChildMem
Ancestors
  loweringStateRelDefs
  abiEncodeEmptySourceSteps abiEncoderWindowPrimitiveFrameMem
  abiEncoderWindowArrayFrameMem abiEncoderWindowMemFrame
  abiEncoderChildContext abiEncoderWindowChild windowTransitionMem
  abiEncoderChildCode abiEncoderAppend abiEncoderWindowPhase memContinuation
  abiEncoderWindowArrayBodyMem abiEncoderWindowContract abiEncoderWindowPhaseFrameMem
  abiEncoderRegisteredEffect abiEncoderProps abiEncoderExtendSim
  emitHelperProps freshWrites compileEnv fragExec allocaFootprint
  instMemFrontier venomMemDefs venomState words arithmetic pred_set

Theorem empty_source_dynamic_child_call_frame[local]:
  (!dst src st out st' ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t) /\
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Lit (n2w (d+off))) s = SOME (n2w (d+off)) /\
  (!x. src = Var x \/ Lit (n2w (d+off)) = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d+off + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d+off,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
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
      [(d+off,LENGTH (enc at av))] s actual /\ mem_cont_sim ctx func s actual /\
    window_mem_frame ctx func s actual
Proof
  strip_tac >> drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  drule_all window_child_prefix_run_mem_frame >> strip_tac >>
  rename1 `window_phase ctx func st prepared {} [] s prep` >>
  `cs_extends child_end en` by
    (drule abi_encode_child_suffix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `cs_extends prepared child_end` by metis_tac[cs_extends_abi_encode] >>
  `cs_extends st prepared` by
    (drule abi_encode_child_prefix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `fn_has_code prepared child_end func` by
    metis_tac[cs_extends_trans, fn_has_code_split] >>
  `st.cs_next_var <= prepared.cs_next_var /\
   st.cs_next_id <= prepared.cs_next_id /\ child_end.cs_next_id <= en.cs_next_id` by
    decide_tac >>
  `!x. SND (SND ops) = Var x ==> not_fresh_at prepared x` by metis_tac[] >>
  drule_all empty_source_child_pre >> strip_tac >>
  qpat_x_assum `!dst src st out st' ctx func s at av sb d. _`
    drule_all >> strip_tac >>
  suspend "compose"
QED

Resume empty_source_dynamic_child_call_frame[compose]:
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
  `window_mem_frame ctx func s actual` by metis_tac[window_mem_frame_trans] >>
  qexistsl_tac [`ops`, `prepared`, `child_len`, `child_end`, `prep`, `actual`] >>
  asm_rewrite_tac[] >>
  (conj_tac >-
    (qpat_x_assum `abi_decoder_operand_live _ child_len` mp_tac >>
     Cases_on `child_len` >>
     simp_tac (srw_ss()) [not_fresh_at_def, abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def])) >>
  (conj_tac >- metis_tac[]) >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `prepared`,
    `window_alloca_sites func (frag_ids prepared child_end)`,
    `[(d+off,LENGTH (enc at av))]`, `prep`] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) []
QED

Finalise empty_source_dynamic_child_call_frame

Theorem empty_source_dynamic_child_run_frame:
  (!dst src st out st' ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t) /\
  compile_abi_encode_child dst src ei T ho (Var cursor) st = (out,en) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Lit (n2w (d+off))) s = SOME (n2w (d+off)) /\
  (!x. src = Var x \/ Lit (n2w (d+off)) = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d+off + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d+off,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
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
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `slot+32 <= s.vs_alloca_next` by
    (irule alloca_region_below_frontier >>
     conj_tac >- fs[alloca_inv_def] >>
     goal_assum (drule_at Any) >> simp_tac (srw_ss()) []) >>
  drule_all empty_source_dynamic_child_call_frame >> strip_tac >>
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
    (simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `d+ho+32 <= actual.vs_alloca_next` by
    (qpat_assum `window_phase _ _ st child_end _ _ s actual`
       (mp_tac o MATCH_MP window_phase_resources) >>
     simp_tac (srw_ss()) [window_alloca_growth_def] >> strip_tac >> decide_tac) >>
  suspend "suffix"
QED

Resume empty_source_dynamic_child_run_frame[suffix]:
  `?t. window_phase ctx func child_end en {site} [(d+ho,32)] actual t /\
    mem_word_at (d+ho) t.vs_memory = n2w off /\
    mem_word_at slot t.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    mem_cont_sim ctx func actual t /\ window_mem_frame ctx func actual t` by
    (drule_all window_array_suffix_run_mem >> strip_tac >>
     drule_all window_array_transition_phase_mem >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
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
     simp_tac (srw_ss()) [] >>
     metis_tac[LESS_EQ_TRANS, SUBSET_UNION, SUBSET_TRANS]) >>
  `mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory =
    mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory` by
    (irule abi_encoder_window_effect_bytes >>
     qexistsl_tac [`{site}`, `[(d+ho,32)]`] >> simp_tac (srw_ss()) [] >>
     metis_tac[window_phase_effect, optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `mem_cont_sim ctx func s t` by metis_tac[mem_cont_sim_trans] >>
  `window_mem_frame ctx func s t` by metis_tac[window_mem_frame_trans] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  suspend "sizes"
QED

Resume empty_source_dynamic_child_run_frame[sizes]:
  simp_tac bool_ss [IN_UNION, IN_SING] >> rpt gen_tac >>
  Cases_on `i = site` >- metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >> strip_tac >>
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
  qpat_x_assum `i IN window_alloca_sites func (frag_ids st en)` mp_tac >>
  simp_tac (srw_ss()) [window_alloca_sites_def] >> metis_tac[]
QED

Finalise empty_source_dynamic_child_run_frame

Theorem empty_source_static_child_run_frame:
  (!dst src st out st' ctx func s at av sb d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb 0 s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_room ctx func s /\
    d + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,0) (d,LENGTH (enc at av)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. window_strong_result ctx func st st' out at av d s t /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t) /\
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb 0 s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand (Lit (n2w (d+ho))) s = SOME (n2w (d+ho)) /\
  (!x. src = Var x \/ Lit (n2w (d+ho)) = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  d+ho + LENGTH (enc at av) <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,0) (d+ho,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,0) (b,sz) /\
    venomMemDefs$regions_disjoint (d+ho,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand dst s = SOME (n2w d) /\
  (!x. dst = Var x ==> not_fresh_at st x) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en))
        [(d+ho,LENGTH (enc at av))] s t /\
      mem_bytes_at (d+ho) (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      mem_cont_sim ctx func s t /\ window_mem_frame ctx func s t
Proof
  strip_tac >> drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase_mem_conditional_frame >> strip_tac >>
  `eval_operand head t = SOME (n2w (d+ho))` by fs[word_add_n2w] >>
  `st.cs_next_var <= prepared.cs_next_var /\
   st.cs_next_id <= prepared.cs_next_id /\ en.cs_next_id <= en.cs_next_id` by decide_tac >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all empty_source_child_pre >> strip_tac >>
  qpat_x_assum `!dst src st out st' ctx func s at av sb d. _` drule_all >> strip_tac >>
  `mem_cont_sim ctx func s t' /\ window_mem_frame ctx func s t'` by
    metis_tac[mem_cont_sim_trans, window_mem_frame_trans] >>
  suspend "package"
QED

Resume empty_source_static_child_run_frame[package]:
  `window_phase ctx func prepared en (window_alloca_sites func (frag_ids prepared en))
    [(d+ho,LENGTH (enc at av))] t t'` by metis_tac[window_phase_strong_result] >>
  `window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
    [(d+ho,LENGTH (enc at av))] s t'` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `prepared`,
       `window_alloca_sites func (frag_ids prepared en)`, `[(d+ho,LENGTH (enc at av))]`, `t`] >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms] >>
     irule window_alloca_sites_mono >>
     simp_tac (srw_ss()) [SUBSET_DEF, frag_ids_def] >> decide_tac) >>
  `mem_bytes_at (d+ho) (LENGTH (enc at av)) t'.vs_memory = enc at av /\
   eval_operand out t' = SOME (n2w (LENGTH (enc at av)))` by
    metis_tac[window_strong_result_public, abi_encoder_window_result_output] >>
  qexists_tac `t'` >> asm_rewrite_tac[] >> rpt strip_tac >>
  Cases_on `i IN window_alloca_sites func (frag_ids prepared en)`
  >- metis_tac[window_strong_result_sizes] >>
  `FLOOKUP t.vs_allocas i = SOME (b,sz)` by
    (drule window_strong_result_effect >>
     simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `window_phase _ _ st prepared _ _ s t`
       (mp_then Any mp_tac window_phase_effect) >>
     simp_tac (srw_ss()) [abi_encoder_registered_effect_def] >> metis_tac[]) >>
  qpat_x_assum `i IN window_alloca_sites func (frag_ids st en)` mp_tac >>
  simp_tac (srw_ss()) [window_alloca_sites_def] >> metis_tac[]
QED

Finalise empty_source_static_child_run_frame
