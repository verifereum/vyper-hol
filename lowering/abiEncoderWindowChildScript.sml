(* Exact recursive child boundaries; no full-capacity source conversion. *)
Theory abiEncoderWindowChild
Ancestors
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderChildCode
  abiEncoderAppend abiEncoderCounters abiEncoderAddressReach abiEncoderProps
  abiEncoderChildContext abiEncoderWindowLookup
  emitHelperProps freshWrites compileEnv fragExec venomState words list pred_set arithmetic

Definition window_observed_contract_def:
  window_observed_contract ei <=>
    !dst src st out en ctx func s at av sb cap d.
      compile_abi_encode_to_buf dst src ei st = (out,en) /\
      abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s ==>
      ?t. window_strong_result ctx func st en out at av d s t /\
        (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
End

Theorem window_observed_contract_strong:
  window_observed_contract ei ==> window_strong_contract ei
Proof
  simp[window_observed_contract_def, window_strong_contract_def] >> metis_tac[]
QED

Theorem window_static_child_context:
  compile_abi_encode_child dst src ei F ho dp st = (out,en) /\
  fn_has_code st en func ==>
  ?head ready.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,ready) /\
    compile_abi_encode_to_buf head src ei ready = (out,en) /\
    fn_has_code st ready func /\ fn_has_code ready en func /\
    cs_extends st ready /\ cs_extends ready en /\
    st.cs_next_var <= ready.cs_next_var /\ ready.cs_next_var <= en.cs_next_var /\
    st.cs_next_id <= ready.cs_next_id /\ ready.cs_next_id <= en.cs_next_id
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  `cs_extends prepared en` by metis_tac[cs_extends_abi_encode] >>
  `prepared.cs_next_var <= en.cs_next_var /\ prepared.cs_next_id <= en.cs_next_id` by
    (mp_tac (cj 2 abi_encoder_counters_mono_mutual) >>
     simp_tac bool_ss [abi_encoder_counters_mono_def] >>
     disch_then (qspecl_then [`head`, `src`, `ei`, `prepared`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id` by
    (qpat_assum `emit_op _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [emitHelperTheory.emit_op_def, fresh_var_def,
       fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     disch_then (SUBST1_TAC o GSYM o CONJUNCT2) >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl_tac [`head`, `prepared`] >> asm_rewrite_tac[]
QED

(* Empty-footprint preparation transports exact child windows and site reuse. *)
Theorem window_static_child_pre:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap (d+ho) s /\
  window_phase ctx func st ready {} [] s t /\
  t.vs_labels = s.vs_labels /\
  st.cs_next_var <= ready.cs_next_var /\
  st.cs_next_id <= ready.cs_next_id /\
  fn_has_code ready en func /\
  eval_operand head t = SOME (n2w (d+ho)) /\
  (!x. head = Var x ==> not_fresh_at ready x) ==>
  abi_encoder_window_pre ctx func ready en head src ei at av sb cap (d+ho) t
Proof
  strip_tac >>
  `abi_encoder_registered_effect {} [] s t` by metis_tac[window_phase_effect] >>
  `abi_encoder_window_input ei at av sb cap t.vs_memory` by
    (irule abi_encoder_window_effect_source >> qexistsl_tac [`{}`, `[]`, `s`] >>
     fs[abi_encoder_window_pre_def]) >>
  `eval_operand src t = SOME (n2w sb)` by
    (irule window_phase_eval >> qexistsl_tac [`ctx`, `ready`, `func`, `{}`, `[]`, `s`, `st`] >>
     fs[abi_encoder_window_pre_def] >> metis_tac[]) >>
  `!i. FLOOKUP t.vs_allocas i = FLOOKUP s.vs_allocas i` by
    fs[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
  `alloca_inv t /\ alloca_room ctx func t /\ window_alloca_growth s t` by
    metis_tac[window_phase_resources] >>
  `~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts` by metis_tac[window_phase_control] >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_encoder_window_pre_def, window_alloca_growth_def] >>
  strip_tac >>
  `s.vs_alloca_next <= t.vs_alloca_next` by fs[window_alloca_growth_def] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- metis_tac[not_fresh_at_mono]
  >- decide_tac
  >- decide_tac >>
  rpt strip_tac >>
  `inst.inst_id IN frag_ids st en` by
    (qpat_x_assum `_ IN frag_ids ready en` mp_tac >>
     simp_tac (srw_ss()) [frag_ids_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem window_static_child_run:
  window_strong_contract ei /\
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
     drule_all window_emit_add_phase >> simp[wordsTheory.word_add_n2w]) >>
  `abi_encoder_window_pre ctx func ready en head src ei at av sb cap (d+ho) t` by
    (irule window_static_child_pre >>
     asm_rewrite_tac[] >> qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `window_strong_contract ei` mp_tac >>
  rewrite_tac[window_strong_contract_def] >>
  disch_then drule_all >> strip_tac >>
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
     simp_tac bool_ss [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `window_phase _ _ st ready _ _ s t`
       (mp_tac o MATCH_MP window_phase_effect) >>
     simp_tac (srw_ss()) [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

(* Parent ownership restricts to a live child's output, including empty children. *)
Theorem window_child_pre_parent:
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  sb+cap <= s.vs_alloca_next /\ d+n <= s.vs_alloca_next /\
  off+LENGTH (enc at av) <= n /\
  venomMemDefs$regions_disjoint (sb,cap) (d,n) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,n) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_window_pre ctx func st en (Lit (n2w (d+off))) src
    ei at av sb cap (d+off) s
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_window_pre_def] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [eval_operand_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (d,n)` mp_tac >>
      simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,n) (b,sz)` by metis_tac[] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (d,n) (b,sz)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Prefix code is split at actual emitted instruction boundaries. *)
Theorem window_child_prefix_context:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  fn_has_code st en func ==>
  ?head a offset b child.
    emit_op ADD [dst;Lit (n2w ho)] st = (head,a) /\
    emit_op MLOAD [dp] a = (offset,b) /\
    emit_op ADD [dst;offset] b = (child,en) /\
    ops = (head,offset,child) /\
    fn_has_code st a func /\ fn_has_code a b func /\ fn_has_code b en func /\
    cs_extends st a /\ cs_extends a b /\ cs_extends b en
Proof
  simp_tac bool_ss [abi_encode_child_prefix_def, comp_bind_def,
    comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [dst;Lit (n2w ho)] st = (head,a)` >>
  rename1 `emit_op MLOAD [dp] a = (offset,b)` >>
  rename1 `emit_op ADD [dst;offset] b = (child,en)` >>
  `cs_extends st a /\ cs_extends a b /\ cs_extends b en` by
    metis_tac[abi_encoder_emit_address_shape] >>
  `cs_extends a en` by metis_tac[cs_extends_trans] >>
  `fn_has_code st a func /\ fn_has_code a en func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code a b func /\ fn_has_code b en func` by
    metis_tac[fn_has_code_split] >>
  asm_rewrite_tac[]
QED

Theorem window_child_emit_counter[local]:
  emit_op opc operands st = (out,en) ==>
  en.cs_next_var = st.cs_next_var+1
Proof
  simp[emitHelperTheory.emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem window_child_pure_word[local]:
  window_phase ctx func st en {} [] s t ==>
  mem_word_at p t.vs_memory = mem_word_at p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at p 32 t.vs_memory = mem_bytes_at p 32 s.vs_memory` by
    (irule abi_encoder_window_effect_bytes >> qexistsl_tac [`{}`, `[]`] >>
     simp[] >> metis_tac[window_phase_effect]) >>
  drule abiEncoderInputFrameTheory.abi_encoder_window_word >>
  disch_then (qspec_then `0` mp_tac) >> simp[]
QED

Theorem window_child_pure_chain[local]:
  window_phase ctx func st mid {} [] s t /\
  window_phase ctx func mid en {} [] t u /\
  st.cs_next_var <= mid.cs_next_var ==>
  window_phase ctx func st en {} [] s u
Proof
  strip_tac >> irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `mid`, `{}`, `[]`, `t`] >> simp[]
QED

Theorem window_child_prefix_run_observed:
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
    t.vs_labels = s.vs_labels /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_child_prefix_context >> strip_tac >> gvs[] >>
  `a.cs_next_var = st.cs_next_var+1 /\ b.cs_next_var = a.cs_next_var+1 /\
   en.cs_next_var = b.cs_next_var+1` by metis_tac[window_child_emit_counter] >>
  `?t1. window_phase ctx func st a {} [] s t1 /\
     eval_operand head t1 = SOME (n2w (d+ho)) /\
     (!x. head = Var x ==> not_fresh_at a x) /\ t1.vs_labels = s.vs_labels /\
     (!x. ~not_fresh_at a x ==> lookup_var x t1 = lookup_var x s)` by
    (`eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all window_emit_add_phase_observed >> simp[wordsTheory.word_add_n2w]) >>
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
    metis_tac[window_child_pure_word, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `?t2. window_phase ctx func a b {} [] t1 t2 /\
     eval_operand offset t2 = SOME (n2w off) /\
     (!x. offset = Var x ==> not_fresh_at b x) /\ t2.vs_labels = t1.vs_labels /\
     (!x. ~not_fresh_at b x ==> lookup_var x t2 = lookup_var x t1)` by
    (drule_all window_cursor_load_phase_observed >> asm_rewrite_tac[]) >>
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
     (!x. ~not_fresh_at en x ==> lookup_var x t3 = lookup_var x t2)` by
    (drule_all window_emit_add_phase_observed >> simp[wordsTheory.word_add_n2w]) >>
  `window_phase ctx func a en {} [] t1 t3` by
    (irule window_child_pure_chain >> qexistsl_tac [`b`, `t2`] >> simp[]) >>
  `eval_operand head t3 = SOME (n2w (d+ho))` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `en`, `func`, `{}`, `[]`, `t1`, `a`] >> simp[]) >>
  `eval_operand offset t3 = SOME (n2w off)` by
    (irule window_phase_eval >>
     qexistsl_tac [`ctx`, `en`, `func`, `{}`, `[]`, `t2`, `b`] >> simp[]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t3 = lookup_var x s` by
    (rpt strip_tac >>
     `~not_fresh_at a x /\ ~not_fresh_at b x` by
       (fs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) >>
  qexists_tac `t3` >> asm_rewrite_tac[] >>
  (conj_tac >- (irule window_child_pure_chain >>
    qexistsl_tac [`a`, `t1`] >> simp[])) >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono, LESS_EQ_ADD, LESS_EQ_TRANS]
QED

Theorem window_child_prefix_run:
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
    t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all window_child_prefix_run_observed >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_child_pre_end[local]:
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

Theorem window_child_prefix_variables:
  abi_encode_child_prefix dst ho dp st = (ops,en) ==>
  ?h v c. ops = (Var h,Var v,Var c)
Proof
  simp[abi_encode_child_prefix_def, emitHelperTheory.emit_op_def,
    fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem window_phase_eval_var:
  window_phase ctx func st en ids outs s t /\
  (?x. op = Var x) /\
  (!x. op = Var x ==> not_fresh_at st x) /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  strip_tac >> gvs[eval_operand_def] >> metis_tac[window_phase_vars]
QED

(* This boundary stops before bookkeeping, retaining the recursive result. *)
Theorem window_dynamic_child_call:
  window_strong_contract ei /\
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
  `abi_encoder_window_pre ctx func prepared en (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (irule window_static_child_pre >> asm_rewrite_tac[] >> simp[] >>
     qexistsl_tac [`Lit (n2w (d+off))`, `s`, `st`] >> simp[]) >>
  `abi_encoder_window_pre ctx func prepared child_end (SND (SND ops)) src
    ei at av sb cap (d+off) prep` by
    (irule window_child_pre_end >> asm_rewrite_tac[] >> qexists_tac `en` >> simp[]) >>
  qpat_x_assum `window_strong_contract ei` mp_tac >>
  rewrite_tac[window_strong_contract_def] >>
  disch_then drule_all >> strip_tac >>
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

Theorem window_child_void_shape[local]:
  emit_void opc operands st = ((),en) ==>
  cs_extends st en /\ en.cs_next_var = st.cs_next_var
Proof
  simp[emitHelperTheory.emit_void_def, fresh_id_def, emit_def,
    comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qexists_tac `[]` >> simp[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem window_child_suffix_context:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func ==>
  ?a next b.
    emit_void MSTORE [head;offset] st = ((),a) /\
    emit_op ADD [offset;len] a = (next,b) /\
    emit_void MSTORE [dp;next] b = ((),en) /\ out = len /\
    fn_has_code st a func /\ fn_has_code a b func /\ fn_has_code b en func /\
    a.cs_next_var = st.cs_next_var /\ b.cs_next_var = a.cs_next_var+1 /\
    en.cs_next_var = b.cs_next_var
Proof
  simp_tac bool_ss [abi_encode_child_suffix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_void MSTORE [head;offset] st = ((),a)` >>
  rename1 `emit_op ADD [offset;len] a = (next,b)` >>
  rename1 `emit_void MSTORE [dp;next] b = ((),en)` >>
  `cs_extends st a /\ cs_extends a b /\ cs_extends b en` by
    metis_tac[window_child_void_shape, abi_encoder_emit_address_shape] >>
  `cs_extends a en` by metis_tac[cs_extends_trans] >>
  `fn_has_code st a func /\ fn_has_code a en func` by metis_tac[fn_has_code_split] >>
  `fn_has_code a b func /\ fn_has_code b en func` by metis_tac[fn_has_code_split] >>
  `a.cs_next_var = st.cs_next_var /\ en.cs_next_var = b.cs_next_var` by
    metis_tac[window_child_void_shape] >>
  asm_rewrite_tac[] >> metis_tac[window_child_emit_counter]
QED

Theorem window_child_store_eval[local]:
  eval_operand op ((mstore p w s) with vs_inst_idx := idx) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def,
    venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def]
QED

Theorem window_child_suffix_steps_observed:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a b t1 t2 t3.
    window_phase ctx func st a {} [(h,32)] s t1 /\
    window_phase ctx func a b {} [] t1 t2 /\
    window_phase ctx func b en {site} [] t2 t3 /\
    a.cs_next_var = st.cs_next_var /\ b.cs_next_var = a.cs_next_var+1 /\
    t1.vs_memory = (mstore h (n2w off) s).vs_memory /\
    t3 = ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts) /\
    out = len /\ eval_operand out t3 = SOME (n2w n) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t3 = lookup_var x s)
Proof
  strip_tac >> drule_all window_child_suffix_context >> strip_tac >>
  qabbrev_tac `t1 = (mstore h (n2w off) s) with vs_inst_idx := LENGTH a.cs_current_insts` >>
  `window_phase ctx func st a {} [(h,32)] s t1` by
    (simp_tac bool_ss [Abbr `t1`] >> irule window_output_store_phase >>
     asm_rewrite_tac[] >> qexistsl_tac [`head`, `offset`] >> asm_rewrite_tac[]) >>
  `eval_operand offset t1 = SOME (n2w off) /\
   eval_operand len t1 = SOME (n2w n) /\ eval_operand dp t1 = SOME (n2w slot)` by
    simp[Abbr `t1`, window_child_store_eval] >>
  `alloca_inv t1 /\ alloca_room ctx func t1 /\ ~t1.vs_halted /\
   t1.vs_current_bb = a.cs_current_bb /\ t1.vs_inst_idx = LENGTH a.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `?t2. window_phase ctx func a b {} [] t1 t2 /\
    eval_operand next t2 = SOME (n2w (off+n)) /\
    (!x. next = Var x ==> not_fresh_at b x) /\ t2.vs_labels = t1.vs_labels /\
    (!x. ~not_fresh_at b x ==> lookup_var x t2 = lookup_var x t1)` by
    (drule_all window_emit_add_phase_observed >> simp[wordsTheory.word_add_n2w]) >>
  `eval_operand dp t2 = SOME (n2w slot) /\ eval_operand len t2 = SOME (n2w n)` by
    (conj_tac >> irule window_phase_eval >> asm_rewrite_tac[] >>
     qexistsl_tac [`ctx`, `b`, `func`, `{}`, `[]`, `t1`, `a`] >>
     asm_rewrite_tac[] >> fs[not_fresh_at_def] >> metis_tac[]) >>
  `alloca_inv t2 /\ alloca_room ctx func t2 /\ ~t2.vs_halted /\
   t2.vs_current_bb = b.cs_current_bb /\ t2.vs_inst_idx = LENGTH b.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `FLOOKUP t2.vs_allocas site = SOME (slot,32)` by
    (irule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
     qexistsl_tac [`{}`, `[]`, `t1`] >>
     (conj_tac >- simp[Abbr `t1`, venomStateTheory.mstore_def,
       venomStateTheory.write_memory_with_expansion_def]) >>
     metis_tac[window_phase_effect]) >>
  `window_phase ctx func b en {site} [] t2
    ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_cursor_store_phase >> asm_rewrite_tac[] >> metis_tac[]) >>
  qexistsl_tac [`a`, `b`, `t1`, `t2`,
    `(mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts`] >>
  simp[window_child_store_eval, Abbr `t1`] >>
  rpt strip_tac >>
  qpat_x_assum `!x. ~not_fresh_at b x ==> _` (qspec_then `x` mp_tac) >>
  simp[not_fresh_at_def, lookup_var_def, venomStateTheory.mstore_def,
    venomStateTheory.write_memory_with_expansion_def] >>
  fs[not_fresh_at_def]
QED

Theorem window_child_suffix_steps:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  fn_has_code st en func /\
  eval_operand head s = SOME (n2w h) /\ eval_operand offset s = SOME (n2w off) /\
  eval_operand dp s = SOME (n2w slot) /\ eval_operand len s = SOME (n2w n) /\
  (!x. dp = Var x \/ len = Var x ==> not_fresh_at st x) /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?a b t1 t2 t3.
    window_phase ctx func st a {} [(h,32)] s t1 /\
    window_phase ctx func a b {} [] t1 t2 /\
    window_phase ctx func b en {site} [] t2 t3 /\
    a.cs_next_var = st.cs_next_var /\ b.cs_next_var = a.cs_next_var+1 /\
    t1.vs_memory = (mstore h (n2w off) s).vs_memory /\
    t3 = ((mstore slot (n2w (off+n)) t2) with vs_inst_idx := LENGTH en.cs_current_insts) /\
    out = len /\ eval_operand out t3 = SOME (n2w n)
Proof
  strip_tac >> drule_all window_child_suffix_steps_observed >> strip_tac >>
  qexistsl_tac [`a`, `b`, `t1`, `t2`, `t3`] >> asm_rewrite_tac[]
QED

Theorem window_child_suffix_run_observed:
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
    eval_operand out t = SOME (n2w n) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all window_child_suffix_steps_observed >> strip_tac >>
  `window_phase ctx func a en {site} [] t1 t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[]`, `b`, `{site}`, `[]`, `t2`] >> simp[]) >>
  `window_phase ctx func st en {site} [(h,32)] s t3` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`, `[(h,32)]`, `a`, `{site}`, `[]`, `t1`] >> simp[]) >>
  `mem_word_at h t2.vs_memory = n2w off` by
    (`mem_word_at h t2.vs_memory = mem_word_at h t1.vs_memory` by
       metis_tac[window_child_pure_word] >>
     asm_rewrite_tac[] >> simp[valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  `mem_word_at h t3.vs_memory = n2w off /\
   mem_word_at slot t3.vs_memory = n2w (off+n)` by
    (asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
     metis_tac[valueEncodingPropsTheory.mstore_mem_word_at_disjoint,
       valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
  qexists_tac `t3` >> asm_rewrite_tac[] >>
  metis_tac[window_phase_effect,
    abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated]
QED

Theorem window_child_suffix_run:
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
    eval_operand out t = SOME (n2w n)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all window_child_suffix_run_observed >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem window_dynamic_child_run:
  window_strong_contract ei /\
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
        FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp[] >> metis_tac[]) >>
  drule_all window_dynamic_child_call >> strip_tac >>
  `eval_operand (Var cursor) actual = SOME (n2w slot)` by
    metis_tac[window_phase_eval_var] >>
  `not_fresh_at child_end cursor` by metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
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

Theorem window_static_child_run_observed:
  window_observed_contract ei /\
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
      (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all window_static_child_context >> strip_tac >>
  `?t. window_phase ctx func st ready {} [] s t /\
    eval_operand head t = SOME (n2w (d+ho)) /\
    (!x. head = Var x ==> not_fresh_at ready x) /\ t.vs_labels = s.vs_labels /\
    (!x. ~not_fresh_at ready x ==> lookup_var x t = lookup_var x s)` by
    (`alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
       s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
     `eval_operand (Lit (n2w ho)) s = SOME (n2w ho)` by simp[eval_operand_def] >>
     drule_all window_emit_add_phase_observed >> simp[wordsTheory.word_add_n2w]) >>
  `abi_encoder_window_pre ctx func ready en head src ei at av sb cap (d+ho) t` by
    (irule window_static_child_pre >>
     asm_rewrite_tac[] >> qexistsl_tac [`Lit (n2w (d+ho))`, `s`, `st`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `window_observed_contract ei` mp_tac >>
  rewrite_tac[window_observed_contract_def] >>
  disch_then drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ t u` >>
  `!x. ~not_fresh_at en x ==> lookup_var x u = lookup_var x s` by
    metis_tac[abi_window_high_vars_trans] >>
  qexists_tac `u` >> asm_rewrite_tac[] >>
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
     simp_tac bool_ss [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_assum `window_phase _ _ st ready _ _ s t`
       (mp_tac o MATCH_MP window_phase_effect) >>
     simp_tac (srw_ss()) [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  metis_tac[window_pre_sites]
QED

Theorem window_dynamic_child_call_observed:
  window_observed_contract ei /\
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
    (!x. ~not_fresh_at child_end x ==> lookup_var x actual = lookup_var x s) /\
    child_end.cs_next_var <= en.cs_next_var
Proof
  strip_tac >>
  `fn_has_code st en func` by fs[abi_encoder_window_pre_def] >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by fs[abi_encoder_window_pre_def] >>
  drule_all window_child_prefix_run_observed >> strip_tac >>
  rename1 `window_phase ctx func st prepared {} [] s prep` >>
  `cs_extends child_end en` by
    (drule abi_encode_child_suffix_shape >> strip_tac >>
     irule abi_encoder_straight_extends >> asm_rewrite_tac[]) >>
  `child_end.cs_next_var <= en.cs_next_var` by
    (drule_all window_child_suffix_context >> strip_tac >> decide_tac) >>
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
    (irule window_child_pre_end >> asm_rewrite_tac[] >> qexists_tac `en` >> simp[]) >>
  qpat_x_assum `window_observed_contract ei` mp_tac >>
  rewrite_tac[window_observed_contract_def] >>
  disch_then drule_all >> strip_tac >>
  rename1 `window_strong_result _ _ _ _ _ _ _ _ prep actual` >>
  `!x. ~not_fresh_at child_end x ==> lookup_var x actual = lookup_var x s` by
    metis_tac[abi_window_high_vars_trans] >>
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

Theorem window_dynamic_child_run_observed:
  window_observed_contract ei /\
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
      (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. dst = Var x \/ Var cursor = Var x ==> not_fresh_at st x` by
    (simp[] >> metis_tac[]) >>
  drule_all window_dynamic_child_call_observed >> strip_tac >>
  `eval_operand (Var cursor) actual = SOME (n2w slot)` by
    metis_tac[window_phase_eval_var] >>
  `not_fresh_at child_end cursor` by metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
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
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    (!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x actual)` by
    (irule window_child_suffix_run_observed >> asm_rewrite_tac[] >>
     qexistsl_tac [`Var cursor`, `FST ops`, `len`, `FST (SND ops)`] >> simp[] >> metis_tac[]) >>
  `!x. ~not_fresh_at en x ==> lookup_var x t = lookup_var x s` by
    metis_tac[abi_window_high_vars_trans] >>
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
