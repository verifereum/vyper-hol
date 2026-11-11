(* Compiler phase/site and setup-state transport for the window encoder. *)
Theory abiEncodeWindowTransport
Ancestors
  abiBuiltinEncodeCode abiBuiltinEncodeContext abiEncoderWindowContract
  abiEncoderWindowPhase abiEncoderRegisteredEffect actualAllocExec
  abiBuiltinAllocation abiEncoderProps exprLoweringProps emitHelperProps
  abiEncoderAddressReach fragExec allocaSiteResource freshWrites abiDecoderReentry
  compileEnv emitHelper venomState venomExecSemantics venomInst
  loweringHalt words list rich_list arithmetic pred_set finite_map

Theorem abi_encode_method_id_shape:
  abi_builtin_encode_method_id mid buf st = ((),en) ==>
  cs_extends st en /\ st.cs_next_var <= en.cs_next_var
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_method_id_def, comp_return_def, comp_bind_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[cs_extends_def, emitted_insts_def, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def,
    GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem abi_encode_setup_parts:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  compile_alloc_buffer (32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4))) st = (buf,allocated) /\
  emit_op ADD [buf.buf_operand;Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))] allocated = (data,addressed) /\
  abi_builtin_encode_method_id mid buf.buf_operand addressed = ((),ready) /\
  fn_has_code st ready func ==>
  fn_has_code st allocated func /\ fn_has_code allocated ready func /\
  st.cs_next_var <= allocated.cs_next_var
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule abi_encode_method_id_shape >> strip_tac >>
  `cs_extends allocated ready` by metis_tac[cs_extends_trans] >>
  `cs_extends st allocated` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem abi_encode_setup_source[local]:
  window_phase ctx func st en {st.cs_next_id}
    (case mid of NONE => [] | SOME _ => [(p+32,32)]) s t /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
  venomMemDefs$regions_disjoint (sb,cap) (p,n) /\
  (IS_SOME mid ==> 64 <= n) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_effect_source >>
  qexistsl_tac [`{st.cs_next_id}`,
    `case mid of NONE => [] | SOME _ => [(p+32,32)]`, `s`] >>
  conj_tac >- simp[window_phase_effect] >> conj_tac
  >- (Cases_on `mid` >> simp[] >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[window_phase_effect]
QED

Theorem abi_encode_window_sites:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code st final func ==>
  st.cs_next_id IN window_alloca_sites func (frag_ids st final) /\
  st.cs_next_id NOTIN window_alloca_sites func (frag_ids ready body_end) /\
  window_alloca_sites func (frag_ids ready body_end) SUBSET
    window_alloca_sites func (frag_ids st final)
Proof
  strip_tac >> drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_trace >> strip_tac >>
  drule_all abi_encode_setup_parts >> strip_tac >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  simp[window_alloca_sites_def, frag_ids_def, SUBSET_DEF] >>
  `st.cs_next_id < ready.cs_next_id` by (Cases_on `mid` >> fs[]) >>
  conj_tac
  >- (conj_tac >- decide_tac >>
      qmatch_asmsub_abbrev_tac `MEM alloc_inst (fn_insts func)` >>
      qexists_tac `alloc_inst` >> simp[Abbr `alloc_inst`, mk_inst_def]) >>
  disj1_tac >> disj1_tac >> Cases_on `mid` >> simp[]
QED

Theorem abi_encode_setup_scratch[local]:
  window_phase ctx func st ready {st.cs_next_id} outs s u /\
  FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,n) /\
  scratch SUBSET ids /\ st.cs_next_id NOTIN scratch /\
  p <= d /\ d+len <= p+n /\
  (!i b sz. i IN ids /\ i <> st.cs_next_id /\
    FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) ==>
  !i b sz. i IN scratch /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,len) (b,sz)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `i <> st.cs_next_id /\ i IN ids` by metis_tac[SUBSET_DEF] >>
  `FLOOKUP s.vs_allocas i = SOME (b,sz)` by
    (qpat_x_assum `window_phase _ _ _ _ _ _ _ _` mp_tac >>
     simp[window_phase_def, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  `sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)` by metis_tac[] >>
  simp[] >>
  `alloca_inv u` by metis_tac[window_phase_resources] >>
  `venomMemDefs$regions_disjoint (p,n) (b,sz)` by
    metis_tac[alloca_site_registered_disjoint] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p,n) (b,sz)` mp_tac >>
  simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_encode_window_pre_transport:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len k body_end = ((),final) /\
  k = (case mid of NONE => 0 | SOME _ => 4) /\
  n = 32+32*word_size (maxlen+k) /\
  abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  LENGTH (enc at av) <= maxlen /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  sb+cap <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (p,n) /\
  (!i b sz. i IN window_alloca_sites func (frag_ids st final) /\
    i <> st.cs_next_id /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
  window_phase ctx func st ready {st.cs_next_id}
    (case mid of NONE => [] | SOME _ => [(p+32,32)]) s u /\
  eval_operand (SND ops) u = SOME (n2w (p+32+k)) /\
  FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,n) /\
  p+n <= u.vs_alloca_next /\ p+n < dimword (:256) ==>
  abi_encoder_window_pre ctx func ready body_end (SND ops) src ei at av
    sb cap (p+32+k) u
Proof
  strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  `p+32+k+LENGTH (enc at av) <= p+n` by
    (mp_tac (Q.SPEC `maxlen+k` abi_builtin_word_size_capacity) >> decide_tac) >>
  `(IS_SOME mid ==> 64 <= n)` by
    (Cases_on `mid` >- simp[] >>
     `k = 4` by (qpat_x_assum `k = _` mp_tac >> simp[]) >>
     `4 <= 32*word_size (maxlen+k)` by
       (mp_tac (Q.SPEC `maxlen+k` abi_builtin_word_size_capacity) >> decide_tac) >>
     Cases_on `word_size (maxlen+k)` >> decide_tac) >>
  `abi_encoder_window_input ei at av sb cap u.vs_memory` by
    (drule_all abi_encode_setup_source >> simp[]) >>
  `eval_operand src u = SOME (n2w sb)` by metis_tac[window_phase_operand] >>
  `alloca_inv u /\ alloca_room ctx func u /\ window_alloca_growth s u` by
    metis_tac[window_phase_resources] >>
  `~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
    u.vs_inst_idx = LENGTH ready.cs_current_insts` by metis_tac[window_phase_control] >>
  qpat_x_assum `k = _` SUBST_ALL_TAC >>
  drule_all abi_encode_window_sites >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  simp_tac bool_ss [abi_encoder_window_pre_def] >>
  asm_rewrite_tac [] >> conj_tac
  >- (rpt strip_tac >- metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `abi_decoder_operand_live ready.cs_next_var (SND ops)` mp_tac >>
      qpat_x_assum `SND ops = Var x` (fn th => rewrite_tac [th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  conj_tac
  >- (qpat_x_assum `window_alloca_growth s u` mp_tac >>
      simp_tac bool_ss [window_alloca_growth_def] >> strip_tac >> decide_tac) >>
  conj_tac >- decide_tac >> conj_tac
  >- (qpat_x_assum `venomMemDefs$regions_disjoint (sb,cap) (p,n)` mp_tac >>
      simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `p <= p+32+(case mid of NONE => 0 | SOME _ => 4)` by decide_tac >>
  `inst.inst_id IN window_alloca_sites func (frag_ids ready body_end)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def] >>
     asm_rewrite_tac[] >> qexists_tac `inst` >> asm_rewrite_tac[]) >>
  drule_all (Q.INST [`d` |-> `p+32+(case mid of NONE => 0 | SOME _ => 4)`,
    `len` |-> `LENGTH (enc at av)`] abi_encode_setup_scratch) >> simp[]
QED
