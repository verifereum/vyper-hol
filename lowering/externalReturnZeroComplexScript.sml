Theory externalReturnZeroComplex
Ancestors
  externalReturnZeroWindow externalReturnZeroChild externalReturnZeroContract abiEncoderWindowStructuralMembers
  abiEncoderWindowComplex abiEncoderWindowMembers abiEncoderWindowContract
  abiEncoderWindowPhase abiEncoderRegisteredEffect abiEncoderChildContext
  abiEncoderAddressReach abiEncoderAdmissible abiEncoderInput abiEncoderProps
  abiEncoderAppend abiEncoder abiEncoderWindow contractABI freshWrites compileEnv fragExec
  words list rich_list finite_map pred_set arithmetic venomState venomMemDefs
  abiEncoderOpenInput abiEncoderCounters exprLoweringProps emitHelperProps valueEncoding
  abiDecodeRanges

Theorem zero_member_drop_cons[local]:
  !l n h rest. DROP n l = h::rest ==>
    n < LENGTH l /\ EL n l = h /\ DROP (SUC n) l = rest
Proof
  Induct >> rw[] >> Cases_on `n` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem zero_member_envelope_frame[local]:
  EVERY (\(b,n). d <= b /\ b+n <= d+len) outs ==>
  !a. EVERY (\(b,n). a < b \/ b+n <= a) [(d,len)] ==>
      EVERY (\(b,n). a < b \/ b+n <= a) outs
Proof
  simp_tac (srw_ss()) [EVERY_MEM] >> strip_tac >>
  rpt gen_tac >> strip_tac >> qx_gen_tac `r` >> strip_tac >>
  Cases_on `r` >> first_x_assum drule >> simp[] >> decide_tac
QED

Theorem zero_members_cons_run_sizes:
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ DROP k infos = (h0,h1,h2,h3)::rest /\
  zero_strong_contract h0 /\
  compile_abi_encode_complex_elems dst src ((h0,h1,h2,h3)::rest)
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?mid u. zero_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb d mid en u /\ DROP (SUC k) infos = rest /\
    compile_abi_encode_complex_elems dst src rest
      (abi_encoder_member_span (TAKE (SUC k) infos))
      (SUM (MAP abi_member_head_size (TAKE (SUC k) ats))) dp mid = (out,en) /\
    window_phase ctx func st mid
      (window_alloca_sites func (frag_ids st en) UNION
        (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
      [(d,LENGTH (enc at (ListV avs)))] s u /\
    st.cs_next_var <= mid.cs_next_var /\
    window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en) /\
    (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d st en s` by
    (qpat_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` mp_tac >>
     simp_tac bool_ss [zero_members_inv_def] >> metis_tac[]) >>
  `fn_has_code st en func` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
  drule_all window_members_cons_context >> strip_tac >>
  `cs_extends ready mid /\ cs_extends mid en` by
    metis_tac[cs_extends_abi_encode_child, cj 3 cs_appends_abi_encode_mutual, cs_appends_def] >>
  `cs_extends st ready` by metis_tac[abi_encoder_emit_address_shape] >>
  `fn_has_code ready en func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all zero_member_source_prepare >> strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs k (Lit 0w) dst dp site slot
    0 0 d ready en t` by
    (qpat_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready en t` mp_tac >>
     simp_tac bool_ss [zero_members_inv_def] >> metis_tac[]) >>
  `k < LENGTH infos /\ EL k infos = (h0,h1,h2,h3) /\ DROP (SUC k) infos = rest` by
    metis_tac[zero_member_drop_cons] >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _` kall_tac >>
  `abi_encoder_admissible h0` by
    (`abi_encoder_admissible (AbiComplex infos)` by
       (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp_tac bool_ss [window_structural_members_inv_def, abi_encoder_window_pre_def] >> metis_tac[]) >>
     qpat_x_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     simp_tac bool_ss [abi_encoder_admissible_def, abi_encoder_members_admissible_every] >>
     simp_tac (srw_ss()) [EVERY_MEM] >>
     disch_then (qspec_then `(h0,h1,h2,h3)` mp_tac) >> simp[] >> metis_tac[MEM_EL]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==> site < ready.cs_next_id` by
    (qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready en t` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, window_member_cursor_def] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready mid) SUBSET window_alloca_sites func (frag_ids ready en) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid)) (window_alloca_sites func (frag_ids mid en)) /\
   (EXISTS (\(_,_,_,dyn). dyn) infos ==>
     site NOTIN window_alloca_sites func (frag_ids ready mid) /\
     DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
       (window_alloca_sites func (frag_ids mid en)))` by
    metis_tac[window_member_site_split] >>
  qpat_x_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` kall_tac >>
  qpat_x_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ st en s` kall_tac >>
  qpat_x_assum `cs_extends ready mid` kall_tac >>
  qpat_x_assum `cs_extends mid en` kall_tac >>
  qpat_x_assum `cs_extends st ready` kall_tac >>
  `?u ids outs. zero_members_inv ctx func infos at ats avs (SUC k) src dst dp site slot
      sb d mid en u /\ window_phase ctx func ready mid ids outs t u /\
    ids SUBSET (window_alloca_sites func (frag_ids ready en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})) /\
    EVERY (\(b,n). d <= b /\ b+n <= d+LENGTH (enc at (ListV avs))) outs /\
    (!R. (!i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
         !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32)` by
    suspend "child" >>
  suspend "compose"
QED

Resume zero_members_cons_run_sizes[child]:
  reverse (Cases_on `h3`)
  >- (`EXISTS (\(_,_,_,dyn). dyn) infos ==> site NOTIN window_alloca_sites func (frag_ids ready mid)` by metis_tac[] >>
      drule_all zero_member_static_step_run_sizes >> strip_tac >>
      qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid)`,
        `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),LENGTH (enc (EL k ats) (EL k avs)))]`] >>
      asm_rewrite_tac[] >>
      (conj_tac >- metis_tac[SUBSET_UNION, SUBSET_TRANS]) >>
      drule_all window_structural_members_inv_output_bounds >> strip_tac >>
      drule_all window_structural_members_inv_total_bounds >> strip_tac >>
      `~is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
      simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
      qpat_x_assum `~is_dynamic _ ==> _` drule >> decide_tac) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos` by
    (simp[EXISTS_MEM] >> qexists_tac `(h0,h1,h2,T)` >> simp[] >> metis_tac[MEM_EL]) >>
  `(window_alloca_sites func (frag_ids ready mid) UNION {site}) SUBSET
     (window_alloca_sites func (frag_ids ready en) UNION {site}) /\
   DISJOINT (window_alloca_sites func (frag_ids ready mid) UNION {site})
     (window_alloca_sites func (frag_ids mid en))` by
    metis_tac[SUBSET_UNION, SUBSET_TRANS, UNION_SUBSET] >>
  drule_all zero_member_dynamic_step_run_sizes >> strip_tac >>
  qexistsl_tac [`t'`, `window_alloca_sites func (frag_ids ready mid) UNION {site}`,
    `[(d+SUM (MAP abi_member_head_size (TAKE k ats)),32);
      (d+window_member_tail infos ats avs k,LENGTH (enc (EL k ats) (EL k avs)))]`] >>
  asm_rewrite_tac[] >>
  drule_all window_structural_members_inv_output_bounds >> strip_tac >>
  drule_all window_structural_members_inv_total_bounds >> strip_tac >>
  `is_dynamic (EL k ats)` by metis_tac[window_structural_members_inv_source] >>
  simp_tac (srw_ss()) [NoAsms, EVERY_DEF] >>
  qpat_x_assum `is_dynamic _ ==> _` drule >> strip_tac >> decide_tac
QED

Resume zero_members_cons_run_sizes[compose]:
  `!i. FLOOKUP t.vs_allocas i = FLOOKUP s.vs_allocas i` by
    (qpat_assum `window_phase _ _ st ready {} [] s t` mp_tac >>
     simp_tac bool_ss [window_phase_def, abi_encoder_registered_effect_def] >>
     simp_tac (srw_ss()) [NoAsms, NOT_IN_EMPTY] >> metis_tac[]) >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  `h1 = abi_member_head_size (EL k ats) /\ k < LENGTH ats` by
    (drule_all window_structural_members_inv_source >> strip_tac >>
     qpat_assum `window_structural_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_structural_members_inv_def, window_member_prefix_def] >> metis_tac[]) >>
  `abi_encoder_member_span (TAKE (SUC k) infos) = abi_encoder_member_span (TAKE k infos) + h2 /\
   SUM (MAP abi_member_head_size (TAKE (SUC k) ats)) =
     SUM (MAP abi_member_head_size (TAKE k ats)) + h1` by
    (rpt (qpat_x_assum `!R. _` kall_tac) >>
     simp[TAKE_SUC, TAKE1_DROP, abi_encoder_member_span_def, MAP_APPEND, SUM_APPEND]) >>
  `window_alloca_sites func (frag_ids ready en) SUBSET window_alloca_sites func (frag_ids st en) /\
   window_alloca_sites func (frag_ids mid en) SUBSET window_alloca_sites func (frag_ids st en)` by
    (simp_tac (srw_ss()) [window_alloca_sites_def, frag_ids_def, SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`mid`, `u`] >> asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!R. _` kall_tac) >>
  (conj_tac >- metis_tac[]) >>
  reverse conj_tac >- decide_tac >>
  irule window_phase_chain >>
  qexistsl_tac [`{}`, `[]`, `ready`, `ids`, `outs`, `t`] >>
  simp_tac (srw_ss()) [NoAsms, EMPTY_SUBSET, EVERY_DEF] >>
  asm_rewrite_tac[] >>
  (conj_tac >-
    (drule zero_member_envelope_frame >>
     simp_tac (srw_ss()) [NoAsms, EVERY_DEF])) >>
  qpat_x_assum `ids SUBSET _` mp_tac >>
  qpat_x_assum `window_alloca_sites func (frag_ids ready en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED

Finalise zero_members_cons_run_sizes

Theorem zero_members_remaining_run_sizes:
  !rest ctx func infos at ats avs k src dst dp site slot sb d st en s out.
  zero_members_inv ctx func infos at ats avs k src dst dp site slot
    sb d st en s /\ DROP k infos = rest /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> zero_strong_contract ei) /\
  compile_abi_encode_complex_elems dst src rest
    (abi_encoder_member_span (TAKE k infos))
    (SUM (MAP abi_member_head_size (TAKE k ats))) dp st = (out,en) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION
          (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
        [(d,LENGTH (enc at (ListV avs)))] s t /\
      zero_members_inv ctx func infos at ats avs (LENGTH infos) src dst dp site slot
        sb d en en t /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  Induct_on `rest`
  >- (rpt gen_tac >>
      simp_tac bool_ss [Once compile_abi_encode_child_def,
        comp_return_def, pairTheory.PAIR_EQ] >> strip_tac >>
      `k = LENGTH infos` by
        (qpat_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [zero_members_inv_def, window_structural_members_inv_def,
           window_member_prefix_def] >>
         strip_tac >> fs[DROP_EQ_NIL] >> decide_tac) >>
      gvs[] >> qexists_tac `s` >> asm_rewrite_tac[] >>
      irule window_phase_refl >>
      qpat_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [zero_members_inv_def, window_structural_members_inv_def,
        abi_encoder_window_pre_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  `zero_strong_contract h0` by metis_tac[MEM] >>
  drule_all zero_members_cons_run_sizes >> strip_tac >>
  `!ei az ms dyn. MEM (ei,az,ms,dyn) rest ==> zero_strong_contract ei` by metis_tac[MEM] >>
  first_x_assum drule_all >> strip_tac >>
  `!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
       !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32` by
    (gen_tac >> disch_tac >>
     qpat_x_assum `!R. _ ==> !i b sz. _ /\ FLOOKUP u.vs_allocas i = _ ==> _`
       (qspec_then `R` mp_tac) >> asm_rewrite_tac[] >> disch_tac >>
     qpat_x_assum `!R. _` (qspec_then `R` mp_tac) >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  rpt (qpat_x_assum `!R. _` kall_tac) >>
  irule window_phase_chain >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
    `[(d,LENGTH (enc at (ListV avs)))]`, `mid`,
    `window_alloca_sites func (frag_ids mid en) UNION
      (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {})`,
    `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `window_alloca_sites func (frag_ids mid en) SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF] >> metis_tac[]
QED

Theorem zero_members_initialized_run_sizes:
  abi_encoder_window_pre ctx func st en dst (Lit 0w) (AbiComplex infos) at
    (ListV avs) 0 0 d s /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  abi_encoder_tuple_type at ats /\
  LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
  window_member_head_size infos = head_lengths ats 0 /\
  window_member_cursor infos dp site slot 0 0 d
    (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_head_size infos)) /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> zero_strong_contract ei) /\
  compile_abi_encode_complex_elems dst src infos 0 0 dp st = (out,en) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION
          (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
        [(d,LENGTH (enc at (ListV avs)))] s t /\
      zero_members_inv ctx func infos at ats avs (LENGTH infos) src dst dp site slot
        sb d en en t /\
      mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs) /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `window_structural_members_inv ctx func infos at ats avs 0 (Lit 0w) dst dp site slot
     0 0 d st en s` by metis_tac[window_structural_members_inv_entry] >>
  `zero_members_inv ctx func infos at ats avs 0 src dst dp site slot sb d st en s` by
    simp[zero_members_inv_def] >>
  drule zero_members_remaining_run_sizes >>
  disch_then (qspec_then `infos` mp_tac) >>
  simp[abi_encoder_member_span_def] >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs)` by
    (irule window_structural_members_inv_complete >>
     qpat_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [zero_members_inv_def] >> metis_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[]
QED

Theorem zero_complex_initialized_run_sizes:
  abi_encoder_window_pre ctx func st en dst (Lit 0w) (AbiComplex infos) at
    (ListV avs) 0 0 d s /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  window_member_cursor infos dp site slot 0 0 d
    (LENGTH (enc at (ListV avs))) st s /\
  (EXISTS (\(_,_,_,dyn). dyn) infos ==>
    mem_word_at slot s.vs_memory = n2w (window_member_head_size infos)) /\
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> zero_strong_contract ei) /\
  compile_abi_encode_complex_elems dst src infos 0 0 dp st = (out,en) ==>
  ?t. window_phase ctx func st en
        (window_alloca_sites func (frag_ids st en) UNION
          (if EXISTS (\(_,_,_,dyn). dyn) infos then {site} else {}))
        [(d,LENGTH (enc at (ListV avs)))] s t /\
      mem_bytes_at d (LENGTH (enc at (ListV avs))) t.vs_memory = enc at (ListV avs) /\
      (EXISTS (\(_,_,_,dyn). dyn) infos ==>
        mem_word_at slot t.vs_memory = n2w (LENGTH (enc at (ListV avs)))) /\
      (!R. (!i b sz. i IN R /\ FLOOKUP s.vs_allocas i = SOME (b,sz) ==> sz = 32) ==>
           !i b sz. i IN R /\ FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32)
Proof
  strip_tac >>
  `abi_encoder_window_input (AbiComplex infos) at (ListV avs) 0 0 s.vs_memory` by
    fs[abi_encoder_window_pre_def] >>
  `?ats. abi_encoder_tuple_type at ats` by
    metis_tac[abi_encoder_window_complex_iff] >>
  drule_all window_complex_head_layout >> strip_tac >>
  drule_all zero_members_initialized_run_sizes >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_x_assum `!R. _` kall_tac >> strip_tac >>
  `LIST_REL abi_encoder_structural_valid ats avs` by
    metis_tac[window_complex_structural_members] >>
  `enc at (ListV avs) = enc (Tuple ats) (ListV avs)` by
    (fs[abi_encoder_tuple_type_def] >> gvs[Once enc_def, LET_THM]) >>
  `window_member_tail infos ats avs (LENGTH infos) = LENGTH (enc at (ListV avs))` by
    (`TAKE (LENGTH infos) ats = ats /\ TAKE (LENGTH infos) avs = avs` by
       metis_tac[TAKE_LENGTH_ID] >>
     drule window_structural_member_tuple_length >>
     pure_asm_rewrite_tac[window_member_tail_def] >> metis_tac[]) >>
  qpat_x_assum `zero_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [zero_members_inv_def, window_structural_members_inv_def] >> metis_tac[]
QED

Theorem zero_complex_strong_contract:
  (!ei az ms dyn. MEM (ei,az,ms,dyn) infos ==> zero_strong_contract ei) ==>
  zero_strong_contract (AbiComplex infos)
Proof
  strip_tac >> simp_tac bool_ss [zero_strong_contract_def] >>
  rpt gen_tac >> strip_tac >>
  drule zero_window_pre_ghost >> strip_tac >>
  `eval_operand src s = SOME (n2w sb) /\
    (!x. src = Var x ==> not_fresh_at st x)` by fs[zero_window_pre_def] >>
  qpat_x_assum `zero_window_pre _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `abi_encoder_window_input (AbiComplex infos) at av 0 0 s.vs_memory` by
    fs[abi_encoder_window_pre_def] >>
  `?ats avs. av = ListV avs /\ abi_encoder_tuple_type at ats` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> metis_tac[]) >>
  gvs[] >> Cases_on `infos`
  >- suspend "empty" >>
  rename1 `h::rest` >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, LET_THM] >>
  Cases_on `EXISTS (\(_,_,_,dyn). dyn) (h::rest)`
  >- suspend "dynamic" >>
  suspend "static"
QED

Resume zero_complex_strong_contract[empty]:
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at (ListV avs) = []` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_complex_iff] >> strip_tac >>
     gvs[abi_encoder_tuple_type_def, enc_def, LET_THM, REV_DEF]) >>
  qexists_tac `s` >> irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [NoAsms, LENGTH, mem_bytes_at_def, eval_operand_def] >>
  metis_tac[window_pre_sites, window_phase_refl, abi_encoder_window_pre_def]
QED

Resume zero_complex_strong_contract[static]:
  asm_rewrite_tac[] >>
  qmatch_asmsub_abbrev_tac `AbiComplex infos` >>
  simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_abi_encode_complex_elems dst src infos 0 0 (Lit 0w) st` >>
  rename1 `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = (ignored,en)` >>
  asm_rewrite_tac[GSYM window_member_head_size_def] >> strip_tac >> gvs[] >>
  `~EXISTS (\(_,_,_,dyn). dyn) infos` by
    (qpat_assum `EVERY _ infos` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `window_member_cursor infos (Lit 0w) 0 0 0 0 d
      (LENGTH (enc at (ListV avs))) st s` by simp[window_member_cursor_def] >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
      mem_word_at 0 s.vs_memory = n2w (window_member_head_size infos)` by simp[] >>
  drule_all zero_complex_initialized_run_sizes >> strip_tac >>
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
  qexists_tac `t` >> irule window_complex_phase_result >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >>
  qpat_x_assum `window_phase _ _ _ _ _ _ _ _` mp_tac >>
  pure_asm_rewrite_tac[] >> simp_tac (srw_ss()) [UNION_EMPTY]
QED

Resume zero_complex_strong_contract[dynamic]:
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
  drule_all window_complex_initialize_phase_sizes >> strip_tac >>
  `abi_encoder_window_pre ctx func ready load dst (Lit 0w) (AbiComplex infos) at
     (ListV avs) 0 0 d u` by
    (qpat_assum `abi_encoder_window_pre _ _ ready st' _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     asm_rewrite_tac[] >>
     `cs_extends ready load /\ cs_extends load st' /\ load.cs_next_id <= st'.cs_next_id` by
       (qpat_assum `ci_mono ready load` mp_tac >>
        qpat_assum `ci_mono load st'` mp_tac >>
        simp_tac bool_ss [ci_mono_def] >> metis_tac[]) >>
     (conj_tac >- metis_tac[fn_has_code_split]) >>
     rpt gen_tac >> strip_tac >>
     `inst.inst_id IN frag_ids ready st'` by
       (qpat_x_assum `inst.inst_id IN frag_ids ready load` mp_tac >>
        simp_tac (srw_ss()) [NoAsms, frag_ids_def] >> decide_tac) >>
     qpat_x_assum `!inst b sz. _` drule_all >> simp_tac bool_ss []) >>
  `ci_mono st allocated /\ ci_mono allocated ready` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, pairTheory.SND] >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_id <= ready.cs_next_id /\
   load.cs_next_id <= st'.cs_next_id` by
    (qpat_assum `ci_mono st allocated` mp_tac >>
     qpat_assum `ci_mono allocated ready` mp_tac >>
     qpat_assum `ci_mono load st'` mp_tac >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `eval_operand src u = SOME (n2w sb) /\
   (!x. src = Var x ==> not_fresh_at ready x)` by
    (conj_tac
     >- (irule window_phase_eval >>
         qexistsl_tac [`ctx`, `ready`, `func`, `{st.cs_next_id}`, `[]`, `s`, `st`] >>
         asm_rewrite_tac[] >>
         qpat_assum `window_phase _ _ st ready _ _ s u` mp_tac >>
         simp_tac bool_ss [window_phase_def] >> metis_tac[]) >>
     metis_tac[not_fresh_at_mono]) >>
  `EXISTS (\(_,_,_,dyn). dyn) infos ==>
     mem_word_at slot u.vs_memory = n2w (window_member_head_size infos)` by asm_rewrite_tac[] >>
  drule_all zero_complex_initialized_run_sizes >> strip_tac >>
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
  `ready.cs_next_var <= load.cs_next_var /\ ready.cs_next_id <= load.cs_next_id` by
    (qpat_assum `ci_mono ready load` mp_tac >> simp_tac bool_ss [ci_mono_def] >> metis_tac[]) >>
  `window_member_cursor infos buf.buf_operand st.cs_next_id slot 0 0 d
     (LENGTH (enc at (ListV avs))) load t` by
    (irule window_member_cursor_phase >> goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  `eval_operand buf.buf_operand t = SOME (n2w slot) /\ slot < dimword (:256)` by
    (qpat_assum `window_member_cursor _ _ _ _ _ _ _ _ load t` mp_tac >>
     simp_tac bool_ss [window_member_cursor_def] >> asm_rewrite_tac[] >> metis_tac[]) >>
  `window_alloca_sites func (frag_ids ready load) SUBSET
   window_alloca_sites func (frag_ids st st')` by
    (simp_tac (srw_ss()) [NoAsms, window_alloca_sites_def, SUBSET_DEF, frag_ids_def] >>
     rpt strip_tac >> decide_tac) >>
  qpat_x_assum `window_phase _ _ ready load _ _ _ _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  `window_phase ctx func st load (window_alloca_sites func (frag_ids st st'))
    [(d,LENGTH (enc at (ListV avs)))] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{st.cs_next_id}`, `[]`, `ready`,
       `window_alloca_sites func (frag_ids ready load) UNION {st.cs_next_id}`,
       `[(d,LENGTH (enc at (ListV avs)))]`, `u`] >>
     asm_rewrite_tac[] >> simp[EVERY_DEF, UNION_SUBSET, INSERT_SUBSET]) >>
  irule window_complex_finish_load >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[SUBSET_REFL] >>
  `fn_has_code load st' func` by
    (qpat_assum `ci_mono ready load` mp_tac >>
     qpat_assum `ci_mono load st'` mp_tac >>
     simp_tac bool_ss [ci_mono_def] >> rpt strip_tac >>
     `fn_has_code ready st' func` by metis_tac[abi_encoder_window_pre_def] >>
     metis_tac[fn_has_code_split]) >>
  qexistsl_tac [`buf.buf_operand`, `slot`] >>
  asm_rewrite_tac[] >> conj_tac >- decide_tac >> metis_tac[]
QED
Finalise zero_complex_strong_contract

Theorem zero_read_plan_strong_contract:
  !ei. zero_read_plan ei ==> zero_strong_contract ei
Proof
  ho_match_mp_tac zero_read_plan_ind >>
  conj_tac >- ACCEPT_TAC zero_copy_strong_contract >>
  rpt strip_tac >> irule zero_complex_strong_contract >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem zero_window_strong_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  zero_window_pre ctx func st st' dst src ei at av sb d s ==>
  ?t. window_strong_result ctx func st st' out at av d s t
Proof
  strip_tac >>
  `zero_read_plan ei` by
    (irule zero_window_read_plan >>
     fs[zero_window_pre_def] >> metis_tac[]) >>
  drule zero_read_plan_strong_contract >>
  simp_tac bool_ss [zero_strong_contract_def] >>
  disch_then drule_all >> simp[]
QED

Theorem zero_window_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  zero_window_pre ctx func st st' dst src ei at av sb d s ==>
  ?t. abi_encoder_window_result ctx func st st' out at av d s t
Proof
  metis_tac[zero_window_strong_run, window_strong_result_public]
QED
