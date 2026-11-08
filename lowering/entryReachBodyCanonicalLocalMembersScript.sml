(* Member execution retains its actual child footprint and ambient readiness
   at one operational endpoint. *)
Theory entryReachBodyCanonicalLocalMembers
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyCertifiedProducer
  entryReachBodyCanonicalProducerBridge entryReachBodyCanonicalMemberEntry
  entryReachBodyCanonicalMembers entryReachBodyCanonicalArrayChild
  entryReachBodyEmptyMember entryReachBodyMemberPrefix entryReachBodyMemberSetup
  entryReachBodyOwnedRegion entryReachBodyScratchSites
  abiDecoderMembers abiDecoderMemberInfos abiDecoderCoherence
  abiDecoderMemberSetup abiDecoderMemberBody abiDecoderMemberCons
  abiDecoderFixedMemory abiDecoderFixedInputs abiCanonicalHeadSize vyperTypeABI vyperABI
  abiDecoderContract abiDecoderReentry abiDecoderCode abiDecoderAllocation
  abiDecoderDynamicLoopSetup abiDecoderOffset
  abiEncoderRegisteredEffect abiEncoderWindowContract
  entryReachBodyOperationalPath entryReachBodyExactArrayLoop
  entryReachBodyScratchSet abiAllocationHistory allocaFrontierBound
  abiEncoder compileEnv emitHelper valueEncodingTyping valueEncoding
  list rich_list arithmetic pred_set


(* This is not an ambient-only result adapter: the local footprint is kept
   in array_child_result throughout the setup/child composition. *)
Theorem entry_local_member_nonempty[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  type_to_abi_dec_info ce.ce_struct_fields ce ty <> DecComplex T [] /\
  entry_certified_child_producer cert ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
  cert last /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ fn_has_code st mid fn /\ fn_has_code mid last fn /\
  abi_decoder_code mid last /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET sites /\
  oid NOTIN sites /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. array_child_result ctx fn oid root extent sites
      (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      b cap site limit_st st last (d+vo) tv v s t
Proof
  strip_tac >>
  qpat_assum `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_semantics_def]) >>
  `dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty) =
     is_dynamic (vyper_to_abi_type env ty)` by
    (irule entry_nonempty_member_offset >> asm_rewrite_tac[] >>
     qexists_tac `tv` >> fs[abi_decoder_members_def, Excl "enc_def"]) >>
  qpat_assum `abi_decoder_members _ _ _ pretys _ _ _`
    (mp_then (Pos hd) mp_tac entry_canonical_member_owned_entry) >>
  disch_then (drule_at (Pat `abi_decoder_members _ _ _ (_::_) (_::_) (_::_) (_::_)`)) >>
  disch_then (drule_at (Pat `abi_decode_member_setup _ _ _ _ _ _ _ _ = _`)) >>
  simp_tac bool_ss [] >>
  qpat_assum `fulltys = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `fullavs = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)
    entry_certified_child_apply >>
  disch_then (drule_at (Pat `entry_certified_child_producer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by
    (drule abi_decode_member_setup_counters >> simp[]) >>
  qpat_x_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [array_child_result_def]) >>
  `entry_decode_path ctx fn s t` by
    (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  qmatch_asmsub_abbrev_tac `abi_encoder_registered_effect ids _ u t` >>
  `abi_encoder_registered_effect ids [(d+vo,type_memory_size tv)] s u` by
    fs[abi_encoder_registered_effect_def, abi_decoder_address_frame_def,
       entry_loop_fields_def] >>
  `abi_encoder_registered_effect ids [(d+vo,type_memory_size tv)] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  unabbrev_all_tac >> qpat_x_assum `vo = _` SUBST_ALL_TAC >>
  qexists_tac `t` >> simp[array_child_result_def, Excl "enc_def"] >>
  rpt strip_tac >>
  `eval_operand op u = SOME w` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live mid.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED

(* Unlike ambient traversal's semantic step, this boundary retains the
   actual local effect, widened only in destination extent, at the same t. *)
Theorem local_member_semantic_step[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) s /\
  array_child_result ctx fn oid root extent sites ids b cap site limit_st
    st last (d + SUM (MAP (type_memory_bytes ce) pretys)) tv v s t /\
  ids SUBSET sites /\ oid NOTIN sites ==>
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])
    tys tvs avs vs t /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) t /\
  abi_encoder_registered_effect ids [(d,SUM (MAP (type_memory_bytes ce) fulltys))] s t
Proof
  simp_tac bool_ss [canonical_members_semantics_def, array_child_result_def] >> strip_tac >>
  `oid NOTIN ids` by metis_tac[SUBSET_DEF] >>
  `LIST_REL val_wf pretvs prevs` by
    (qpat_assum `abi_decoder_members _ _ _ pretys _ _ _`
       (mp_then Any mp_tac abi_decoder_members_relations) >>
     strip_tac >> fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule (cj 1 value_has_type_val_wf) >> first_x_assum irule >> simp[]) >>
  `abi_decoder_members ce env ce.ce_struct_fields [ty] [tv] [av] [v] /\
   abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs` by fs[abi_decoder_members_def] >>
  `abi_decoder_members ce env ce.ce_struct_fields
     (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v])` by
    (qpat_assum `abi_decoder_members _ _ _ pretys _ _ _`
       (mp_then Any mp_tac abi_decoder_members_lengths) >>
     strip_tac >> simp[abi_decoder_members_append]) >>
  qpat_assum `abi_decoder_members _ _ _ pretys _ _ _`
       (mp_then Any mp_tac abi_decoder_members_relations) >> strip_tac >>
  qpat_assum `abi_decoder_members _ _ _ pretys _ _ _`
       (mp_then Any mp_tac abi_decoder_members_lengths) >> strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by fs[abi_decoder_members_def] >>
  drule abi_decoder_coherent_header >> simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `tuple_in_memory (prevs ++ [v]) (pretvs ++ [tv]) d t.vs_memory` by
    (irule entry_member_memory_extend >> asm_rewrite_tac[] >>
     qpat_assum `abi_encoder_registered_effect ids _ s t` (irule_at Any) >>
     qpat_assum `entry_owned_region _ _ _ d _ s` (irule_at Any) >>
     asm_rewrite_tac[] >> simp[MAP_APPEND, SUM_APPEND]) >>
  `abi_encoder_registered_effect ids [(d,SUM (MAP (type_memory_bytes ce) fulltys))] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect ids _ s t` (irule_at Any) >>
     simp[] >> rpt strip_tac >> gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"]) >>
  `entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) t` by
    (irule entry_owned_region_preserved >>
     qpat_assum `abi_encoder_registered_effect ids [(d,_)] s t` (irule_at Any) >>
     qpat_assum `entry_owned_region _ _ _ d _ s` (irule_at Any) >> simp[]) >>
  `abi_decode_source CALLDATALOAD t = abi_decode_source CALLDATALOAD s` by
    fs[entry_loop_fields_def, abi_decode_source_def] >>
  asm_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` mp_tac >>
  gvs[SUM_APPEND, Excl "enc_def"]
QED

Theorem entry_local_member_decode[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  entry_certified_child_producer cert ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
  cert last /\
  ao = SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)) /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  abi_decode_member_setup dst src CALLDATALOAD (Lit 0w)
    (dec_info_needs_offset (type_to_abi_dec_info ce.ce_struct_fields ce ty)) ao vo st = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) mid = ((),last) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ fn_has_code st mid fn /\ fn_has_code mid last fn /\
  fn_has_code st last fn /\ abi_decoder_code mid last /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET sites /\
  oid NOTIN sites /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. array_child_result ctx fn oid root extent sites
      (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      b cap site limit_st st last (d+vo) tv v s t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v]) tys tvs avs vs t /\
    entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) t
Proof
  strip_tac >>
  `?t. array_child_result ctx fn oid root extent sites
      (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      b cap site limit_st st last (d+vo) tv v s t` by
    (Cases_on `type_to_abi_dec_info ce.ce_struct_fields ce ty = DecComplex T []`
     >- ( `abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
            abi_decoder_metadata ce env ty tv (DecComplex T []) av v` by
            fs[canonical_members_semantics_def, abi_decoder_members_def] >>
          mp_tac (Q.INST [`ei` |-> `DecComplex T []`] entry_empty_dynamic_member_endpoint) >>
          (impl_tac >- gvs[Excl "enc_def"]) >> strip_tac >>
          `entry_scratch_ready sites b cap u /\
           entry_owned_region oid root extent d (SUM (MAP (type_memory_bytes ce) fulltys)) u /\
           alloca_inv u /\ abi_alloca_history (fn_insts fn) u /\
           alloca_frontier_inv ctx fn site u` by
            (irule entry_member_resource_frame >> qexists_tac `s` >> simp[]) >>
          `entry_owned_region oid root extent (d+vo) (type_memory_size tv) u` by
            (gvs[canonical_members_semantics_def, entry_owned_region_def,
                 MAP_APPEND, SUM_APPEND, Excl "enc_def"] >> decide_tac) >>
          qexists_tac `u` >>
          gvs[array_child_result_def, abi_encoder_registered_effect_def,
              abi_decoder_address_frame_def, entry_loop_fields_def, Excl "enc_def"]) >>
     drule_all entry_local_member_nonempty >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qpat_x_assum `vo = _` SUBST_ALL_TAC >>
  drule_all local_member_semantic_step >> simp[]
QED

Theorem local_member_step_frame[local]:
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d n st s /\
  array_child_result ctx fn oid root extent sites ids b cap site limit_st
    st last childd tv v s t /\
  entry_owned_region oid root extent d n t /\
  st.cs_next_var <= last.cs_next_var /\ ids SUBSET wide /\ wide SUBSET sites /\
  d <= childd /\ childd+type_memory_size tv <= d+n ==>
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d n last t /\ canonical_members_effect ctx fn sites d n st s t /\
  abi_encoder_registered_effect wide [(d,n)] s t
Proof
  simp_tac bool_ss [canonical_members_frame_def, array_child_result_def,
    canonical_members_effect_def] >> strip_tac >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[] >>
  `abi_decoder_operand_live last.cs_next_var src /\
   abi_decoder_operand_live last.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `abi_encoder_registered_effect wide [(d,n)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect ids _ s t` (irule_at Any) >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect sites [(d,n)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect wide _ s t` (irule_at Any) >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem local_members_interval[local]:
  first <= child_first /\ child_last <= last /\
  oid NOTIN abi_decoder_ids first last /\
  window_alloca_sites fn (abi_decoder_ids first last) SUBSET sites ==>
  oid NOTIN abi_decoder_ids child_first child_last /\
  window_alloca_sites fn (abi_decoder_ids child_first child_last) SUBSET sites
Proof
  strip_tac >>
  `window_alloca_sites fn (abi_decoder_ids child_first child_last) SUBSET
    window_alloca_sites fn (abi_decoder_ids first last)` by
    (irule entry_decoder_sites_interval_subset >> simp[]) >>
  conj_tac >- (fs[abi_decoder_ids_def] >> decide_tac) >>
  metis_tac[SUBSET_TRANS]
QED

Theorem local_members_child_bounds[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s ==>
  type_memory_size tv = type_memory_bytes ce ty /\
  abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty) /\
  d + SUM (MAP (type_memory_bytes ce) pretys) + type_memory_size tv <=
    d + SUM (MAP (type_memory_bytes ce) fulltys)
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by fs[abi_decoder_members_def] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  gvs[MAP_APPEND, SUM_APPEND, Excl "enc_def"]
QED

Theorem local_members_cons_step[local]:
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs (ty::tys) (tv::tvs) (av::avs) (v::vs) s /\
  entry_certified_child_producer cert ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
  cert last /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce (ty::tys))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?mid t.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
      (abi_decoder_member_infos ce.ce_struct_fields ce tys)
      (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (pretys ++ [ty]))))
      (SUM (MAP (type_memory_bytes ce) (pretys ++ [ty]))) mid = ((),last) /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) mid t /\
    canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
      (pretys ++ [ty]) (pretvs ++ [tv]) (preavs ++ [av]) (prevs ++ [v]) tys tvs avs vs t /\
    canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) fulltys)) st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) fulltys))] s t /\
    st.cs_next_var <= mid.cs_next_var /\ st.cs_next_id <= mid.cs_next_id /\
    mid.cs_next_id <= last.cs_next_id /\ fn_has_code mid last fn
Proof
  strip_tac >> drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  `cert end_st` by
    (qpat_x_assum `!a z elems ao vo. _`
       (drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ = _`)) >>
     disch_then drule_all >> simp[]) >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `oid NOTIN abi_decoder_ids middle.cs_next_id end_st.cs_next_id /\
   window_alloca_sites fn (abi_decoder_ids middle.cs_next_id end_st.cs_next_id) SUBSET sites` by
    (irule local_members_interval >>
     qexistsl_tac [`st.cs_next_id`, `last.cs_next_id`] >> simp[]) >>
  `abi_decoder_code middle end_st` by (drule_all abi_decoder_to_buf_code >> simp[]) >>
  `end_st.cs_next_var <= limit_st.cs_next_var /\
   middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  qpat_assum `canonical_members_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [canonical_members_frame_def]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`) entry_local_member_decode >>
  disch_then (drule_at (Pat `abi_decode_member_setup _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule local_members_child_bounds >> strip_tac >>
  `window_alloca_sites fn (abi_decoder_ids middle.cs_next_id end_st.cs_next_id) SUBSET
   window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` by
    (irule entry_decoder_sites_interval_subset >> simp[]) >>
  drule_at (Pat `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`) local_member_step_frame >>
  disch_then (qspec_then `window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` mp_tac) >>
  disch_then (drule_at (Pat `canonical_members_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`end_st`, `t`] >> asm_rewrite_tac[] >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ end_st = _` mp_tac >>
  simp[MAP_APPEND, SUM_APPEND]
QED

Theorem local_members_effect_trans[local]:
  canonical_members_effect ctx fn sites d n st s u /\
  canonical_members_effect ctx fn sites d n mid u t /\
  st.cs_next_var <= mid.cs_next_var ==>
  canonical_members_effect ctx fn sites d n st s t
Proof
  simp_tac bool_ss [canonical_members_effect_def] >> strip_tac >>
  `entry_decode_path ctx fn s t` by
    (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  `abi_encoder_registered_effect sites [(d,n)] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `eval_operand op u = SOME w` by metis_tac[] >>
  `abi_decoder_operand_live mid.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem local_members_suffix_lengths[local]:
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs tys tvs avs vs s ==>
  LENGTH tvs = LENGTH tys /\ LENGTH avs = LENGTH tys /\ LENGTH vs = LENGTH tys
Proof
  simp_tac bool_ss [canonical_members_semantics_def] >> strip_tac >>
  drule_at (Pat `abi_decoder_members _ _ _ tys tvs avs vs`) abi_decoder_members_lengths >> simp[]
QED

Theorem local_members_suffix[local]:
  !tys tvs avs vs pretys pretvs preavs prevs st last s.
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  canonical_members_semantics ce env fulltys fulltvs fullavs fullvs sb d
    pretys pretvs preavs prevs tys tvs avs vs s /\
  (!i. i < LENGTH tys ==> entry_certified_child_producer cert ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce tys)
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) fulltys)) (ListV fullavs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) fulltys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) fulltys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) fulltys)) last t /\
    tuple_in_memory fullvs fulltvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) fulltys))] s t
Proof
  Induct_on `tys` >> rpt gen_tac >> strip_tac
  >- (drule local_members_suffix_lengths >> simp[] >> strip_tac >> gvs[] >>
      fs[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def, comp_return_def] >>
      qexists_tac `s` >>
      gvs[canonical_members_effect_def, entry_decode_path_refl, entry_loop_fields_def,
          abi_encoder_registered_effect_refl, canonical_members_semantics_def, Excl "enc_def"]) >>
  drule local_members_suffix_lengths >> strip_tac >>
  Cases_on `tvs` >- gvs[] >> Cases_on `avs` >- gvs[] >> Cases_on `vs` >- gvs[] >>
  `entry_certified_child_producer cert ce env h h' h'' h''' ctx fn oid root extent sites b cap site limit_st` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all local_members_cons_step >> strip_tac >>
  `!i. i < LENGTH tys ==> entry_certified_child_producer cert ce env
    (EL i tys) (EL i t) (EL i t') (EL i t'')
    ctx fn oid root extent sites b cap site limit_st` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH (h::tys) ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
  `oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
   window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET sites` by
    (irule local_members_interval >>
     qexistsl_tac [`st.cs_next_id`, `last.cs_next_id`] >> simp[]) >>
  qpat_x_assum `!tvs avs vs pretys pretvs preavs prevs st last s. _`
    (drule_at (Pat `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule_all >> strip_tac >>
  `window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) SUBSET
   window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` by
    (irule entry_decoder_sites_interval_subset >> simp[]) >>
  `abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) fulltys))] t''' t''''` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect _ _ t''' t''''` (irule_at Any) >> simp[]) >>
  qexists_tac `t''''` >> asm_rewrite_tac[] >> conj_tac
  >- (irule local_members_effect_trans >> goal_assum (drule_at Any) >> simp[]) >>
  irule abi_encoder_registered_effect_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem entry_certified_local_members_endpoint:
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> entry_certified_child_producer cert ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce tys) 0 0 st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t
Proof
  strip_tac >>
  `canonical_members_semantics ce env tys tvs avs vs sb d
     [] [] [] [] tys tvs avs vs s` by
    simp[canonical_members_semantics_def, abi_decoder_members_def, val_in_memory_def] >>
  drule_at (Pat `canonical_members_semantics _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    local_members_suffix >>
  simp_tac bool_ss [MAP, SUM] >> disch_then drule_all >> simp[]
QED

Theorem entry_canonical_local_members_endpoint:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> array_child_producer ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w)
    (abi_decoder_member_infos ce.ce_struct_fields ce tys) 0 0 st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`cert` |-> `\z. T`] entry_certified_local_members_endpoint) >>
  simp_tac bool_ss [entry_certified_child_unconditional] >>
  disch_then drule_all >> simp[]
QED

Theorem entry_certified_local_complex_endpoint:
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> entry_certified_child_producer cert ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [Once compile_abi_decode_to_buf_def, LET_THM]) >>
  drule_all entry_certified_local_members_endpoint >> simp[]
QED

Theorem entry_certified_local_fixed_array_endpoint:
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  abi_decoder_metadata ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av /\
  (!avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH vs = n /\ abi_decoder_members ce env ce.ce_struct_fields
      (REPLICATE n ty) (REPLICATE n tv) avs vs ==>
    !i. i < n ==> entry_certified_child_producer cert ce env ty tv (EL i avs) (EL i vs)
      ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Fixed n))) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (type_memory_bytes ce (ArrayT ty (Fixed n))) st s /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (type_memory_bytes ce (ArrayT ty (Fixed n))) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (type_memory_bytes ce (ArrayT ty (Fixed n))) last t /\
    val_in_memory (ArrayTV tv (Fixed n)) v d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,type_memory_bytes ce (ArrayT ty (Fixed n)))] s t
Proof
  strip_tac >> drule_all abi_decoder_fixed_array_values >> strip_tac >>
  `type_memory_bytes ce (ArrayT ty (Fixed n)) =
    SUM (MAP (type_memory_bytes ce) (REPLICATE n ty))` by
    simp[Once type_memory_bytes_def, map_replicate, SUM_REPLICATE] >>
  `!i. i < LENGTH (REPLICATE n ty) ==> entry_certified_child_producer cert ce env
    (EL i (REPLICATE n ty)) (EL i (REPLICATE n tv)) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st` by
    (simp[] >> rpt strip_tac >> simp[EL_REPLICATE] >>
     qpat_x_assum `!avs vs. _` drule_all >> simp[]) >>
  gvs[abi_decoder_fixed_array_infos, Once vyper_to_abi_type_def,
      canonical_array_tuple, map_replicate, Excl "enc_def"] >>
  drule_at (Pat `abi_decoder_members _ _ _ _ _ _ _`) entry_certified_local_complex_endpoint >>
  simp[map_replicate, SUM_REPLICATE, Excl "enc_def"] >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  irule abi_decoder_fixed_array_memory >> simp[]
QED

(* The established unconditional interfaces are the trivial-certificate cases. *)
Theorem entry_canonical_local_complex_endpoint:
  abi_decoder_members ce env ce.ce_struct_fields tys tvs avs vs /\
  mem_bytes_at sb
    (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) =
    enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
  (!i. i < LENGTH tys ==> array_child_producer ce env
    (EL i tys) (EL i tvs) (EL i avs) (EL i vs)
    ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) st s /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) < dimword (:256) /\
  d + SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (SUM (MAP (type_memory_bytes ce) tys)) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (SUM (MAP (type_memory_bytes ce) tys)) last t /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,SUM (MAP (type_memory_bytes ce) tys))] s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`cert` |-> `\z. T`] entry_certified_local_complex_endpoint) >>
  simp_tac bool_ss [entry_certified_child_unconditional] >>
  disch_then drule_all >> simp[]
QED

Theorem entry_canonical_local_fixed_array_endpoint:
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) /\
  abi_decoder_metadata ce env (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n)) di av v /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av /\
  (!avs vs. av = ListV avs /\
    v = ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs)) /\
    LENGTH vs = n /\ abi_decoder_members ce env ce.ce_struct_fields
      (REPLICATE n ty) (REPLICATE n tv) avs vs ==>
    !i. i < n ==> array_child_producer ce env ty tv (EL i avs) (EL i vs)
      ctx fn oid root extent sites b cap site limit_st) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Fixed n))) st = ((),last) /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d (type_memory_bytes ce (ArrayT ty (Fixed n))) st s /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Fixed n))) av) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Fixed n)) < dimword (:256) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\ oid NOTIN sites /\
  oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. canonical_members_effect ctx fn sites d (type_memory_bytes ce (ArrayT ty (Fixed n))) st s t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d (type_memory_bytes ce (ArrayT ty (Fixed n))) last t /\
    val_in_memory (ArrayTV tv (Fixed n)) v d t.vs_memory /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,type_memory_bytes ce (ArrayT ty (Fixed n)))] s t
Proof
  strip_tac >>
  mp_tac (Q.INST [`cert` |-> `\z. T`] entry_certified_local_fixed_array_endpoint) >>
  simp_tac bool_ss [entry_certified_child_unconditional] >>
  disch_then drule_all >> simp[]
QED
