(* Member execution retains its actual child footprint and ambient readiness
   at one operational endpoint. *)
Theory entryReachBodyCanonicalLocalMembers
Ancestors
  entryReachBodyCanonicalProducerBridge entryReachBodyCanonicalMemberEntry
  entryReachBodyCanonicalMembers entryReachBodyCanonicalArrayChild
  entryReachBodyEmptyMember entryReachBodyMemberPrefix entryReachBodyMemberSetup
  entryReachBodyOwnedRegion entryReachBodyScratchSites
  abiDecoderMembers abiDecoderMemberInfos abiDecoderCoherence
  abiDecoderMemberSetup abiDecoderMemberBody abiDecoderMemberCons
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
  array_child_producer ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
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
  qpat_x_assum `array_child_producer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [array_child_producer_def]) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`sb + abi_tuple_child_offset
    (MAP (vyper_to_abi_type env) fulltys) fullavs (LENGTH pretys)`, `d+vo`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
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
  array_child_producer ce env ty tv av v ctx fn oid root extent sites b cap site limit_st /\
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
