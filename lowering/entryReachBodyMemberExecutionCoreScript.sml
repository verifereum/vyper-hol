(* Resource and execution composition independent of member semantics. *)
Theory entryReachBodyMemberExecutionCore
Ancestors
  entryReachBodyCanonicalMembers entryReachBodyCanonicalArrayChild
  entryReachBodyOwnedRegion abiEncoderRegisteredEffect
  entryReachBodyOperationalPath entryReachBodyExactArrayLoop
  abiDecoderContract abiDecoderReentry abiDecoderAllocation
  abiEncoderWindowContract abiAllocationHistory allocaFrontierBound
  entryReachBodyScratchSet abiDecoderDynamicLoopSetup
  abiDecoderMemberCons abiDecoderMemberBody abiDecoderMemberInfos
  abiDecoderMemberSetup entryReachBodyScratchSites abiDecoderCode
  abiEncoder compileEnv emitHelper valueEncoding list rich_list arithmetic pred_set

Theorem entry_members_effect_refl:
  canonical_members_effect ctx fn sites d n st s s
Proof
  simp[canonical_members_effect_def, entry_decode_path_refl,
    entry_loop_fields_def, abi_encoder_registered_effect_refl]
QED

Theorem entry_members_effect_trans:
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

Theorem entry_members_resource_advance:
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  array_child_result ctx fn oid root extent sites ids b cap site limit_st
    st next cell tv v s t /\
  st.cs_next_var <= next.cs_next_var /\ ids SUBSET wide /\ wide SUBSET sites /\
  oid NOTIN sites /\ d <= cell /\ cell + type_memory_size tv <= d + outsz ==>
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz next t /\
  canonical_members_effect ctx fn sites d outsz st s t /\
  abi_encoder_registered_effect wide [(d,outsz)] s t
Proof
  simp_tac bool_ss [canonical_members_frame_def, array_child_result_def,
    canonical_members_effect_def] >> strip_tac >>
  `oid NOTIN ids` by metis_tac[SUBSET_DEF] >>
  `entry_owned_region oid root extent d outsz t` by
    (irule entry_owned_region_preserved >>
     qpat_assum `abi_encoder_registered_effect ids _ s t` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  `abi_encoder_registered_effect wide [(d,outsz)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect ids _ s t` (irule_at Any) >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect sites [(d,outsz)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect wide _ s t` (irule_at Any) >> simp[]) >>
  `eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[] >>
  `abi_decoder_operand_live next.cs_next_var src /\
   abi_decoder_operand_live next.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  asm_rewrite_tac[]
QED

(* The callback owns semantics; this contract exposes actual compiler phases,
   the suffix certificate, and the containing function's resource window. *)
Definition entry_members_callback_def:
  entry_members_callback cursor cert sf ce ctx fn oid root extent sites b cap site
    limit_st dst src sb d outsz <=>
  !pre ty tys ao vo st ops middle next last s.
    cursor pre (ty::tys) st s /\
    ao = SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre) /\
    vo = SUM (MAP (type_memory_bytes ce) pre) /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d outsz st s /\
    abi_decode_member_setup dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (dec_info_needs_offset (type_to_abi_dec_info sf ce ty)) ao vo st = (ops,middle) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),next) /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (abi_decoder_member_infos sf ce tys)
      (ao + abi_embedded_static_size ce.ce_struct_fields ty)
      (vo + type_memory_bytes ce ty) next = ((),last) /\
    cert next /\ fn_has_code st middle fn /\ fn_has_code middle next fn /\
    fn_has_code st next fn /\ fn_has_code next last fn /\
    abi_decoder_code middle next /\
    st.cs_next_id < middle.cs_next_id /\ middle.cs_next_id <= next.cs_next_id /\
    next.cs_next_id <= last.cs_next_id /\
    st.cs_next_var <= middle.cs_next_var /\ middle.cs_next_var <= next.cs_next_var /\
    next.cs_next_var <= last.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
    fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword(:256) /\
    oid NOTIN sites /\ oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
    window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
    ?t. cursor (pre ++ [ty]) tys next t /\
      canonical_members_frame ctx fn oid root extent sites b cap site limit_st
        dst src sb d outsz next t /\
      canonical_members_effect ctx fn sites d outsz st s t /\
      abi_encoder_registered_effect
        (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
        [(d,outsz)] s t
End

Theorem entry_members_core_cons[local]:
  entry_members_callback cursor cert sf ce ctx fn oid root extent sites b cap site
    limit_st dst src sb d outsz /\
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  cursor pre (ty::tys) st s /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (abi_decoder_member_infos sf ce (ty::tys))
    (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre))
    (SUM (MAP (type_memory_bytes ce) pre)) st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword(:256) /\
  oid NOTIN sites /\ oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?next t. cursor (pre++[ty]) tys next t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d outsz next t /\
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
      (abi_decoder_member_infos sf ce tys)
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) (pre++[ty])))
      (SUM (MAP (type_memory_bytes ce) (pre++[ty]))) next = ((),last) /\
    fn_has_code next last fn /\ st.cs_next_id <= next.cs_next_id /\
    next.cs_next_id <= last.cs_next_id /\ st.cs_next_var <= next.cs_next_var /\
    canonical_members_effect ctx fn sites d outsz st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,outsz)] s t
Proof
  strip_tac >> drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `cert end_st` by
    (first_x_assum (drule_at (Pat `compile_abi_decode_complex_elems _ _ _ (Lit 0w) _ _ _ _ _ = _`)) >>
     disch_then drule_all >> simp[]) >>
  `abi_decoder_code middle end_st` by
    (drule_all abi_decoder_to_buf_code >> simp[]) >>
  qhdtm_x_assum `entry_members_callback`
    (mp_tac o PURE_REWRITE_RULE [entry_members_callback_def]) >>
  disch_then (drule_at (Pat `cursor pre (ty::tys) st s`)) >>
  simp_tac bool_ss [AND_IMP_INTRO, GSYM CONJ_ASSOC, FORALL_AND_THM] >>
  disch_then (drule_at (Pat `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >> simp[] >> strip_tac >>
  qexistsl_tac [`end_st`, `t`] >> asm_rewrite_tac[] >>
  conj_tac >- (simp[MAP_APPEND, SUM_APPEND]) >> decide_tac
QED

Theorem entry_members_execution_suffix:
  !tys pre st last s.
  entry_members_callback cursor cert sf ce ctx fn oid root extent sites b cap site
    limit_st dst src sb d outsz /\
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  cursor pre tys st s /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (abi_decoder_member_infos sf ce tys)
    (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields) pre))
    (SUM (MAP (type_memory_bytes ce) pre)) st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword(:256) /\
  oid NOTIN sites /\ oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. cursor (pre++tys) [] last t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d outsz last t /\
    canonical_members_effect ctx fn sites d outsz st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,outsz)] s t
Proof
  Induct_on `tys` >> rpt gen_tac >> strip_tac
  >- (fs[abi_decoder_member_infos_def, Once compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, comp_return_def] >>
      qexists_tac `s` >> simp[entry_members_effect_refl, abi_encoder_registered_effect_refl]) >>
  drule_all entry_members_core_cons >> strip_tac >>
  `window_alloca_sites fn (abi_decoder_ids next.cs_next_id last.cs_next_id) SUBSET
   window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id)` by
    (irule entry_decoder_sites_interval_subset >> simp[]) >>
  `oid NOTIN abi_decoder_ids next.cs_next_id last.cs_next_id /\
   window_alloca_sites fn (abi_decoder_ids next.cs_next_id last.cs_next_id) SUBSET sites` by
    (conj_tac >- (fs[abi_decoder_ids_def] >> decide_tac) >> metis_tac[SUBSET_TRANS]) >>
  first_x_assum (drule_at (Pat `cursor _ tys _ _`)) >>
  disch_then drule_all >> strip_tac >>
  `abi_encoder_registered_effect
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
    [(d,outsz)] t t'` by
    (irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect _ _ t t'` (irule_at Any) >> simp[]) >>
  qpat_x_assum `cursor (_ ++ _) [] last t'`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  qexists_tac `t'` >> asm_rewrite_tac[] >> conj_tac
  >- (irule entry_members_effect_trans >> goal_assum (drule_at Any) >> simp[]) >>
  irule abi_encoder_registered_effect_trans >> goal_assum (drule_at Any) >> simp[]
QED

Theorem entry_members_execution:
  entry_members_callback cursor cert sf ce ctx fn oid root extent sites b cap site
    limit_st dst src sb d outsz /\
  (!a z elems ao vo.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) elems ao vo a = ((),z) /\
    fn_has_code a z fn /\ cert z ==> cert a) /\ cert last /\
  cursor [] tys st s /\
  canonical_members_frame ctx fn oid root extent sites b cap site limit_st
    dst src sb d outsz st s /\
  compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (abi_decoder_member_infos sf ce tys) 0 0 st = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code st last fn /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword(:256) /\
  oid NOTIN sites /\ oid NOTIN abi_decoder_ids st.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id) SUBSET sites ==>
  ?t. cursor tys [] last t /\
    canonical_members_frame ctx fn oid root extent sites b cap site limit_st
      dst src sb d outsz last t /\
    canonical_members_effect ctx fn sites d outsz st s t /\
    abi_encoder_registered_effect
      (window_alloca_sites fn (abi_decoder_ids st.cs_next_id last.cs_next_id))
      [(d,outsz)] s t
Proof
  strip_tac >> drule_at (Pat `cursor _ _ _ _`) entry_members_execution_suffix >>
  simp_tac bool_ss [MAP, SUM, APPEND] >> disch_then drule_all >> simp[]
QED
