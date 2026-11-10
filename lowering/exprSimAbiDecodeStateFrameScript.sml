Theory exprSimAbiDecodeStateFrame
Ancestors
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeLiveFrame exprSimAbiDecodeConsumerProbe
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeEndpointFrame
  abiDecoderSiteEffect actualDecoderSites exprLoweringProps localPtrsProps
  exprSimProps compileEnv venomState loweringSlice valueEncodingProps venomMemDefs

Theorem abi_decode_closed_effect:
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  ?u rd prev writes. decode_site_effect ctx func start.cs_next_var writes s u /\
    t = u with <|vs_returndata := rd; vs_prev_bb := prev|>
Proof
  simp[abi_decode_success_closed_def, abi_decode_success_post_def] >> metis_tac[]
QED

Theorem abi_decode_success_local_region:
  local_ptrs_reserved ce start /\ local_ptrs_rel func ce scopes s /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  (local_region ce scopes t name lo sz <=> local_region ce scopes s name lo sz)
Proof
  strip_tac >> drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  drule_all abi_decode_reserved_local_region >> simp[]
QED

Theorem abi_decode_success_local_lookup:
  local_ptrs_reserved ce start /\ local_ptrs_rel func ce scopes s /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
  lookup_scopes name scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  lookup_var p t = lookup_var p s
Proof
  strip_tac >> drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  drule_all abi_decode_reserved_local_lookup >> simp[]
QED

Theorem abi_decode_success_locals_kept:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce es.scopes s /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  locals_kept ce es es s t
Proof
  strip_tac >> irule locals_kept_regions >> rpt strip_tac >>
  drule_all abi_decode_success_local_memory >> simp[]
QED

Theorem abi_decode_success_local_ptrs_rel:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  local_ptrs_rel func ce scopes t
Proof
  strip_tac >> irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> drule_all abi_decode_success_local_memory >> simp[])
  >- (rpt strip_tac >> drule_all abi_decode_success_local_lookup >> simp[])
  >- (gvs[abi_decode_success_closed_def, abi_decode_allocation_floor_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[])
  >- (drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
      fs[decode_site_effect_def]) >>
  drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  fs[decode_site_effect_def]
QED

Theorem abi_decode_success_immutables_rel:
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
  abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t ==>
  immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t
Proof
  strip_tac >>
  `t.vs_data_section = s.vs_data_section` by
    (fs[abi_decode_immutable_success_def] >> drule abi_decode_closed_effect >>
     strip_tac >> gvs[decode_site_effect_def, decode_static_frame_def] >>
     qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  Cases_on `ce.ce_is_ctor`
  >- (fs[immutables_rel_def, abi_decode_immutable_success_def,
         abi_decode_immutable_memory_def] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name tv v byte_offset. _ ==> immutable_value_admissible _ _ /\ _`
        drule_all >> strip_tac >>
      `mem_bytes_at byte_offset (type_memory_size tv') t.vs_memory =
       mem_bytes_at byte_offset (type_memory_size tv') s.vs_memory` by metis_tac[] >>
      simp[] >> irule val_in_memory_mem_agree >>
      conj_tac >- metis_tac[immutable_admissible_val_wf] >>
      qexistsl_tac [`type_memory_size tv'`, `s.vs_memory`] >> simp[]) >>
  fs[immutables_rel_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_success_immutable_base_zero:
  local_ptrs_reserved ce start /\ immutable_base_zero ce s /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  immutable_base_zero ce t
Proof
  strip_tac >> drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
  reverse conj_tac
  >- (fs[decode_site_effect_def, decode_static_frame_def] >>
      qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  rpt strip_tac >>
  `not_fresh_at start x` by metis_tac[local_ptrs_reserved_def] >>
  `eval_operand (Var x) s = SOME 0w` by fs[immutable_base_zero_def] >>
  `lookup_var x s = SOME 0w` by fs[eval_operand_def] >>
  drule_all abi_decode_old_var_frame >> simp[]
QED

Theorem abi_decode_success_stmt_state_rel:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  fn_inst_ids_distinct func /\ stmt_state_rel ctx func ce cx es s /\
  abi_decode_immutable_success ce (get_tenv cx) ty tv bs out d start final ctx func cx es s t ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  `abi_decode_success_closed ce (get_tenv cx) ty tv bs out d start final ctx func s t` by
    fs[abi_decode_immutable_success_def] >>
  `state_rel func ce cx es s /\ alloca_inv s /\
   immutable_alloca_sep func ce cx es s /\ immutable_base_zero ce s` by
    fs[stmt_state_rel_def] >>
  `local_ptrs_rel func ce es.scopes s /\
   immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s` by
    fs[state_rel_def] >>
  `local_ptrs_rel func ce es.scopes t` by
    (drule_all abi_decode_success_local_ptrs_rel >> simp[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t` by
    (drule_all abi_decode_success_immutables_rel >> simp[]) >>
  `immutable_alloca_sep func ce cx es t` by
    (irule abi_decode_immutable_separation_frame >> qexists_tac `s` >>
     simp[] >> reverse conj_tac
     >- fs[abi_decode_success_closed_def] >>
     metis_tac[abi_decode_success_local_region]) >>
  `immutable_base_zero ce t` by metis_tac[abi_decode_success_immutable_base_zero] >>
  drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  `state_rel func ce cx es (u with <|vs_returndata := rd; vs_prev_bb := prev|>)` by
    (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >> simp[] >>
     fs[decode_site_effect_def, decode_static_frame_def] >>
     rpt conj_tac >> qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  fs[stmt_state_rel_def, decode_site_effect_def, decode_site_resources_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     alloca_room_def, fmp_room_def, pending_alloca_size_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
