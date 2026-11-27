Theory exprSimAbiDecodeStateFrame
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeLiveFrame exprSimAbiDecodeConsumerProbe
  exprSimAbiDecodeImmutableFrame alist option finite_map
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

Theorem abi_decode_source_immutables_frame[local]:
  immutables_rel ce cx.txn.target src ce.ce_is_ctor es s /\
  immutable_alloca_sep func (ce with ce_module := src) cx es t /\
  abi_decode_window_frame func start s t /\
  t.vs_data_section = s.vs_data_section ==>
  immutables_rel ce cx.txn.target src ce.ce_is_ctor es t
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor`
  >- (qpat_assum `immutable_alloca_sep _ _ _ _ _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def]) >>
      fs[immutables_rel_def] >> rpt gen_tac >> strip_tac >>
      rename1 `FLOOKUP _ _ = SOME (itv,iv)` >>
      qpat_x_assum `!name tv v byte_offset. _ ==> immutable_value_admissible _ _ /\ _`
        (drule_all_then strip_assume_tac) >>
      `mem_bytes_at byte_offset (type_memory_size itv) t.vs_memory =
       mem_bytes_at byte_offset (type_memory_size itv) s.vs_memory` by
        (qpat_assum `abi_decode_window_frame _ _ _ _`
           (irule o REWRITE_RULE [abi_decode_window_frame_def]) >>
         rpt strip_tac >>
         qpat_x_assum `ce.ce_is_ctor ==> !name tv v off. _` mp_tac >>
         simp[] >> disch_then (drule_all_then strip_assume_tac) >> metis_tac[]) >>
      simp[] >> irule val_in_memory_mem_agree >>
      conj_tac >- metis_tac[immutable_admissible_val_wf] >>
      qexists_tac `type_memory_size itv` >> qexists_tac `s.vs_memory` >> simp[]) >>
  fs[immutables_rel_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_success_stmt_state_rel:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  fn_inst_ids_distinct func /\ stmt_state_rel H ctx func ce cx es s /\
  abi_decode_immutable_success ce (get_tenv cx) ty tv bs out d start final ctx func cx es s t ==>
  stmt_state_rel H ctx func ce cx es t
Proof
  strip_tac >>
  `abi_decode_success_closed ce (get_tenv cx) ty tv bs out d start final ctx func s t` by
    fs[abi_decode_immutable_success_def] >>
  `state_rel H func ce cx es s /\ alloca_inv s /\ immutable_base_zero ce s` by
    fs[stmt_state_rel_def] >>
  `local_ptrs_rel func ce es.scopes s` by fs[state_rel_def] >>
  `local_ptrs_rel func ce es.scopes t` by
    (drule_all abi_decode_success_local_ptrs_rel >> simp[]) >>
  `!name lo sz. local_region ce es.scopes t name lo sz <=>
                 local_region ce es.scopes s name lo sz` by
    (rpt gen_tac >> drule_all abi_decode_success_local_region >> simp[]) >>
  `ce with ce_module := ce.ce_module = ce` by simp[compile_env_component_equality] >>
  `!src. src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src) ==>
     immutable_alloca_sep func (ce with ce_module := src) cx es t` by
    (rpt gen_tac >> strip_tac >>
     `immutable_alloca_sep func (ce with ce_module := src) cx es s` by
       (qpat_assum `stmt_state_rel H ctx func ce cx es s`
          (strip_assume_tac o REWRITE_RULE [stmt_state_rel_def]) >>
        gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
     `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t` by
       fs[abi_decode_success_closed_def] >>
     `!name lo sz. local_region (ce with ce_module := src) es.scopes t name lo sz ==>
                    local_region (ce with ce_module := src) es.scopes s name lo sz` by
       (qpat_assum `!name lo sz. local_region ce _ t _ _ _ <=> _`
          (assume_tac o REWRITE_RULE [local_region_def]) >>
        simp[local_region_def]) >>
     irule abi_decode_immutable_separation_frame >> qexists_tac `s` >>
     simp[]) >>
  `t.vs_data_section = s.vs_data_section` by
    (drule abi_decode_closed_effect >> strip_tac >>
     gvs[decode_site_effect_def, decode_static_frame_def] >>
     qpat_x_assum `u = _` (fn th => simp[Once th])) >>
  `!src. src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src) ==>
     immutables_rel ce cx.txn.target src ce.ce_is_ctor es t` by
    (rpt gen_tac >> strip_tac >> irule abi_decode_source_immutables_frame >>
     qexistsl_tac [`func`, `s`, `start`] >> simp[] >>
     qpat_assum `state_rel H func ce cx es s`
       (strip_assume_tac o REWRITE_RULE [state_rel_def]) >>
     fs[state_rel_def, abi_decode_immutable_success_def, optionTheory.IS_SOME_EXISTS] >>
     metis_tac[]) >>
  `immutable_base_zero ce t` by metis_tac[abi_decode_success_immutable_base_zero] >>
  `immutable_alloca_sep func ce cx es t` by
    (qpat_assum `!src. src = ce.ce_module \/ _ ==>
                   immutable_alloca_sep func (ce with ce_module := src) cx es t`
       (qspec_then `ce.ce_module` (strip_assume_tac o SIMP_RULE bool_ss [])) >>
     metis_tac[]) >>
  drule abi_decode_closed_effect >> strip_tac >> gvs[] >>
  `state_rel H func ce cx es (u with <|vs_returndata := rd; vs_prev_bb := prev|>)` by
    (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >> simp[] >>
     fs[decode_site_effect_def, decode_static_frame_def] >>
     rpt conj_tac >> qpat_x_assum `u = _` (fn th => simp[Once th]) >>
     fs[immutables_rel_def, LET_THM] >>
     qpat_assum `u.vs_data_section = s.vs_data_section`
       (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  fs[stmt_state_rel_def, decode_site_effect_def, decode_site_resources_def,
     alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     alloca_room_def, fmp_room_def, pending_alloca_size_def,
     GSYM optionTheory.IS_SOME_EXISTS] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
