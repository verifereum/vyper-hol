Theory exprSimAbiDecodeStateFrame
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeLiveFrame exprSimAbiDecodeConsumerProbe
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeEndpointFrame
  abiDecoderSiteEffect actualDecoderSites exprLoweringProps localPtrsProps
  exprSimProps compileEnv venomState loweringSlice valueEncodingProps venomMemDefs
  stateRelProj placeMemoryProtectedFrame exprSimAbiDecodeImmutableFrame

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
  fn_inst_ids_distinct func /\ stmt_state_rel H ctx func ce cx es s /\
  abi_decode_immutable_success ce (get_tenv cx) ty tv bs out d start final ctx func cx es s t ==>
  stmt_state_rel H ctx func ce cx es t
Proof
  strip_tac >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_immutable_base_zero >> strip_tac >>
  `abi_decode_success_closed ce (get_tenv cx) ty tv bs out d start final ctx func s t /\
   abi_decode_window_frame func start s t` by fs[abi_decode_immutable_success_def] >>
  `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t` by
    fs[abi_decode_success_closed_def] >>
  `local_ptrs_rel func ce es.scopes t` by
    (drule_all abi_decode_success_local_ptrs_rel >> simp[]) >>
  `immutable_base_zero ce t` by
    (drule_all abi_decode_success_immutable_base_zero >> simp[]) >>
  `!name lo sz. local_region ce es.scopes t name lo sz ==>
                local_region ce es.scopes s name lo sz` by
    (rpt strip_tac >> drule_all abi_decode_success_local_region >> metis_tac[]) >>
  `!src. src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src) ==>
     immutable_alloca_sep func (ce with ce_module := src) cx es t` by
    (gen_tac >> disch_tac >> drule_all stmt_state_rel_immutable_alloca_sep_source >>
     strip_tac >> irule abi_decode_immutable_separation_frame >>
     qexists_tac `s` >> fs[local_region_def]) >>
  `decode_site_resources ctx func t /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
   t.vs_block_ctx = s.vs_block_ctx /\ t.vs_logs = s.vs_logs /\
   t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
   t.vs_pending_deletions = s.vs_pending_deletions /\
   t.vs_immutables = s.vs_immutables /\ t.vs_data_section = s.vs_data_section /\
   t.vs_code = s.vs_code` by
    (drule abi_decode_closed_effect >> strip_tac >> conj_tac
     >- (drule decode_site_effect_resources >> strip_tac >>
         irule decode_site_resources_fields >> qexists_tac `u` >>
         qpat_assum `t = _` SUBST1_TAC >> simp[]) >>
     drule decode_site_effect_static >> rewrite_tac[decode_static_frame_def] >>
     strip_tac >> qpat_assum `t = _` SUBST1_TAC >>
     qpat_assum `u = _` SUBST1_TAC >> simp[]) >>
  `!src. src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src) ==>
     immutables_rel ce cx.txn.target src ce.ce_is_ctor es t` by
    (gen_tac >> disch_tac >> Cases_on `src = ce.ce_module`
     >- (gvs[] >> drule state_rel_immutables_rel >> strip_tac >>
         drule_all abi_decode_success_immutables_rel >> simp[]) >>
     `immutables_rel ce cx.txn.target src ce.ce_is_ctor es s` by
       (Cases_on `ALOOKUP ce.ce_modules src` >> fs[state_rel_def] >> metis_tac[]) >>
     `immutable_alloca_sep func (ce with ce_module := src) cx es t` by
       (first_x_assum (qspec_then `src` mp_tac) >> simp[]) >>
     Cases_on `ce.ce_is_ctor`
     >- (qpat_x_assum `immutables_rel _ _ src _ _ _` mp_tac >>
         simp[immutables_rel_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
         `mem_bytes_at byte_offset (type_memory_size tv') t.vs_memory =
          mem_bytes_at byte_offset (type_memory_size tv') s.vs_memory` by
           (qpat_assum `abi_decode_window_frame _ _ _ _`
              (irule o REWRITE_RULE [abi_decode_window_frame_def]) >>
            rpt strip_tac >>
            qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
            simp[immutable_alloca_sep_def] >> strip_tac >>
            first_x_assum (drule_all_then strip_assume_tac) >>
            first_x_assum drule_all >> simp[]) >>
         first_x_assum (drule_all_then strip_assume_tac) >> simp[] >>
         irule val_in_memory_mem_agree >>
         conj_tac >- (irule (CONJUNCT1 immutable_admissible_val_wf) >> simp[]) >>
         qexistsl_tac [`type_memory_size tv'`, `s.vs_memory`] >> simp[]) >>
     fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  `state_rel H func ce cx es t` by
    (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `decode_site_resources _ _ _`
    (strip_assume_tac o REWRITE_RULE [decode_site_resources_def]) >>
  irule stmt_state_rel_intro >> asm_rewrite_tac [] >> conj_tac
  >~ [`immutable_alloca_sep func ce cx es t`]
  >- (qpat_assum `!src. _ ==> immutable_alloca_sep _ _ _ _ _`
        (qspec_then `ce.ce_module` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
      `ce with ce_module := ce.ce_module = ce` by
        simp[compile_env_component_equality] >> fs[]) >>
  rpt strip_tac >>
  qpat_assum `!src. _ ==> immutable_alloca_sep _ _ _ _ _`
    (qspec_then `src` assume_tac) >> fs[]
QED
