(* A flag member uses the linked flag table and emits no instruction. *)
Theory bodyFlagLeafMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyFullShared bodyInvSplit
  exprBodyPreProps exprSimHypsDefs exprSimProps exprSimStack exprSimMemDefs
  exprLoweringProps loweringPosts loweringStateRelDefs bodyPtrDefs
  gasOutcomeFullMods gasOutcomeFull gasContext gasStorage gasSummary
  fragGasOriginPtr vyperStorageFootprint vyperTypeSystem vyperTyping
  vyperInterpreter vyperState vyperAST vyperValue compileEnv exprLowering
  stmtSimDefs valueEncoding venomState ptrDiscipline loweringSlice

Theorem flag_member_index[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  get_module_code cx src = SOME tops /\ lookup_flag fid tops = SOME members /\
  INDEX_OF mid members = SOME i ==>
  cenv.ce_flag_member_id (nsid_to_string (src,fid)) mid = i
Proof
  simp[expr_sim_inv_mods_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem flag_member_annotation[local]:
  expr_body_pre_mods mods cenv cx env (FlagMember ann nsid mid) es ==>
  ann = FlagT nsid
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> simp[well_typed_expr_def]
QED

Theorem flag_outcome_nil[local]:
  ~s.vs_halted /\
  (!tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       Q H res (es with gas_obs := []) G tn s) ==>
  gas_outcome_full_mods (DF, lo, explicit, ctx, func, PG) mods cx st0 source
    (es,s,G,tn) Q R
Proof
  strip_tac >> PURE_REWRITE_TAC[gas_outcome_full_mods_def] >>
  qexists_tac `[]` >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (disj1_tac >>
      conj_tac >- simp[gas_bad_storage_at_def, gas_explicit_def] >>
      qexistsl_tac [`ARB`, `func`, `PG`, `G`, `tn`, `s`] >>
      simp[gas_origin_ptr_focus_nil]) >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`res`, `es`, `OK s`, `G`, `tn`] >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem flag_nil_frame[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G tn s ==>
  stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) s /\
  storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
  ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G tn s
Proof
  strip_tac >> conj_tac
  >- (drule msg_gas_state_frame >>
      disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
      simp[]) >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ es _` mp_tac >>
      PURE_REWRITE_TAC[immutable_frame_mods_def, immutables_rel_mods_def,
           immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
           loweringStateRelDefsTheory.immutables_rel_def,
           evaluation_state_accfupds] >> simp[]) >>
  conj_tac
  >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
       storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >>
  PURE_REWRITE_TAC[evaluation_state_accfupds] >> simp[]
QED

Theorem flag_member_value_full_mods[local]:
  expr_body_pre_mods mods cenv cx env (FlagMember ann (src,fid) mid) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann (src,fid) mid) es
Proof
  rw[expr_sim_full_mods_def] >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  drule_all flag_member_index >> strip_tac >>
  drule flag_member_annotation >> strip_tac >>
  qpat_x_assum `lower_value compile_expr cenv _ _ _ = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
       unwrap_value_def] >> strip_tac >> gvs[] >>
  irule flag_outcome_nil >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `INL (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (src,fid)) mid))` >>
  simp[] >>
  gen_tac >> strip_tac >> first_x_assum drule >>
  disch_then (strip_assume_tac o MATCH_MP flag_nil_frame) >>
  simp[expr_store_bound_def, expr_type_def, is_word_type_def,
       ptr_val_ok_def, op_taint_def, ghost_kept_at_def,
       expr_post_mods_def, expr_post_def, expr_val_rel_def, expr_val_at_def,
       typed_val_to_w256_word_value, word_value_def, val_to_w256_def,
       eval_operand_def, locals_kept_def]
QED

Theorem flag_member_vv_full_mods[local]:
  expr_body_pre_mods mods cenv cx env (FlagMember ann (src,fid) mid) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann (src,fid) mid) es
Proof
  rw[expr_vv_sim_full_mods_def] >>
  `gas_admissible (bind (eval_expr cx (FlagMember ann (src,fid) mid))
     (read_result cx)) expr_res_ok es` by
    (irule eval_expr_force_admissible >> simp[] >>
     rpt gen_tac >> simp[Once evaluate_def, lookup_flag_mem_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]) >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  drule_all flag_member_index >> strip_tac >>
  drule flag_member_annotation >> strip_tac >>
  qpat_x_assum `compile_expr cenv _ _ _ = _` mp_tac >>
  simp[compile_expr_def, comp_return_def] >> strip_tac >> gvs[] >>
  irule flag_outcome_nil >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `INL (Value (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (src,fid)) mid)))` >>
  conj_tac >- simp[Once evaluate_def, lookup_flag_mem_def, return_def] >>
  simp[] >> gen_tac >> strip_tac >> first_x_assum drule >>
  disch_then (strip_assume_tac o MATCH_MP flag_nil_frame) >>
  simp[vv_store_bound_def, contextTheory.vv_location_def, expr_type_def,
       is_word_type_def, ptr_vv_ok_def, ptr_val_ok_def, read_result_def,
       return_def, op_taint_def, ghost_kept_at_def, vv_post_mods_def,
       vv_holds_mods_def, vv_place_ptr_mods_def, vv_place_ptr_def,
       vv_holds_def, vv_at_def, vv_storage_live_def, expr_val_rel_def,
       expr_val_at_def, typed_val_to_w256_word_value, word_value_def,
       val_to_w256_def, eval_operand_def, locals_kept_def]
QED

Theorem flag_member_expr_full_ok_mods:
  !mods exps cx ann nsid mid. body_expr_full_ok_mods mods exps cx (FlagMember ann nsid mid)
Proof
  simp[body_expr_full_ok_mods_def] >> rpt strip_tac >> PairCases_on `nsid`
  >- (irule flag_member_value_full_mods >> first_assum (irule_at Any)) >>
  irule flag_member_vv_full_mods >> first_assum (irule_at Any)
QED
