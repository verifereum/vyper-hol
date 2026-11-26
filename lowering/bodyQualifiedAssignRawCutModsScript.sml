(* Common operand cut for a non-mutating qualified Assign with a raw saved RHS. *)
Theory bodyQualifiedAssignRawCutMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceRawUnwrapMods
  bodyQualifiedPlaceTargetEntryMods bodySavedTargetSourceMods
  bodyFullShared bodyFullPostsMods bodyFullPredsMods
  bodyWriteTargetStageMods bodyAssignQualifiedStageJoinMods bodyAssignLocalPlaceRoutesMods
  loweringPosts loweringStateRelDefs exprLowering exprLoweringProps stmtLoweringMono compileEnv
  fragGasOriginPtr fragExec context vyperStorageFootprint venomState
  ptrDiscipline words finite_map list

Theorem qualified_raw_cut_landing[local]:
  target_root bt = TopLevelNameTarget (owner,id) /\
  type_place_target env bt = SOME (Type dty) /\
  (!i se. MEM i (target_indices bt) /\
    expr_sim_inv_mods mods cenv cx env se ==>
      expr_body_pre_mods mods cenv cx env i se) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb
    (SOME vv) sr st shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0)
    rhs_marks v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu target_marks p ee Gz tz z /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
    requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|> /\
  (!r. read_result cx r mid = (INL v,mid) ==>
    read_result cx r ee = (INL v,ee)) /\
  (!l. vv_operand vv <> Label l) /\
  (!l. FST dst <> Label l) /\
  unwrap_value cenv vv st = (op,su) /\
  fn_has_code st su func /\ fn_has_code su sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
    not_fresh_at sa x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
    not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx) /\
  return_buf_frame d cenv st z /\ return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==>
    allocas_from (w2n bw + capacity) z) ==>
  ?s G tn.
    qualified_assign_operand_cut_mods (DF,lo,d,gas_explicit_sites ctx shadow_ctx,
      ctx,func,PG)
      cenv cx st0 (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb)
      (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    qualified_place_raw_unwrap_mods >>
  qpat_assum `!explicit PG. ?z' Gf tf. _`
    (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] strip_assume_tac) >>
  qexists_tac `z'` >>
  qexists_tac `Gf` >>
  qexists_tac `tf` >>
  simp[qualified_assign_operand_cut_mods_def] >>
  qhdtm_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `compile_expr cenv (expr_type e) e sa = (vv,sr)` by
    (qpat_assum `assign_place_rhs_code_mods cenv bt e sa = _`
       (mp_then (Pos hd) strip_assume_tac qualified_assign_rhs_code_view_mods) >> gvs[]) >>
  `ci_mono sa sr` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono sr st` by
    (qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `ci_mono st su` by
    (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (drule_all qualified_place_store_frame_mods >> simp[]) >>
  `return_buf_sep d cenv ee z'` by
    (`!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) z'` by
      (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK z',Gf,tf)`
         (qspec_then `DF (storage_trace_horizon ee.storage_trace)` assume_tac) >>
       rpt gen_tac >> disch_tac >>
       irule return_buf_allocas_suffix >>
       rpt (first_assum (irule_at Any)) >> simp[]) >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >> simp[] >>
     qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >>
     simp[] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars]) >>
  fs[ci_mono_def] >>
  conj_tac >-
   (gen_tac >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee z' /\ _`
      (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  Cases_on `is_word_type (expr_type e)` >> fs[] >>
  strip_tac >> qexists_tac `sa` >> simp[]
QED
