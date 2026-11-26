(* Delayed unwrap at the actual local Assign store cut. *)
Theory bodyAssignLocalRawOperandAtStoreMods
Ancestors
  bodyAssignLocalPreStoreMods bodyQualifiedPlaceTargetEntryMods bodyAssignLocalSavedMods
  bodyAssignQualifiedStageJoinMods bodyAssignLocalPlaceRoutesMods
  stmtLoweringMono exprLoweringProps fragExec compileEnv
  bodyQualifiedPlaceRawUnwrapMods bodySavedTargetSourceMods
  bodyQualifiedPlaceRhsPostMods bodyFullPredsMods exprReasonOperand
  vyperTypeContract exprBodyPreProps vyperStorageFootprint
  fragGasOriginPtr gasOutcomeFullMods exprSimHypsDefs context option
  bodyPlaceWriteSourceMods vyperState list bodyWriteTargetStageMods
  loweringStateRelDefs venomState bodyFullShadowBodyInv
  loweringPosts bodyPtrDefs bodySimFull ptrSafetyTransport bodyFullShared
  vyperStorageTrace vyperEvalExprPreservesScopesDom stmtSimLogCompose stmtSimDefs wordArgsPtr
  vyperTypeEvalCaseProofs bodyCopyReadPhysicalTypeMods vyperTypeSystem
  aggregateEvaluatedLayout stmtSimDeclStore logArgumentTypeEval
  vyperTypeArgFits memoryValueTyping bodyPtrSignedConvertSourceTyping

Theorem raw_local_store_interval[local]:
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv)
    sr st shadow_sr shadow_st dst /\
  dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?op cur. unwrap_value cenv vv st = (op,cur) /\
    compile_assign_value cenv (FST dst) LocMemory op (is_word_type dty)
      (vv_location vv) dty (lowered_value_type cenv e)
      (type_memory_bytes cenv dty) cur = ((),sb) /\
    fn_has_code st cur func
Proof
  strip_tac >> drule_all_then strip_assume_tac qualified_place_code_intervals_mods >>
  qhdtm_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  Cases_on `unwrap_value cenv vv st` >>
  rename1 `unwrap_value cenv vv st = (op,cur)` >>
  `assign_place_store_code_mods cenv e (SOME vv) dst =
    comp_bind (unwrap_value cenv vv) (\op. compile_assign_value cenv
      (FST dst) LocMemory op (is_word_type dty) (vv_location vv) dty
      (lowered_value_type cenv e) (type_memory_bytes cenv dty))` by
    (qpat_assum `dst = (_,SOME LocMemory,_)` (once_rewrite_tac o single) >>
     simp[assign_place_memory_store_code_mods]) >>
  qpat_x_assum `assign_place_store_code_mods cenv e (SOME vv) dst st = _` mp_tac >>
  simp[comp_bind_def] >> strip_tac >> simp[] >>
  `cs_extends st cur` by
    (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `cs_extends cur sb` by
    (`ci_mono cur (SND (compile_assign_value cenv (FST dst) LocMemory op
        (is_word_type dty) (vv_location vv) dty (lowered_value_type cenv e)
        (type_memory_bytes cenv dty) cur))` by SIMP_TAC (srw_ss()) [ci_mono_stmt_helpers] >>
     pop_assum mp_tac >> simp[ci_mono_def]) >>
  qpat_assum `fn_has_code st sb func`
    (mp_then (Pat `fn_has_code _ _ _`) mp_tac fn_has_code_split) >>
  disch_then (qspec_then `cur` mp_tac) >> simp[]
QED

Theorem raw_bytes_placement[local]:
  is_bytestring_type ty /\ is_bytestring_type sty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type tv v /\ value_has_type stv v /\
  expr_val_at cenv cx ty sa cur ee v op s ==>
  expr_val_at cenv cx sty sa cur ee v op s
Proof
  strip_tac >>
  `val_footprint tv v = val_footprint stv v` by
    (qspecl_then [`get_tenv cx`,`ty`,`sty`] (drule_all_then ACCEPT_TAC)
       valueCopyBytesTheory.bytestring_val_footprint_eq) >>
  `~is_word_type ty /\ ~is_word_type sty` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  qpat_x_assum `expr_val_at _ _ ty _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def,value_has_type_val_wf] >> strip_tac
  >- (qexists `w` >> simp[] >> disj1_tac >> qexistsl [`aid`,`b`,`sz`] >>
      simp[] >> first_assum ACCEPT_TAC)
  >- (qexists `w` >> simp[] >> disj2_tac >> disj1_tac >>
      qexistsl [`n`,`b`,`sz`] >> simp[] >>
      `?bt. tv = BaseTV bt` by
        (qpat_assum `evaluate_type _ ty = SOME tv`
           (mp_then (Pat `evaluate_type _ _ = _`) mp_tac valueCopyBytesTheory.bytestring_type_value) >>
         simp[] >> strip_tac >> gvs[]) >>
      `?bt'. stv = BaseTV bt'` by
        (qpat_assum `evaluate_type _ sty = SOME stv`
           (mp_then (Pat `evaluate_type _ _ = _`) mp_tac valueCopyBytesTheory.bytestring_type_value) >>
         simp[] >> strip_tac >> gvs[]) >>
      gvs[] >> irule exprSimPropsTheory.local_val_at_base >>
      metis_tac[value_has_type_val_wf,arithmeticTheory.LESS_EQ_REFL]) >>
  qexists `w` >> simp[]
QED

val here = ``local_assign_here_mods (DF,lo,d,ctx,func) cenv cx env st0
  (sa,es,s0,G0,tn0) (bt,id,path,dty,dst) (entry,p,cap,b,off,ptv,dw) ee``;

val rhs = ``qualified_assign_rhs_reached_mods cx st0 e es s0
  (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
     es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0) ms v mid Gu tu u``;

val reached = ``qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
  mid sr st dst u Gu tu marks (MemoryPlace id path) ee Gz tz z``;

Theorem assign_local_raw_operand_at_store_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
          expr_body_pre_mods mods cenv cx env i se) /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  body_const_cells_agree_mods mods cx env es /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H)) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv)
    sr st shadow_sr shadow_st dst /\
  ^rhs /\ ^reached /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  ^here st z Gz tz /\ write_place cx (MemoryPlace id path) v ee = (INL (),ff) ==>
  ?op cur sw s G tn.
    unwrap_value cenv vv st = (op,cur) /\
    compile_assign_value cenv (FST dst) LocMemory op (is_word_type dty)
      (vv_location vv) dty (lowered_value_type cenv e)
      (type_memory_bytes cenv dty) cur = ((),sb) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (z,Gz,tz) [] (OK s,G,tn)) /\
    ^here cur s G tn /\
    local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw)
      (op,sw) sa ee cur s G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dst = (FST dst,SOME LocMemory,SOME (ValPT dty))` by
    fs[local_assign_here_mods_def] >>
  drule_all_then strip_assume_tac raw_local_store_interval >>
  `(?gs raw. eval_expr cx e (es with gas_obs := gs) = (INL raw,mid) /\
               read_result cx raw mid = (INL v,mid)) /\
   compile_expr cenv (expr_type e) e sa = (vv,sr)` by
    (qhdtm_assum `qualified_assign_rhs_reached_mods`
       (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
     `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
       fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (strip_assume_tac o MATCH_MP qualified_place_rhs_saved_view_mods)) >>
     gvs[] >> rpt (first_assum (irule_at Any))) >>
  pop_assum strip_assume_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `!l. vv_operand vv <> Label l` by
    (drule_then (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) expr_body_pre_mods_inv >>
     drule_all compile_expr_reason_uniform >>
     disch_then (qspec_then `expr_type e` mp_tac) >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum drule >> Cases_on `vv` >> simp[reason_result_shape_def,vv_operand_def]) >>
  `!r. read_result cx r mid = (INL v,mid) ==>
       read_result cx r ee = (INL v,ee) /\
       ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
         requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|>` by
    (qhdtm_assum `qualified_assign_target_reached_mods`
       (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
     qpat_assum `IS_SOME (check_contract F _ _ _)`
       (strip_assume_tac o REWRITE_RULE [IS_SOME_EXISTS]) >>
     qhdtm_assum `body_const_cells_agree_mods`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     rpt strip_tac >>
     drule_all_then strip_assume_tac saved_checked_target_source_update_mods >> simp[]) >>
  qpat_assum `!r. read_result _ _ _ = _ ==> _ /\ _`
    (drule_then strip_assume_tac) >>
  `expr_sim_inv_mods mods cenv cx env ee` by
    (drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
     qhdtm_assum `local_assign_here_mods`
       (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
     qhdtm_assum `qualified_assign_target_reached_mods`
       (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
     qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [APPEND_NIL])) >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     simp[] >> strip_tac >>
     `expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee`
       suffices_by simp[] >>
     irule place_write_reached_source_mods >>
     qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >> simp[]) >>
  `sr.cs_next_var <= st.cs_next_var /\ sr.cs_next_id <= st.cs_next_id` by
    (qhdtm_assum `qualified_assign_code_mods`
       (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
     qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `!r. read_result cx r mid = (INL v,mid) ==>
       read_result cx r ee = (INL v,ee)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!r. _ ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_x_assum `eval_expr _ _ _ = (INL raw,mid)` kall_tac >>
  qpat_x_assum `read_result _ raw mid = _` kall_tac >>
  qpat_x_assum `read_result _ raw ee = _` kall_tac >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (mp_then (Pat `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
      mp_tac qualified_raw_saved_at_cut) >>
  disch_then (fn th => qhdtm_assum `qualified_assign_rhs_reached_mods`
    (mp_then (Pat `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (qspecl_then [`tops`,`src`,`exps`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> simp[]) >>
  disch_then strip_assume_tac >>
  qhdtm_assum `local_assign_here_mods`
    (strip_assume_tac o REWRITE_RULE [local_assign_here_mods_def]) >>
  `copy_old_operand st (vv_operand vv)` by
    (rw[exprSimCopyTheory.copy_old_operand_def] >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sr` >> simp[]) >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at st x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  drule_all qualified_raw_run_suffix >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (strip_assume_tac o BETA_RULE)) >>
  rename1 `wb_frame cenv ee ee st z s` >>
  rename1 `ghost_kept_at lo cenv ee st Gz tz z G tn` >>
  `^here cur s G tn` by suspend "frame" >>
  `?sw. local_assign_store_source_mods cenv cx e vv (dty,ptv) v (FST dst,dw)
      (op,sw) sa ee cur s G tn` suffices_by
    (strip_tac >> qexistsl [`op`,`cur`,`sw`,`s`,`G`,`tn`] >> simp[]) >>
  suspend "source"
QED

Resume assign_local_raw_operand_at_store_mods[frame]:
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `?q. FST dst = Var q /\ not_fresh_at st q` by suspend "destvar" >>
  `st.cs_next_var <= cur.cs_next_var /\ st.cs_next_id <= cur.cs_next_id` by
    (qspecl_then [`cenv`,`vv`,`st`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `not_fresh_at st p` by
    (qpat_assum `local_ptrs_reserved cenv st`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
     qpat_assum `!n1 n2 x z1 z2. _ ==> not_fresh_at st x /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1 o SPEC_ALL))) >>
  `lookup_var p s = SOME b` by simp[] >>
  `local_backed func p s (w2n b) cap` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
       (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     drule_all nameLoweringPropsTheory.local_ptrs_rel_value >>
     simp[eval_operand_def]) >>
  `eval_operand (FST dst) s = SOME dw /\ op_taint tn (FST dst) = {} /\
    op_prov G (FST dst) = FLOOKUP G p /\
    (0 < type_memory_size ptv ==>
      ?x. FST dst = Var x /\ not_fresh_at cur x /\
          ptr_covers G tn x s (type_memory_size ptv))` by suspend "destfields" >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ s`
       (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room) >>
     simp[alloca_room_def] >> decide_tac) >>
  `return_buf_sep d cenv ee s` by suspend "bufsep" >>
  `alloca_frame cenv es sa s0 cenv ee s /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` by
    suspend "compose" >>
  `!x. not_fresh_at st x ==> not_fresh_at cur x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> not_fresh_at st x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!aid a. FLOOKUP z.vs_allocas aid = SOME a ==> FLOOKUP s.vs_allocas aid = SOME a` by
    (qhdtm_assum `wb_frame` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >> simp[]) >>
  `return_buf_frame d cenv cur s` by
    (drule bodyMemoryDefsTheory.return_buf_frame_frame >> disch_then irule >> simp[]) >>
  `ret_pc_ok cenv cur s` by
    (rw[ret_pc_ok_def] >>
     qpat_assum `ret_pc_ok cenv st z` (drule_then strip_assume_tac o REWRITE_RULE [ret_pc_ok_def]) >>
     simp[]) >>
  simp[local_assign_here_mods_def,local_region_def] >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[]) >>
  rpt strip_tac >> (first_assum ACCEPT_TAC ORELSE
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) ORELSE
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC))
QED

Resume assign_local_raw_operand_at_store_mods[destvar]:
  `ptr_covers Gz tz p z cap` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ z`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     qpat_assum `!n e p sz. _ ==> ptr_covers _ _ _ _ _ /\ _` (drule_all_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (qspec_then `H0` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
  Cases_on `FST dst` >> gvs[ptr_covers_def,ptrDisciplineTheory.op_prov_def]
QED

Resume assign_local_raw_operand_at_store_mods[destfields]:
  qpat_assum `ghost_kept_at _ _ ee st _ _ z _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  `not_fresh_at cur q` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  gvs[eval_operand_def,ptrDisciplineTheory.op_prov_def,ptr_covers_def]
QED

Resume assign_local_raw_operand_at_store_mods[bufsep]:
  `!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) s` by
    (rpt strip_tac >>
     `allocas_from (w2n bw + capacity) z` by fs[return_buf_sep_def] >>
     `w2n bw + capacity <= z.vs_alloca_next` by fs[loweringPostsTheory.return_buf_frame_def] >>
     qpat_assum `!D. gas_origin_ptr_path _ _ [] _`
       (qspec_then `DF H0` (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
     drule gas_path_ptr_allocas_from >>
     disch_then (qspecl_then [`w2n bw + capacity`,`s`] mp_tac) >> simp[]) >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ _ z`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule return_buf_sep_locals_kept) >>
  simp[] >> qexists `st` >> simp[]
QED

Resume assign_local_raw_operand_at_store_mods[compose]:
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    (qpat_assum `eval_target_place _ _ _ = _` (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_assum `eval_expr _ _ _ = _` (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >>
     drule eval_target_place_preserves_scopes_dom >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (`alloca_frame cenv ee st z cenv ee s` by
        (qpat_assum `stmt_state_rel H0 _ _ _ _ _ z`
           (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule log_wb_alloca_frame) >>
         qpat_assum `wb_frame _ ee ee st z s` (irule_at Any) >> simp[]) >>
      irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`z`,`st`] >> simp[]) >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ _ s0`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
  qpat_assum `ghost_kept_at _ _ ee st _ _ z _ _` (irule_at Any) >>
  qexists `ee` >> simp[] >>
  drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (qspec_then `H0` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  qpat_assum `stmt_state_rel H0 _ _ _ _ _ s0`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule exprSimWordArgsTheory.wb_frame_trans) >>
  qpat_assum `wb_frame cenv es mid sa s0 u` (irule_at Any) >>
  qpat_assum `wb_frame cenv mid ee sr u z` (irule_at Any) >> simp[] >>
  qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (CONJUNCT1 compile_expr_ci_mono) >>
  simp[ci_mono_def]
QED

Resume assign_local_raw_operand_at_store_mods[source]:
  drule_then assume_tac expr_body_pre_mods_inv >>
  `env_consistent env cx es` by drule_then ACCEPT_TAC expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `well_formed_type env.type_defs (expr_type e)` by
    drule_all_then ACCEPT_TAC checked_expr_type_well_formed >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (irule copy_lowered_fits_mods >> qexistsl_tac [`cx`,`env`,`es`,`mods`] >> simp[]) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) (expr_type e)` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[type_widens_to_def]) >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty` by
    (irule typedCopyCompatibilityTheory.type_widens_to_trans >> qexists `expr_type e` >> simp[]) >>
  `eval_operand (FST dst) s = SOME dw` by fs[local_assign_here_mods_def] >>
  `is_word_type (expr_type e) <=> is_word_type dty` by
    (qpat_assum `type_widens_to (get_tenv cx) (expr_type e) dty` mp_tac >>
     simp[NoAsms,type_widens_to_def] >> strip_tac >> simp[arg_type_fits_word_type]) >>
  Cases_on `is_word_type dty`
  >- suspend "source_word" >>
  suspend "source_memory"
QED

Resume assign_local_raw_operand_at_store_mods[source_word]:
  `is_word_type (expr_type e)` by simp[] >>
  `lowered_value_type cenv e = dty /\ expr_type e = dty` by
    (conj_tac >> irule compileEnvTheory.type_widens_to_word >>
     simp[] >> qexists `get_tenv cx` >> first_assum ACCEPT_TAC) >>
  `lowered_value_type cenv e = expr_type e` by simp[] >>
  `post_value_type cenv e = dty` by simp[post_value_type_lowered] >>
  qpat_assum `is_word_type (expr_type e)` (fn word =>
    qpat_x_assum `if is_word_type (expr_type e) then _ else _`
      (strip_assume_tac o SRULE [word])) >>
  `rt = ptv` by
    (qpat_assum `expr_type e = dty` (fn eq =>
       qpat_assum `evaluate_type _ (expr_type e) = SOME rt` (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[]) >>
  qexists `typed_val_to_w256 ptv v` >>
  `store_lays_out ptv ptv v` by
    (qspecl_then [`get_tenv cx`,`dty`,`ptv`,`v`] mp_tac store_lays_out_typed >> fs[]) >>
  fs[local_assign_store_source_mods_def]
QED

Resume assign_local_raw_operand_at_store_mods[source_memory]:
  `~is_word_type (expr_type e)` by simp[] >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[arg_type_fits_word_type] >>
  qpat_assum `~is_word_type (expr_type e)` (fn nonword =>
    qpat_x_assum `if is_word_type (expr_type e) then _ else _`
      (qx_choose_then `rt` (qx_choose_then `sw` (map_every assume_tac o CONJUNCTS)) o
       SRULE [nonword])) >>
  `value_has_type ptv v` by (drule_all type_widens_to_value_has_type >> simp[]) >>
  `type_memory_bytes cenv dty = type_memory_size ptv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >> qexists `get_tenv cx` >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env ee`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[] >>
     rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qexists `sw` >> simp[local_assign_store_source_mods_def] >>
  simp[value_has_type_val_wf] >>
  (Cases_on `vv_location vv = SOME LocMemory`
   >- (simp[] >> suspend "source_locmemory")) >>
  (Cases_on `is_bytestring_type dty`
   >- (simp[] >> suspend "source_direct_bytes")) >>
  simp[] >> suspend "source_direct_other"
QED

Resume assign_local_raw_operand_at_store_mods[source_direct_bytes]:
  `is_bytestring_type (lowered_value_type cenv e)` by
    (qpat_assum `type_widens_to _ (lowered_value_type cenv e) dty` mp_tac >>
     simp[NoAsms,type_widens_to_def] >> strip_tac >>
     (first_assum ACCEPT_TAC ORELSE
      metis_tac[compileEnvTheory.arg_type_fits_bytestring_source])) >>
  `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
          (?str. v = StringV str /\ len = LENGTH str)) /\
         val_store_size rt v = 32 * word_size len + 32` by
    (drule_all_then strip_assume_tac bytestring_typed_value_view >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME rt` mp_tac >>
     qpat_assum `lowered_value_type cenv e = BaseT _` (once_rewrite_tac o single) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     strip_tac >>
     qpat_assum `BaseTV _ = rt` (once_rewrite_tac o single o SYM) >>
     simp[exprSimPropsTheory.val_store_size_def]) >>
  `val_store_size rt v <= type_memory_size rt` by simp[exprSimPropsTheory.val_store_size_le,value_has_type_val_wf] >>
  qexists `val_store_size rt v` >>
  (conj_tac >- (qexists `len` >> simp[])) >>
  qpat_x_assum `val_store_size rt v = _` kall_tac >>
  disch_tac >>
  `0 < type_memory_size rt` by decide_tac >>
  (conj_tac
   >- (qpat_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
       `not_fresh_at cur x` by
         (qpat_assum `!x. op = Var x ==> _` (drule_then ACCEPT_TAC)) >>
       qexists `x` >> (conj_tac >- first_assum ACCEPT_TAC) >>
       (conj_tac >- first_assum ACCEPT_TAC) >>
       irule reasonCopySourcePtrTheory.ptr_covers_mono >>
       qexists `type_memory_size rt` >> conj_tac >> first_assum ACCEPT_TAC)) >>
  decide_tac
QED

Resume assign_local_raw_operand_at_store_mods[source_locmemory]:
  conj_tac
  >- (disch_tac >> qpat_assum `0 < type_memory_size rt ==> _`
        (drule_then strip_assume_tac) >> qexists `x` >> simp[]) >>
  disch_tac >> disj1_tac >>
  (reverse (Cases_on `is_bytestring_type (lowered_value_type cenv e)`) >- fs[]) >>
  `is_bytestring_type (post_value_type cenv e) /\
   expr_val_at cenv cx (post_value_type cenv e) sa cur ee v op s` by
    (qpat_assum `~is_word_type (expr_type e) /\ _ ==> _` mp_tac >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid)` by
    simp[Once bind_def] >>
  `?pt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pt /\
        value_has_type pt v` by
    (drule_all_then strip_assume_tac copy_read_physical_type_gas_obs_mods >>
     qexists `pt` >> simp[]) >>
  irule raw_bytes_placement >> simp[] >>
  qexistsl [`pt`,`post_value_type cenv e`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume assign_local_raw_operand_at_store_mods[source_direct_other]:
  conj_tac
  >- (disch_tac >> qpat_assum `0 < type_memory_size rt ==> _`
        (drule_then strip_assume_tac) >> qexists `x` >> simp[]) >>
  strip_tac >>
  `~is_bytestring_type (lowered_value_type cenv e)` by
    (strip_tac >> qpat_assum `type_widens_to _ (lowered_value_type cenv e) dty`
       (mp_then (Pat `type_widens_to _ _ _`) mp_tac typedMemoryCopyTheory.type_widens_from_bytestring) >> simp[]) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sa cur ee v op s` by simp[] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qhdtm_assum `qualified_assign_target_reached_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z`
    (qspec_then `H0` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >>
  `FST (SND dst) = SOME LocMemory` by
    (qpat_assum `dst = (_,_,_)` (once_rewrite_tac o single) >> simp[]) >>
  `place_ptr_rel cenv cx z (PlaceR (MemoryPlace id path)) dw (SOME LocMemory) (Type dty)` by
    (qhdtm_assum `write_target_location_mods`
       (mp_tac o REWRITE_RULE [write_target_location_mods_def]) >>
     qpat_assum `eval_operand (FST dst) z = SOME dw` (once_rewrite_tac o single) >>
     simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) dw (SOME LocMemory) (Type dty)` by
    (qpat_assum `place_ptr_rel _ _ z _ _ _ _`
       (mp_then (Pat `place_ptr_rel _ _ _ _ _ _ _`) irule
          targetPlaceSimCasesBaseTheory.place_ptr_rel_vars_frame) >>
     qexists `st` >> simp[]) >>
  `lowered_value_type cenv e <> dty` by (strip_tac >> gvs[]) >>
  qpat_assum `place_ptr_rel cenv cx s _ dw _ _`
    (mp_then (Pat `place_ptr_rel _ _ _ _ _ _ _`)
       (fn th => qpat_assum `expr_val_at cenv cx (lowered_value_type cenv e) sa cur ee v op s`
         (mp_then (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) (drule_all_then mp_tac) th))
       bodyAssignLocalSavedModsTheory.saved_local_typed_separation) >>
  qpat_assum `w2n dw = _` (once_rewrite_tac o single) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Finalise assign_local_raw_operand_at_store_mods
