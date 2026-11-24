(* A qualified assignment binds the RHS read before the destination. The
   two cuts use the actual source and machine endpoints of those runs. *)
Theory bodyAssignQualifiedStageJoinMods
Ancestors
  bodyAssignLocalPlaceRoutesMods bodyInvModuleProps bodyWriteTargetStageMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  stmtSimForArrayFrame stmtSimProps bodyPtrDefs haltExitProj
  targetPlaceSim targetPlaceSimCases vyperInterpreter vyperExprNoControl
  vyperStorageTrace vyperStorageFootprint vyperState vyperAST bodyFullPredsMods bodyFullPostsMods
  stmtSimDefs exprSimDefs fragExec gasContext loweringPosts compileEnv
  exprLowering stmtLowering vyperSubscriptOverlap vyperTypeSystem alist
Libs monadsyntax

Definition assign_qualified_exit_mods_def[nocompute]:
  assign_qualified_exit_mods ctx cx RetQ H res ee gt r <=>
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
       allocas_below_fmp s)
End

Theorem qualified_assign_source[local]:
  eval_stmt cx (Assign (BaseTarget bt) e) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_target_place cx bt) (\p. write_place cx p v))
Proof
  simp[Once evaluate_def,bind_assoc]
QED

Theorem qualified_assign_expr_exit[local]:
  expr_exit (res : 'a + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?ex. res = INR ex /\ assign_qualified_exit_mods ctx cx RetQ H (INR ex) ee gt r
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  simp[assign_qualified_exit_mods_def, GSYM expr_exit_def, stmt_exit_ptr_def,
       expr_exit_INR_type, halt_exit_INR_type] >>
  Cases_on `r` >> simp[expr_exit_def]
QED

Theorem qualified_assign_rhs_admissible[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def,AllCaseEqs()] >> strip_tac >> gvs[]
     >- metis_tac[read_result_no_control] >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`,`gs`] >> simp[qualified_assign_source,Once vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def,expr_res_ok_def,no_control_exc_def]
QED

Theorem qualified_assign_target_admissible[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
    (INL v,mid with gas_obs := tail)) ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok mid
Proof
  strip_tac >> rw[gas_admissible_def] >> Cases_on `res` >- simp[target_place_res_ok_def] >>
  rename1 `INR ex` >> `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >> qexistsl [`ee`,`prefix ++ gs`] >>
     simp[qualified_assign_source,Once vyperStateTheory.bind_def] >>
     simp[vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def,target_place_res_ok_def,no_control_exc_def]
QED

Theorem qualified_assign_rhs_releases[local]:
  (!s pv se sr v sf. eval_expr cx e s = (INL pv,se) /\
     read_result cx pv sr = (INL v,sf) ==> Child) /\
  bind (eval_expr cx e) (read_result cx) s = (INL v,mid) ==> Child
Proof
  simp[vyperStateTheory.bind_def,AllCaseEqs()] >> metis_tac[]
QED

(* A normal result of a qualified target cannot be a local-memory place.
   This uses source evaluation, not the syntactic shape of emitted code. *)
Theorem qualified_assign_place_kind_mods:
  target_root bt = TopLevelNameTarget key /\
  eval_target_place cx bt es = (INL p,ee) ==>
  (?tr slot tv. p = StoragePlace tr slot tv) \/
  (?owner id path. p = ImmutablePlace owner id path)
Proof
  strip_tac >> Cases_on `p` >> simp[] >>
  drule eval_target_place_memory_root >> simp[place_access_root]
QED

Theorem qualified_assign_place_store_bind_mods[local]:
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt mid /\
  type_place_target env bt = SOME (Type dty) /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok mid /\
  (!marks p ee Gz tz z.
    (!tail. eval_target_place cx bt
       (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
       (INL p,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
        ee (PlaceR p) (Type dty) dst Gu tu Gz tz z) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (write_place cx p v) (ee,z,Gz,tz) Q
      (assign_qualified_exit_mods ctx cx RetQ)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_target_place cx bt) (\p. write_place cx p v))
    (mid,u,Gu,tu) Q (assign_qualified_exit_mods ctx cx RetQ)
Proof
  strip_tac >>
  qpat_x_assum `write_place_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_place_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`dty`,`sr`,`st`,`shadow_sr`,`shadow_st`,`dst`,`u`,`Gu`,`tu`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ChildQ ChildR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_place >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!p. storage_trace_frame (write_place _ p _)`]
  >- simp[storage_trace_frame_write_place] >>
  qexists `\H res ee G tn t. ChildQ H res ee G tn t /\ ee.gas_obs = []` >>
  conj_tac >- suspend "target_reached" >>
  irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `ChildR`,Excl "AND_IMP_INTRO"] >> rpt gen_tac >> disch_tac >>
  irule qualified_assign_expr_exit >> simp[]
QED

Resume qualified_assign_place_store_bind_mods[target_reached]:
  qx_genl_tac [`marks`,`res`,`ee`,`Gz`,`tz`,`z`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon ee.storage_trace) res ee Gz tz z /\ ee.gas_obs = []` by
    (first_x_assum drule >> simp[]) >>
  qpat_x_assum `ChildQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  simp[Abbr `ChildQ`,NoAsms] >>
  disch_then (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac)) >>
  disj1_tac >> qexists `p` >> simp[] >>
  first_x_assum irule >> conj_tac
  >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise qualified_assign_place_store_bind_mods[local]

Theorem qualified_assign_write_access_mods:
  !bt. target_root bt = TopLevelNameTarget key ==>
    MEM (WriteAcc (StateRef key)) (accesses_stmt (Assign (BaseTarget bt) e))
Proof
  `(!x:expr. T) /\ (!bt. target_root bt = TopLevelNameTarget key ==>
      MEM (WriteAcc (StateRef key)) (accesses_target bt))` suffices_by
    simp[accesses_stmt_def,accesses_atarget_def] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_root_def, accesses_expr_def]
QED

Theorem qualified_assign_destination_type_mods:
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' ==>
  ?dty. type_place_target env bt = SOME (Type dty) /\
        type_widens_to env.type_defs (expr_type e) dty
Proof
  Cases_on `type_place_target env bt` >>
  simp[type_stmt_def,atarget_accepts_def,AllCaseEqs()] >>
  Cases_on `x` >> simp[type_stmt_def,atarget_accepts_def,AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

(* At a reached qualified destination there is no NONE/INVALID location.
   The empty RHS shortcut still uses a real location and the zero word. *)
Theorem qualified_assign_store_code_mods:
  assign_place_store_code_mods cenv e NONE (dst,SOME loc,SOME (ValPT dty)) =
    compile_store_at_loc cenv.ce_imm_alloca dst (Lit 0w) (SOME loc) /\
  assign_place_store_code_mods cenv e (SOME vv) (dst,SOME loc,SOME (ValPT dty)) =
    comp_bind (unwrap_value cenv vv) (\opd.
      compile_assign_value cenv dst loc opd (is_word_type dty)
        (vv_location vv) dty (lowered_value_type cenv e) (type_memory_bytes cenv dty))
Proof
  simp[assign_place_store_code_mods_def]
QED

Theorem qualified_assign_destination_mods:
  target_root bt = TopLevelNameTarget (owner,id) /\
  eval_target_place cx bt s = (INL p,se) /\
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee
    (PlaceR p) (Type dty) dst G0 tn0 G tn t ==>
  (?tr slot tv. p = StoragePlace tr slot tv /\
     dst = (FST dst,SOME (slot_loc tr),SOME (ValPT dty))) \/
  (?path. p = ImmutablePlace owner id path /\
     dst = (FST dst,SOME LocCode,SOME (ValPT dty)))
Proof
  strip_tac >> drule_all_then strip_assume_tac qualified_assign_place_kind_mods >> gvs[]
  >- (drule_then strip_assume_tac write_target_post_view_mods >>
      drule_then strip_assume_tac write_target_storage_view_mods >>
      PairCases_on `dst` >> gvs[value_type_place_def]) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_then strip_assume_tac write_target_immutable_view_mods >>
  PairCases_on `dst` >> gvs[value_type_place_def]
QED

Definition qualified_assign_code_mods_def[nocompute]:
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
      shadow_sr shadow_st dst <=>
    assign_place_rhs_code_mods cenv bt e sa = (saved,sr) /\
    assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
      (gas_shadow_expr e) shadow_sa = (saved,shadow_sr) /\
    gas_shadow_state sr shadow_sr /\ gas_shadow_state st shadow_st /\
    compile_get_target_ptr compile_expr cenv bt sr = (dst,st) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target bt) shadow_sr = (dst,shadow_st) /\
    assign_place_store_code_mods cenv e saved dst st = ((),sb) /\
    assign_place_store_code_mods (gas_shadow_env T cenv) (gas_shadow_expr e)
      saved dst shadow_st = ((),shadow_sb)
End

(* This exposes the representation at the RHS cut without choosing a different
   source read for the snapshot arm. *)
Theorem qualified_assign_rhs_code_view_mods:
  assign_place_rhs_code_mods cenv bt e sa = (saved,sr) ==>
  (has_length_word (expr_type e) /\ is_empty_value_expr e /\ saved = NONE /\ sr = sa) \/
  (~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
   ?raw vv sm. saved = SOME vv /\ compile_expr cenv (expr_type e) e sa = (raw,sm) /\
      (if expr_can_mutate cenv (target_to_expr bt) then
         compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm = (vv,sr)
       else vv = raw /\ sr = sm))
Proof
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e` >>
  simp[assign_place_rhs_code_mods_def,comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `_ = (raw,sm)` >> Cases_on `expr_can_mutate cenv (target_to_expr bt)` >>
  simp[comp_bind_def,comp_return_def] >>
  Cases_on `compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm` >>
  gvs[]
QED

Definition qualified_assign_rhs_reached_mods_def[nocompute]:
  qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ marks v mid Gu tu u <=>
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u)
End

Definition qualified_assign_target_reached_mods_def[nocompute]:
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
      mid sr st dst u Gu tu marks p ee Gz tz z <=>
    (!tail. eval_target_place cx bt
       (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
       (INL p,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
        ee (PlaceR p) (Type dty) dst Gu tu Gz tz z)
End

Datatype:
  qualified_assign_route = AssignSlotEmpty | AssignSlotWord | AssignSlotCopy
                         | AssignImmEmpty | AssignImmWord | AssignImmCopy
End

Definition qualified_assign_route_mods_def[nocompute]:
  qualified_assign_route_mods route (owner,id) p (saved : vyper_value option) dty dst <=>
    (case route of
       AssignSlotEmpty => IS_NONE saved
     | AssignSlotWord  => IS_SOME saved /\ is_word_type dty
     | AssignSlotCopy  => IS_SOME saved /\ ~is_word_type dty
     | AssignImmEmpty  => IS_NONE saved
     | AssignImmWord   => IS_SOME saved /\ is_word_type dty
     | AssignImmCopy   => IS_SOME saved /\ ~is_word_type dty) /\
    (case route of
       AssignSlotEmpty => T | AssignSlotWord => T | AssignSlotCopy => T
     | _ => F) = (?tr slot tv. p = StoragePlace tr slot tv) /\
    ((?tr slot tv. p = StoragePlace tr slot tv /\
       dst = (FST dst,SOME (slot_loc tr),SOME (ValPT dty))) \/
     (?path. p = ImmutablePlace owner id path /\
       dst = (FST dst,SOME LocCode,SOME (ValPT dty))))
End

Definition qualified_assign_landing_mods_def[nocompute]:
  qualified_assign_landing_mods (DF,lo,d,ctx,shadow_ctx,func,PG) cenv cx st0
      bt e key dty sr st dst saved es s0 RhsQ RetQ Q route <=>
    !ms v mid Gu tu u marks p ee Gz tz z.
      qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ ms v mid Gu tu u /\
      qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
        mid sr st dst u Gu tu marks p ee Gz tz z /\
      qualified_assign_route_mods route key p saved dty dst ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cenv.ce_modules cx st0 (write_place cx p v) (ee,z,Gz,tz) Q
        (assign_qualified_exit_mods ctx cx RetQ)
End

Theorem qualified_assign_select_route_mods[local]:
  target_root bt = TopLevelNameTarget key /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z ==>
  ?route. qualified_assign_route_mods route key p saved dty dst
Proof
  PairCases_on `key` >> simp[qualified_assign_target_reached_mods_def] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then assume_tac) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` assume_tac) >>
  drule_all_then strip_assume_tac qualified_assign_destination_mods >> gvs[]
  >- (Cases_on `saved`
      >- (qexists `AssignSlotEmpty` >> simp[qualified_assign_route_mods_def]) >>
      Cases_on `is_word_type dty`
      >- (qexists `AssignSlotWord` >> simp[qualified_assign_route_mods_def]) >>
      qexists `AssignSlotCopy` >> simp[qualified_assign_route_mods_def]) >>
  Cases_on `saved`
  >- (qexists `AssignImmEmpty` >> simp[qualified_assign_route_mods_def]) >>
  Cases_on `is_word_type dty`
  >- (qexists `AssignImmWord` >> simp[qualified_assign_route_mods_def]) >>
  qexists `AssignImmCopy` >> simp[qualified_assign_route_mods_def]
QED

(* All dispatch runs off one selected destination. In particular the
   empty route does not skip evaluation of the source RHS, only its code. *)
Theorem qualified_assign_target_then_write_mods[local]:
  target_root bt = TopLevelNameTarget key /\
  type_place_target env bt = SOME (Type dty) /\
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt mid /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok mid /\
  qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ ms v mid Gu tu u /\
  (!route. qualified_assign_landing_mods (DF,lo,d,ctx,shadow_ctx,func,PG)
     cenv cx st0 bt e key dty sr st dst saved es s0 RhsQ RetQ Q route) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_target_place cx bt) (\p. write_place cx p v))
    (mid,u,Gu,tu) Q (assign_qualified_exit_mods ctx cx RetQ)
Proof
  strip_tac >> irule qualified_assign_place_store_bind_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`d`,`dst`,`dty`,`env`,`shadow_func`,`shadow_sr`,`shadow_st`,`sr`,`st`] >> simp[] >>
  qx_genl_tac [`marks`,`p`,`ee`,`Gz`,`tz`,`z`] >> strip_tac >>
  `qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z` by
    simp[qualified_assign_target_reached_mods_def] >>
  drule_all qualified_assign_select_route_mods >>
  disch_then (qspec_then `saved` (qx_choose_then `route` assume_tac)) >>
  first_x_assum (qspec_then `route` mp_tac) >>
  rewrite_tac[qualified_assign_landing_mods_def] >>
  disch_then (drule_all_then ACCEPT_TAC)
QED

Theorem qualified_assign_bind_rhs_mods[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!s pv se sr v sf. eval_expr cx e s = (INL pv,se) /\
     read_result cx pv sr = (INL v,sf) ==> body_base_target_full_ok_mods mods exps cx bt) /\
  (gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
   gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res mid Gu tu u. ?v. res = INL v /\ RhsQ H v mid Gu tu u)
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
  (!ms v mid Gu tu u.
    qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ ms v mid Gu tu u /\
    body_base_target_full_ok_mods mods exps cx bt /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok mid ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_target_place cx bt) (\p. write_place cx p v))
      (mid,u,Gu,tu) Q (assign_qualified_exit_mods ctx cx RetQ)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0,G0,tn0) Q
    (assign_qualified_exit_mods ctx cx RetQ)
Proof
  strip_tac >> drule_then assume_tac qualified_assign_rhs_admissible >>
  qpat_x_assum `gas_admissible _ _ _ ==> _` (drule_then assume_tac) >>
  rewrite_tac[qualified_assign_source] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result]
  >~ [`storage_trace_frame (bind (eval_target_place _ _) _)`]
  >- simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_write_place] >>
  qexists `\H res mid Gu tu u. ?v. res = INL v /\ RhsQ H v mid Gu tu u /\ mid.gas_obs = []` >>
  conj_tac >- suspend "rhs_reached" >>
  irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> gvs[] >> goal_assum (drule_at Any)) >>
  BETA_TAC >> rpt gen_tac >> disch_tac >> irule qualified_assign_expr_exit >> simp[]
QED

Resume qualified_assign_bind_rhs_mods[rhs_reached]:
  qx_genl_tac [`ms`,`res`,`mid`,`Gu`,`tu`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `body_base_target_full_ok_mods mods exps cx bt` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all_then ACCEPT_TAC qualified_assign_rhs_releases) >>
  drule_all_then assume_tac qualified_assign_target_admissible >>
  disj1_tac >> qexists `v` >> simp[] >>
  first_x_assum irule >> simp[qualified_assign_rhs_reached_mods_def] >>
  qexists `ms` >> first_assum ACCEPT_TAC
QED

Finalise qualified_assign_bind_rhs_mods[local]

(* C1.6 supplies expr_body_pre_mods. The prefix supplier alone sees the
   optional saved representation: NONE is the code-only shortcut, and SOME
   carries either the original VV or the snapshot made by the paired code.
   The target supplier uses the reached source state and allocated key;
   landing rules then split empty, word and (possibly normalized) copy. *)
Theorem assign_qualified_staged_routes_mods:
  target_root bt = TopLevelNameTarget key /\
  module_body_inv mods src tops cenv cx /\ EVERY (struct_args_unique o SND) mods /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  (!k. MEM (WriteAcc (StateRef k)) (accesses_stmt (Assign (BaseTarget bt) e)) /\
       IS_SOME (FLOOKUP env.bare_global_assignable k) ==>
       IS_SOME (FLOOKUP cenv.ce_module_vars k)) /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\
  (!s pv se sr v sf. eval_expr cx e s = (INL pv,se) /\
     read_result cx pv sr = (INL v,sf) ==> body_base_target_full_ok_mods mods exps cx bt) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  stmt_env cenv lctx ret_ty (Assign (BaseTarget bt) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget bt) e)) shadow_sa =
      (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  (!dty saved sr st shadow_sr shadow_st dst.
    type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type e) dty /\
    struct_args_unique tops /\
    expr_body_pre_mods mods cenv cx env e es /\
    body_expr_full_ok_mods mods exps cx e /\
    qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
      shadow_sr shadow_st dst ==>
    ?RhsQ.
      (gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
       gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
         (\H res mid Gu tu u. ?v. res = INL v /\ RhsQ H v mid Gu tu u)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
      (!ms v mid Gu tu u.
        qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ ms v mid Gu tu u /\
        body_base_target_full_ok_mods mods exps cx bt /\
        (IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
         IS_SOME (FLOOKUP cenv.ce_module_vars key)) /\
        gas_admissible (eval_target_place cx bt) target_place_res_ok mid ==>
        write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt mid /\
        write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
          cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu) /\
      (!route. qualified_assign_landing_mods (DF,lo,d,ctx,shadow_ctx,func,PG)
         cenv cx st0 bt e key dty sr st dst saved es s0 RhsQ RetQ Q route)) ==>
  ce = cenv /\
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0,G0,tn0) Q
    (assign_qualified_exit_mods ctx cx RetQ)
Proof
  strip_tac >> drule_then assume_tac module_body_inv_lookup >>
  `struct_args_unique tops` by
    (qpat_x_assum `EVERY _ mods` mp_tac >> simp[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `(src,tops)` mp_tac) >> simp[ALOOKUP_MEM]) >>
  drule_then strip_assume_tac qualified_assign_destination_type_mods >>
  drule_then assume_tac qualified_assign_write_access_mods >>
  drule_all assign_place_paired_code_mods >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`saved`,`sr`,`shadow_sr`,`dst`,`st`,`shadow_st`] strip_assume_tac)) >>
  simp[] >>
  `qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst` by simp[qualified_assign_code_mods_def] >>
  `IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
   IS_SOME (FLOOKUP cenv.ce_module_vars key)` by
    (disch_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `!dty saved sr st shadow_sr shadow_st dst. _ ==> ?RhsQ. _`
    (drule_all_then (qx_choose_then `RhsQ` strip_assume_tac)) >>
  irule qualified_assign_bind_rhs_mods >>
  reverse conj_tac >- (qexists `lctx` >> simp[]) >>
  qexistsl [`RhsQ`,`exps`,`mods`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`ms`,`v`,`mid`,`Gu`,`tu`,`u`] >> strip_tac >>
  qpat_x_assum `!ms v mid Gu tu u. _ ==> write_place_sim_mods _ _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  irule qualified_assign_target_then_write_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`RhsQ`,`d`,`dst`,`dty`,`e`,`env`,`es`,`key`,`ms`,`s0`,`saved`,
            `shadow_func`,`shadow_sr`,`shadow_st`,`sr`,`st`] >> simp[]
QED
