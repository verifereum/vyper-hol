(* An assignment reads its RHS before selecting the place. The compiled
   prefix can either retain the value's representation or snapshot it. *)
Theory bodyAssignLocalPlaceRoutesMods
Ancestors
  bodyWriteTargetStageMods bodyFullPredsMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  gasShadowCompileStmtHelpers gasShadowCompileConvert gasShadowCompileBase
  gasShadowCompileHelpers
  stmtSimProps bodyPtrDefs haltExitProj targetPlaceSim targetPlaceSimCases
  vyperInterpreter vyperState vyperAST vyperExprNoControl
  vyperStorageTrace vyperStorageFootprint gasContext exprSimDefs stmtSimDefs
  fragExec context venomState stmtLowering loweringPosts compileEnv exprLowering
  gasShadow gasShadowState
Libs monadsyntax

Theorem assign_place_source_bind_mods[local]:
  eval_stmt cx (Assign (BaseTarget bt) e) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_target_place cx bt) (\p. write_place cx p v))
Proof
  simp[Once evaluate_def,bind_assoc]
QED

Theorem assign_place_rhs_admissible_mods[local]:
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
     qexistsl [`ee`,`gs`] >> simp[assign_place_source_bind_mods,Once vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def,expr_res_ok_def,no_control_exc_def]
QED

Theorem assign_place_target_admissible_mods[local]:
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix ++ tail) =
    (INL v,mid with gas_obs := tail)) ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok mid
Proof
  strip_tac >> rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `INR ex` >> `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >> qexistsl [`ee`,`prefix ++ gs`] >>
     simp[assign_place_source_bind_mods,Once vyperStateTheory.bind_def] >>
     simp[vyperStateTheory.bind_def]) >>
  gvs[stmt_res_ok_def,target_place_res_ok_def,no_control_exc_def]
QED

Theorem assign_place_releases_target_mods[local]:
  (!s pv s1 sr v s2. eval_expr cx e s = (INL pv,s1) /\
     read_result cx pv sr = (INL v,s2) ==> Child) /\
  bind (eval_expr cx e) (read_result cx) s = (INL v,mid) ==> Child
Proof
  simp[vyperStateTheory.bind_def,AllCaseEqs()] >> metis_tac[]
QED

Theorem assign_local_target_memory_mods[local]:
  target_root bt = NameTarget id /\ eval_target_place cx bt es = (INL p,ee) ==>
  ?path. p = MemoryPlace id path
Proof
  simp[Once evaluate_def,vyperStateTheory.bind_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac aug_place_name_root_base >> gvs[get_place_def,return_def]
QED

Theorem assign_expr_exit_as_stmt_mods[local]:
  expr_exit (res : 'a + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?ex. res = INR ex /\
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==>
      !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  simp[GSYM expr_exit_def,stmt_exit_ptr_def,expr_exit_INR_type,halt_exit_INR_type] >>
  Cases_on `r` >> simp[expr_exit_def]
QED

Theorem assign_local_place_memory_result_mods[local]:
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sb s0 ee
    (PlaceR (MemoryPlace id path)) (Type ty) dst G0 tn0 G tn t ==>
  dst = (FST dst,SOME LocMemory,SOME (ValPT ty))
Proof
  simp[write_target_post_mods_def,write_target_location_mods_def,place_ptr_rel_def,
    value_type_place_def] >> PairCases_on `dst` >> simp[] >> strip_tac >> simp[]
QED

(* Apply the place supplier at the selected source and machine cursor. Only
   a normal target result is classified by the local root. *)
Theorem assign_local_place_write_bind_mods:
  target_root bt = NameTarget id /\
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt mid /\
  type_place_target env bt = SOME (Type dty) /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu /\
  gas_admissible (eval_target_place cx bt) target_place_res_ok mid /\
  (!marks path ee Gz tz z.
    (!tail. eval_target_place cx bt
       (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
       (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
    (?entry w. lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL w) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
        ee (PlaceR (MemoryPlace id path)) (Type dty) dst Gu tu Gz tz z) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tz) Q
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_target_place cx bt) (\p. write_place cx p v))
    (mid,u,Gu,tu) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s.
        (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
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
      qexistsl_tac [`mid'`,`t`,`v'`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!p. storage_trace_frame (write_place _ p _)`]
  >- simp[storage_trace_frame_write_place] >>
  qexists `\H res ee G tn t. ChildQ H res ee G tn t /\ ee.gas_obs = []` >>
  conj_tac >- suspend "target_normal" >>
  irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `ChildR`,Excl "AND_IMP_INTRO"] >>
  rpt gen_tac >> disch_tac >> irule assign_expr_exit_as_stmt_mods >> simp[]
QED

Resume assign_local_place_write_bind_mods[target_normal]:
  qx_genl_tac [`marks`,`res`,`ee`,`Gz`,`tz`,`z`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon ee.storage_trace) res ee Gz tz z /\ ee.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then ACCEPT_TAC)) >>
  pop_assum mp_tac >> simp[Abbr `ChildQ`, NoAsms, Excl "AND_IMP_INTRO"] >>
  qpat_x_assum `(\H res ee G tn t. ?p. _) _ _ _ _ _ _` mp_tac >> BETA_TAC >>
  disch_then (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac)) >> disch_tac >>
  `?path. p = MemoryPlace id path` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all_then ACCEPT_TAC assign_local_target_memory_mods) >>
  qpat_x_assum `p = MemoryPlace id _` SUBST_ALL_TAC >>
  `dst = (FST dst,SOME LocMemory,SOME (ValPT dty))` by
    drule_then ACCEPT_TAC assign_local_place_memory_result_mods >>
  simp[] >>
  qpat_x_assum `!marks path ee Gz tz z. _` irule >> conj_tac
  >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED
Finalise assign_local_place_write_bind_mods[local]

(* NONE is the empty-value shortcut. In this case the source still reads
   the RHS, but its replay ends at the original compiler cursor. *)
Definition assign_place_rhs_code_mods_def:
  assign_place_rhs_code_mods cenv bt e =
    if has_length_word (expr_type e) /\ is_empty_value_expr e then
      comp_return NONE
    else comp_bind (compile_expr cenv (expr_type e) e) (\raw.
      comp_bind
        (if expr_can_mutate cenv (target_to_expr bt) then
           compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw)
         else comp_return raw)
        (\vv. comp_return (SOME vv)))
End

Definition assign_place_store_code_mods_def:
  assign_place_store_code_mods cenv e saved dst =
    case saved of
      NONE => compile_store_at_loc cenv.ce_imm_alloca (FST dst) (Lit 0w) (FST (SND dst))
    | SOME vv =>
      comp_bind (unwrap_value cenv vv) (\opd.
        let sty = lowered_value_type cenv e in
        let dty = case SND (SND dst) of SOME (ValPT t) => t | _ => sty in
          case FST (SND dst) of
            SOME loc => compile_assign_value cenv (FST dst) loc opd (is_word_type dty)
                (vv_location vv) dty sty (type_memory_bytes cenv dty)
          | NONE => emit_void INVALID [])
End

Theorem assign_place_memory_store_code_mods:
  assign_place_store_code_mods cenv e NONE (dst,SOME LocMemory,SOME (ValPT dty)) =
    emit_void MSTORE [dst;Lit 0w] /\
  assign_place_store_code_mods cenv e (SOME vv) (dst,SOME LocMemory,SOME (ValPT dty)) =
    comp_bind (unwrap_value cenv vv) (\opd.
      compile_assign_value cenv dst LocMemory opd (is_word_type dty)
        (vv_location vv) dty (lowered_value_type cenv e) (type_memory_bytes cenv dty))
Proof
  simp[assign_place_store_code_mods_def,compile_store_at_loc_def]
QED

Theorem assign_place_stmt_code_mods:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget bt) e) sa = (ce,sb) /\
  assign_place_rhs_code_mods cenv bt e sa = (saved,sr) /\
  compile_get_target_ptr compile_expr cenv bt sr = (dst,st) ==>
  ce = cenv /\ assign_place_store_code_mods cenv e saved dst st = ((),sb)
Proof
  strip_tac >>
  `stmt_env cenv lctx ret_ty (Assign (BaseTarget bt) e) sa =
     (cenv,SND (assign_place_store_code_mods cenv e saved dst st))` suffices_by
    (Cases_on `assign_place_store_code_mods cenv e saved dst st` >> simp[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `assign_place_rhs_code_mods _ _ _ _ = _` mp_tac >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e` >>
  simp[stmt_env_def,declare_stmt_local_def,assign_place_rhs_code_mods_def,
       assign_place_store_code_mods_def,Once compile_stmt_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,pairTheory.ELIM_UNCURRY] >>
  strip_tac >> gvs[comp_bind_def,pairTheory.ELIM_UNCURRY]
QED

Theorem assign_place_rhs_shadow_mods:
  gas_shadow_compiles (assign_place_rhs_code_mods cenv bt e)
    (assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt) (gas_shadow_expr e))
Proof
  simp[assign_place_rhs_code_mods_def,gas_shadow_expr_type] >>
  IF_CASES_TAC >- simp[gas_shadow_compiles_return] >>
  simp[gas_shadow_expr_can_mutate] >>
  irule gas_shadow_compiles_bind >> simp[gas_shadow_stmt_compile_expr_env] >>
  gen_tac >> BETA_TAC >>
  irule gas_shadow_compiles_bind >> simp[gas_shadow_compiles_return] >>
  IF_CASES_TAC >> simp[gas_shadow_compiles_return,gas_shadow_compiles_snapshot_vv]
QED

Theorem assign_place_paired_code_mods:
  stmt_env cenv lctx ret_ty (Assign (BaseTarget bt) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget bt) e)) shadow_sa =
      (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa ==>
  ce = cenv /\ ?saved sr shadow_sr dst st shadow_st.
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
Proof
  strip_tac >> Cases_on `assign_place_rhs_code_mods cenv bt e sa` >>
  rename1 `_ = (saved,sr)` >>
  Cases_on `assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
    (gas_shadow_expr e) shadow_sa` >> rename1 `_ = (_,shadow_sr)` >>
  `gas_shadow_compiles (assign_place_rhs_code_mods cenv bt e)
    (assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt) (gas_shadow_expr e))`
    by irule assign_place_rhs_shadow_mods >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sr` >>
  rename1 `_ = (dst,st)` >>
  Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
    (gas_shadow_target bt) shadow_sr` >> rename1 `_ = (_,shadow_st)` >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
    (compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target bt))`
    by irule gas_shadow_stmt_get_target_ptr_env >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sr`,`shadow_sr`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all assign_place_stmt_code_mods >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac) >>
  `stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (Assign (BaseTarget (gas_shadow_target bt)) (gas_shadow_expr e)) shadow_sa =
      (gas_shadow_env T cenv,shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def,gas_shadow_assignment_def]) >>
  simp[] >>
  drule_all assign_place_stmt_code_mods >> simp[]
QED

(* The three suppliers describe, respectively, the RHS representation,
   the target entry at the reached cursor, and the selected physical write.
   The write supplier may use the word, empty, typed-copy or bytes path,
   then install the replacement into the linked statement post Q. *)
Theorem assign_local_place_routes_from_writes_mods:
  target_root bt = NameTarget id /\
  type_place_target env bt = SOME (Type dty) /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!s pv s1 sr0 v s2. eval_expr cx e s = (INL pv,s1) /\
     read_result cx pv sr0 = (INL v,s2) ==> body_base_target_full_ok_mods mods exps cx bt) /\
  stmt_env cenv lctx ret_ty (Assign (BaseTarget bt) e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty
    (gas_shadow_stmt (Assign (BaseTarget bt) e)) shadow_sa =
      (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  (!saved sr shadow_sr dst st shadow_st.
    assign_place_rhs_code_mods cenv bt e sa = (saved,sr) /\
    assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
      (gas_shadow_expr e) shadow_sa = (saved,shadow_sr) /\
    gas_shadow_state sr shadow_sr /\ gas_shadow_state st shadow_st /\
    compile_get_target_ptr compile_expr cenv bt sr = (dst,st) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target bt) shadow_sr = (dst,shadow_st) /\
    assign_place_store_code_mods cenv e saved dst st = ((),sb) /\
    assign_place_store_code_mods (gas_shadow_env T cenv) (gas_shadow_expr e)
      saved dst shadow_st = ((),shadow_sb) ==>
    ?RhsQ.
  (gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
   gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res mid Gu tu u. ?v. res = INL v /\ RhsQ H v mid Gu tu u)
     (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) /\
  (!marks v mid Gu tu u.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u) /\
    body_base_target_full_ok_mods mods exps cx bt /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok mid ==>
    write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt mid /\
    write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu) /\
  (!ms v mid Gu tu u marks path ee Gz tz z.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit ms s0.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u) /\
    (!tail. eval_target_place cx bt
       (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
       (INL (MemoryPlace id path),ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    dst = (FST dst,SOME LocMemory,SOME (ValPT dty)) /\
    (?entry w. lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL w) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
        ee (PlaceR (MemoryPlace id path)) (Type dty) dst Gu tu Gz tz z) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (write_place cx (MemoryPlace id path) v) (ee,z,Gz,tz) Q
      (\H res ee gt r.
        (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s.
          (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0,G0,tn0) Q
    (\H res ee gt r.
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s.
        (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all assign_place_paired_code_mods >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`saved`,`sr`,`shadow_sr`,`dst`,`st`,`shadow_st`] strip_assume_tac)) >>
  qpat_x_assum `!saved sr shadow_sr dst st shadow_st. _ ==> ?RhsQ. _`
    (qspecl_then [`saved`,`sr`,`shadow_sr`,`dst`,`st`,`shadow_st`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (qx_choose_then `RhsQ` strip_assume_tac) >>
  drule_then assume_tac assign_place_rhs_admissible_mods >>
  qpat_x_assum `gas_admissible _ _ _ ==> _` (drule_then assume_tac) >>
  rewrite_tac[assign_place_source_bind_mods] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl [`mid`,`t`,`v`] >> rule_assum_tac BETA_RULE >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame (bind (eval_target_place _ _) _)`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_write_place]) >>
  qexists `\H res mid Gu tu u. ?v. res = INL v /\ RhsQ H v mid Gu tu u /\ mid.gas_obs = []` >>
  conj_tac >- suspend "rhs_normal" >>
  irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> gvs[] >> goal_assum (drule_at Any)) >>
  BETA_TAC >> rpt gen_tac >> disch_tac >> irule assign_expr_exit_as_stmt_mods >> simp[]
QED

Resume assign_local_place_routes_from_writes_mods[rhs_normal]:
  qx_genl_tac [`ms`,`res`,`mid`,`Gu`,`tu`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> RhsQ H v mid Gu tu u` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `body_base_target_full_ok_mods mods exps cx bt` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_all_then ACCEPT_TAC assign_place_releases_target_mods) >>
  drule_all_then assume_tac assign_place_target_admissible_mods >>
  qpat_x_assum `!marks v mid Gu tu u. _ ==> write_place_sim_mods _ _ _ _ _ _ /\ _`
    (qspecl_then [`ms`,`v`,`mid`,`Gu`,`tu`,`u`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> simp[] >>
  irule assign_local_place_write_bind_mods >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`d`,`dst`,`dty`,`env`,`id`,`shadow_func`,`shadow_sr`,`shadow_st`,`sr`,`st`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!ms v mid Gu tu u marks path ee Gz tz z. _`
    (qspecl_then [`ms`,`v`,`mid`,`Gu`,`tu`,`u`] mp_tac) >>
  disch_then irule >> simp[] >> goal_assum (drule_at Any)
QED
Finalise assign_local_place_routes_from_writes_mods
