(*
 * Augmented assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAugAssign
Ancestors stateFrame[qualified,ignore_grammar] bodyPtrDefs[qualified,ignore_grammar]
  stateRelProj exprBodyPreProps[qualified,ignore_grammar]
  bodyTypedTargetScope augAssignFullTargetRoutes augAssignFullEntryPre augAssignFullCodeStages
  augAssignFullBindStages augAssignFullSourceReplay augAssignFullRhsSaved
  augAssignFullLoad augAssignFullImmutableValidLoad augAssignFullImmutableCertificate
  augAssignFullStageFrames augAssignFullImmutableStageFrames augAssignFullWriteback
  augAssignFullOperandReady augAssignFullOperatorSource
  augAssignFullCurrentSource augAssignFullOperator bodyFullBuiltinWordPowCompose
  exprSimSource targetPlaceSim
  bodyFullTarget bodyFullTargetDefs bodyFullTargetRoots bodyPtrPopTargetFragTransport
  stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory stmtSimProps loweringPosts allocLimits
  gasContext targetPlaceSimCases stmtSimDefs vyperExprNoControl
  tuplePlaceHeadGas gasOutcomeFullGuarded
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  bodyFullShared vyperEvalExprPreservesScopesDom vyperScopePreservation
  vyperStatePreservation vyperStorageFootprint vyperStorageTrace
  bodyFullIfExpReach
  augAssignFullLoadImmutableResources augAssignFullLoadFrame
  context exprSimCopy bodyFullAssign immutableAssignStore
  bodyImmutableAugAssignStore bodyImmutableAugAssignExec vyperPlaceFrames
  augAssignFullImmutableDeadMask exprSafeOperand words
  bodyAugPlaceTarget bodyInvCodeProps constSubstCorrect vyperTypeConstantCells
  immutableWordStorePath immutableRegionFrameProps immutableRegionTypingProps immutableDeployAssignRestore
  immutableDeployAssignMemoryFrame immutableCtorWordStoreGhost
  targetOverlapAccess vyperImmutableAccessFrame bodyFullSubscriptLiveImmSelect
  vyperImmutableMetadataFrame vyperTypeInvariants augAssignFullEntryFrame
  stmtSimDeclStore exprSimProps[qualified,ignore_grammar]
  placeMemoryPathRebuild[qualified,ignore_grammar] fragExec[qualified,ignore_grammar]
  bodyFullShadowBodyInv[qualified,ignore_grammar] bodyInvSplit[qualified,ignore_grammar]
  vyperTypeEnv[qualified,ignore_grammar] exprLoweringProps[qualified,ignore_grammar]
  valueEncodingProps[qualified,ignore_grammar] loweringStateRelDefs[qualified,ignore_grammar]

val _ = Parse.hide "body";

Theorem augassign_scopes_dom[local]:
  eval_stmt cx (AugAssign aty target bop e) es = (res,ee) ==>
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  simp[augassign_source_bind, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac eval_target_place_preserves_scopes_dom >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac eval_expr_preserves_scopes_dom >> imp_res_tac read_result_scopes >>
  imp_res_tac lift_sum_state >> imp_res_tac write_place_scopes_dom >>
  gvs[] >> metis_tac[]
QED

Theorem augassign_sep_outcome[local]:
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0) /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (AugAssign aty target bop e)) (es,s0,G0,tn0)
    (\H res ee G tn t.
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (return_buf_sep d cenv ee t ==> Q H res ee G tn t)) R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (AugAssign aty target bop e)) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\
       (!bw cap. d = SOME (bw,cap) ==> allocas_from _ t)) R` (irule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    (qpat_x_assum `ee.gas_obs = []` (fn th => simp[GSYM th])) >>
  `eval_stmt cx (AugAssign aty target bop e) (es with gas_obs := xs) = (res,ee)` by
    (qpat_assum `ee with gas_obs := [] = ee` (fn eq =>
       qpat_assum `!tail. eval_stmt _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,eq])))) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (mp_tac (Q.INST [`st` |-> `es with gas_obs := xs`,
       `f` |-> `eval_stmt cx (AugAssign aty target bop e)`,
       `res` |-> `res`, `st'` |-> `ee`, `H` |-> `H`,
       `st0` |-> `st0`, `cx` |-> `cx`]
       (INST_TYPE [alpha |-> oneSyntax.one_ty] valid_horizon_frame)) >>
     simp[evaluate_storage_trace_frame]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule augassign_scopes_dom >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  first_x_assum irule >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  qexistsl_tac [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[]
QED

(* A local. *)
Theorem body_augassign_local_full:
  !cx aty bop id e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (NameTarget id) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty (NameTarget id) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (NameTarget id) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (NameTarget id) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (NameTarget id) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (NameTarget id) bop e)))
      (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) es
Proof
  suspend "use_ordinary"
QED

(* A scalar top-level variable. *)
Theorem body_augassign_toplevel_word_full:
  !cx aty bop nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget nsid) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (TopLevelNameTarget nsid) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (TopLevelNameTarget nsid) bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)))
      (eval_stmt cx (AugAssign aty (TopLevelNameTarget nsid) bop e)) es
Proof
  suspend "use_ordinary"
QED

(* A field of a struct local. *)
Theorem body_augassign_attr_local_full:
  !cx aty bop id fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  suspend "use_ordinary"
QED

(* A field of a storage struct. *)
Theorem body_augassign_attr_storage_full:
  !cx aty bop nsid fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (TopLevelNameTarget nsid) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) es
Proof
  suspend "use_ordinary"
QED

Theorem body_augassign_nested_immutable_full:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) /\
    immutable_root cx t /\ ~(?nsid. t = TopLevelNameTarget nsid) /\
    ~supported_stmt_expr_exists (const_name_root cx) (AugAssign aty t bop e) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule (cj 1 aug_place_typing) >> strip_tac >>
  drule_all aug_place_typing_word >> strip_tac >>
  `IS_SOME (type_place_target env t)` by simp[] >>
  drule_all typed_immutable_target_root >>
  disch_then (qx_choosel_then [`id`,`root_ty`] STRIP_ASSUME_TAC) >>
  `target_indices_pre cenv cx env t` by
    (drule_all augassign_entry_target_indices_pre >> simp[]) >>
  `cenv.ce_module = NONE` by metis_tac[bodyInvCodePropsTheory.body_inv_module_locations] >>
  `imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t es` by
    (mp_tac (Q.SPECL [`t`,`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
       `func`,`shadow_func`,`cenv`,`cx`,`env`,`es`,`id`]
       body_imm_target_place_sim_full) >> simp[]) >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule augassign_sep_outcome >>
  qexistsl_tac [`cenv`,`d`,`sa`] >> simp[] >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    (simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
     Cases_on `res` >> simp[target_place_res_ok_def] >>
     rename1 `eval_target_place cx t _ = (INR ex,ee)` >>
     `no_control_exc ex` by
       metis_tac[vyperExprNoControlTheory.eval_target_place_no_control] >>
     qpat_assum `gas_admissible _ _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     simp[augassign_source_bind,bind_def,stmt_res_ok_def,no_control_exc_def] >>
     gvs[gas_admissible_def,target_place_res_ok_def,augassign_source_bind,
         bind_def,stmt_res_ok_def,no_control_exc_def]) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choose_then `r` (qx_choose_then `ca` (qx_choose_then `shadow_ca`
      (fn th =>
        case rev (CONJUNCTS th) of
          cases::slices => map_every assume_tac (rev slices) >> assume_tac cases
        | [] => NO_TAC))))) >>
  qpat_x_assum `imm_target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [imm_target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`aty`,`sa`,`ca`,`shadow_sa`,`shadow_ca`,
                           `r`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx t) _ targetQ targetR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
     (\H res ee G tn v. targetQ H res ee G tn v /\
       (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z))
     targetR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` kall_tac >>
  qmatch_goalsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ _ stmtQ stmtR` >>
  rewrite_tac[augassign_source_bind] >>
  irule augassign_target_bind_full >>
  qexists_tac `\H res ee G tn u. targetQ H res ee G tn u /\
    ~u.vs_halted /\ ee.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z)` >>
  reverse conj_tac
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ targetR` (irule_at Any) >>
      conj_tac >- (simp[] >> rpt strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
      simp[Abbr `targetR`,Abbr `stmtR`] >>
      rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[] >> drule_all augassign_expr_exit_to_stmt_exit >>
      disch_then (qspecl_then [`gt`,`RetQ`] strip_assume_tac) >> simp[] >> gvs[]) >>
  suspend "nested_target_endpoint"
QED

Resume body_augassign_nested_immutable_full[nested_target_endpoint]:
  qx_genl_tac [`marks`,`res`,`st`,`Gtarget`,`tnt`,`v`] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon st.storage_trace` >>
  `valid_horizon cx st0 H0 st.storage_trace` by
    fs[Abbr `H0`,vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!H. valid_horizon _ _ H st.storage_trace ==> targetQ _ _ _ _ _ _ /\ _`
       (qspec_then `H0` (drule_then strip_assume_tac)) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H st.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (targetQ = _)` (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`root`,`path`]
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) STRIP_ASSUME_TAC) >>
  `root = id` by fs[] >> qpat_x_assum `root = id` SUBST_ALL_TAC >>
  qabbrev_tac `p = ImmutablePlace (NONE:num option) id path` >>
  disj1_tac >> qexists_tac `p` >> simp[] >>
  qpat_assum `imm_target_post H0 _ _ _ _ _ _ _ _ _ id path aty r v`
    (strip_assume_tac o REWRITE_RULE [imm_target_post_def]) >>
  qpat_x_assum `_ \/ ?loc cur rhs result s1 s2 s3 ss1 ss2 ss3. _`
    (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (qx_choosel_then [`loc`,`old`,`rhsop`,`dst`,`cb`,`cc`,`cd`,
        `shadow_cb`,`shadow_cc`,`shadow_cd`] STRIP_ASSUME_TAC))
  >- fs[] >>
  `loc = LocCode` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >> gvs[] >>
  `sa.cs_next_var <= ca.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv ca` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv ca v` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `st with gas_obs := [] = st` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  qabbrev_tac `reads = gas_explicit marks s0.vs_gas_readings` >>
  `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)` by
    (qpat_assum `st with gas_obs := [] = st` (fn upd =>
       qpat_assum `!tail. eval_target_place cx t _ = _`
         (qspec_then `[]` (mp_tac o PURE_REWRITE_RULE [APPEND_NIL,upd]))) >>
     simp[Abbr `p`,Abbr `reads`]) >>
  `body_const_cells_agree [(NONE,tops)] cx env st` by
    (irule body_const_cells_agree_target >>
     qpat_assum `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)`
       (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `expr_body_pre cenv cx env e st` by
    (drule_all aug_place_rhs_pre_target_gas_obs >> simp[]) >>
  suspend "nested_load"
QED

Resume body_augassign_nested_immutable_full[nested_load]:
  rename1 `evaluate_subscripts itv iv path = INL cur` >>
  rename1 `mem_path_offset itv path = SOME (k,ptv)` >>
  rename1 `FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)` >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[finite_mapTheory.FLOOKUP_EMPTY] >>
  rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
  `expr_sim_inv cenv cx env st` by
    metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
  `dead_lo_ok H0 (DF H0) lo cenv cx` by
    (qpat_assum `!H. dead_lo_ok H _ _ _ _` (qspec_then `H0` ACCEPT_TAC)) >>
  drule_all augassign_immutable_path_load_resources >> strip_tac >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `read_place cx p st = (INL cur,st) /\ place_type_value cx p st = (INL ptv,st)` by
    simp[Abbr `p`,read_place_def,place_type_value_def,get_immutables_def,
         get_address_immutables_def,bind_def,return_def,lift_sum_def,lift_option_type_def] >>
  `compile_imm_load_word T cenv.ce_imm_alloca (FST r) ca = (old,cb)` by
    fs[compile_ptr_load_def] >>
  `allocas_from lo v /\ lo <= v.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `op_taint tnt (FST r) = {}` by fs[target_ptr_ok_def,Abbr `p`] >>
  `op_prov Gtarget (FST r) = NONE` by first_assum ACCEPT_TAC >>
  `copy_old_operand ca (FST r)` by simp[exprSimCopyTheory.copy_old_operand_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region v = SOME 0w /\ copy_old_operand ca region /\
     op_taint tnt region = {} /\ op_prov Gtarget region = NONE` by suspend "nested_load_base" >>
  `w2n (n2w (off+k) : bytes32) + 32 <= lo /\
   mem_word_taint tnt.t_mem (w2n (n2w (off+k) : bytes32)) = {}` by
    (qpat_assum `w2n (n2w (off+k) : bytes32) = _` (fn th => PURE_REWRITE_TAC [th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (FST r) v = SOME (n2w (off+k))` by
    (once_rewrite_tac [arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
  drule_all augassign_ctor_word_load_at >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`u`,`Gload`,`tnload`] strip_assume_tac)))))) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    stmt_state_rel H ctx func cenv cx st u /\ storage_well_formed_on cx st (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx st Gload tnload u /\
    target_ptr_ok cenv (PlaceR p) r Gload tnload u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload /\
    return_buf_frame d cenv cb u /\ alloca_history func u /\
    u.vs_alloca_next = v.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    eval_operand (FST r) u = SOME (n2w (off+k))` by suspend "nested_load_frame" >>
  pop_assum (mk_asm "loadPost") >>
  `eval_operand old u = SOME (typed_val_to_w256 ptv cur)` by asm_rewrite_tac[] >>
  `op_prov Gload (FST r) = NONE` by
    (Cases_on `FST r` >> fs[ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  suspend "nested_rhs_compose"
QED

Resume body_augassign_nested_immutable_full[nested_load_base]:
  `lo <> 0` by decide_tac >>
  `immutable_base_zero cenv v` by metis_tac[stmt_state_rel_immutable_base_zero] >>
  qpat_assum `ghost_inv_at (DF H0) lo d cenv cx st Gtarget tnt v`
    (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  qpat_assum `immutable_base_zero cenv v`
    (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.immutable_base_zero_def]) >>
  qpat_assum `local_ptrs_reserved cenv ca`
    (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
  qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> _`
    (assume_tac o REWRITE_RULE [ptrDisciplineTheory.op_taint_def]) >>
  Cases >> simp[copy_old_operand_def,ptrDisciplineTheory.op_taint_def,
                ptrDisciplineTheory.op_prov_def] >> metis_tac[]
QED

Resume body_augassign_nested_immutable_full[nested_load_frame]:
  qx_gen_tac `H` >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx st v /\ storage_well_formed_on cx st (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx st Gtarget tnt v` by
    (qpat_assum `Abbrev (targetQ = _)` (fn abbreviation =>
       qpat_assum `!K. valid_horizon _ _ K st.storage_trace ==> targetQ K _ _ _ _ _ /\ _`
         (qspec_then `H` (drule_then
           (strip_assume_tac o BETA_RULE o
            REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] abbreviation])))) >>
     fs[imm_target_post_def]) >>
  drule_all (Q.INST [`entry` |-> `sa`,`sa` |-> `ca`,`sb` |-> `cb`,
    `es` |-> `es`,`st` |-> `st`,`s0` |-> `s0`,`s` |-> `v`,
    `G` |-> `Gtarget`,`G1` |-> `Gload`,`tn` |-> `tnt`,`tn1` |-> `tnload`,
    `D` |-> `DF H`,`addr` |-> `n2w (off+k)`] augassign_load_endpoint_frame) >>
  simp[]
QED

Resume body_augassign_nested_immutable_full[nested_rhs_compose]:
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok st` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `!D. gas_origin_ptr_path _ (v,Gtarget,tnt) [] (OK u,Gload,tnload)`
       (qspec_then `DF H0` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func v fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi))))) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    stmt_state_rel H ctx func cenv cx st u /\
    storage_well_formed_on cx st (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx st Gload tnload u` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "loadPost" (qspec_then `H` mp_tac) >> simp[]) >>
  asm "loadPost" (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `local_ptrs_reserved cenv cb` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. FST r = Var x ==> not_fresh_at cb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule_all (Q.INST [`target` |-> `t`, `es` |-> `st`, `sa` |-> `cb`, `sb` |-> `cc`,
                    `old` |-> `old`, `place` |-> `r`] augassign_rhs_saved_outcome) >>
  disch_then (qspecl_then [`RetQ`,`PG`] assume_tac) >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ rhsQ rhsR` >>
  `!gs. read_place cx p (st with gas_obs := gs) = (INL cur,st with gas_obs := gs)` by
    (`read_result cx (PlaceR p) st = (INL cur,st)` by simp[read_result_def] >>
     drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[read_result_def]) >>
  drule_then assume_tac exprSimIfExpWidenedAdapterTheory.place_type_value_gas_obs >>
  qabbrev_tac `goRhs = bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))` >>
  reverse (qsuff_tac `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 goRhs (st,v,Gtarget,tnt) stmtQ stmtR`)
  >- (irule (Q.INST [`s1` |-> `u`,`G1` |-> `Gload`,`tn1` |-> `tnload`]
        gas_outcome_full_zero_prefix_guarded) >>
      simp[] >> conj_tac
      >- (simp[Abbr `goRhs`] >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
      qexistsl_tac [`Gload`,`tnload`,`u`] >> conj_tac
      >- (qx_gen_tac `H` >> disch_tac >>
          asm "loadPost" (qspec_then `H` mp_tac) >> simp[]) >>
      simp[Abbr `goRhs`] >> irule augassign_rhs_bind_full >>
      qexists_tac `\H res ee G tn q. rhsQ H res ee G tn q /\ ~q.vs_halted /\ ee.gas_obs = []` >>
      reverse conj_tac
      >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ rhsQ rhsR` (irule_at Any) >>
          simp[Abbr `rhsR`,Abbr `stmtR`] >> metis_tac[]) >>
      suspend "nested_rhs") >>
  disch_tac >>
  irule (Q.INST_TYPE [`:'a` |-> `:unit`]
    gasOutcomeFullStmtsTheory.gas_outcome_full_handler_transport) >>
  qexistsl_tac [`stmtQ`,`stmtR`,`st`,`goRhs`] >> simp[] >>
  `!gs. bind (read_place cx p) (\cur.
      bind (place_type_value cx p) (\ptv.
        bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p)))) (st with gas_obs := gs) =
    goRhs (st with gas_obs := gs)` by simp[bind_def,Abbr `goRhs`] >>
  simp[gasStorageTheory.gas_bad_storage_at_def] >> conj_tac
  >- (qx_genl_tac [`ms`,`err`,`ee`,`leaf`,`fin`] >> disch_tac >>
      qexistsl_tac [`err`,`ee`] >>
      simp[Once ignore_bind_def,bind_assoc] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[vyperStateTheory.evaluation_state_component_equality] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[vyperStateTheory.evaluation_state_component_equality] >>
      `st with gas_obs := [] = st` by
        simp[vyperStateTheory.evaluation_state_component_equality] >>
      qpat_x_assum `gas_exempt_cert _ _ _ (ignore_bind goRhs _) _ _ _ _` mp_tac >>
      simp[Abbr `goRhs`,ignore_bind_def,bind_assoc]) >>
  qx_genl_tac [`ms`,`res`,`ee`,`result`,`G'`,`tn'`] >> strip_tac >>
  qexistsl_tac [`ms`,`res`,`ee`,`result`,`G'`,`tn'`] >> simp[]
QED

Resume body_augassign_nested_immutable_full[nested_rhs]:
  qx_genl_tac [`ms`,`res`,`ee`,`Gq`,`tnq`,`q`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (rhsQ = _)` (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `rhs` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) >>
  disj1_tac >> qexists_tac `rhs` >> simp[] >>
  qabbrev_tac `rhsReads = gas_explicit ms u.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (st with gas_obs := rhsReads) = (INL rhs,ee)` by
    (pop_assum (fn upd =>
       qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,upd])))) >>
  `is_word_type (expr_type e)` by
    (drule_all aug_place_typing_word >> simp[]) >>
  `expr_body_pre cenv cx env e (st with gas_obs := rhsReads)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all (REWRITE_RULE [ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval) >> simp[]) >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >>
  simp[] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME tvR` >>
  drule_all (REWRITE_RULE [ETA_AX] augassign_joint_operand_ready) >>
  strip_tac >>
  drule_all augassign_source_prefix_replay >>
  disch_then (mk_asm "sourceReplay") >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e st cb cc u ee rhs rhsop q /\
       ghost_inv_at (DF H) lo d cenv cx ee Gq tnq q /\
       ghost_kept_at lo cenv st cb Gload tnload u Gq tnq /\
       u.vs_alloca_next <= q.vs_alloca_next` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> rhsQ K _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (rhsQ = _)` (fn th =>
       CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
     BETA_TAC >>
     disch_then (CONJUNCTS_THEN2
       (qx_choose_then `rhs'` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) >>
     `rhs' = rhs` by fs[] >>
     qpat_x_assum `rhs' = rhs` SUBST_ALL_TAC >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee q /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gq tnq q` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> expr_post K ctx func cenv cx e st cb cc u ee rhs rhsop q /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2
       (STRIP_ASSUME_TAC o REWRITE_RULE [expr_post_def]) STRIP_ASSUME_TAC) >>
     simp[]) >>
  qpat_assum `expr_post _ ctx func cenv cx e st cb cc u ee rhs rhsop q`
    (STRIP_ASSUME_TAC o REWRITE_RULE [expr_post_def]) >>
  `type_bits aty MOD 8 = 0` by
    (drule (cj 3 aug_place_typing) >>
     metis_tac[assignable_type_well_formed,stmtSimAugAssignTheory.well_formed_type_bits]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `post_value_type cenv e = expr_type e` SUBST_ALL_TAC >>
  `eval_operand rhsop q = SOME (typed_val_to_w256 tvR rhs)` by
    (irule exprBopSimPropsTheory.expr_val_rel_typed >>
     qexistsl_tac [`cx`,`expr_type e`] >> simp[]) >>
  `op_prov Gq rhsop = NONE /\ op_taint tnq rhsop = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `!l. old <> Label l /\ rhsop <> Label l` by
    (qpat_assum `compile_imm_load_word T cenv.ce_imm_alloca _ _ = _`
       (mp_tac o MATCH_MP fragFuelExprHelpersTheory.compile_ptr_load_not_label o
        ONCE_REWRITE_RULE [GSYM (cj 5 compile_ptr_load_def)]) >> simp[]) >>
  `cb.cs_next_var <= cc.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv cc` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. old = Var x ==> not_fresh_at cc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. FST r = Var x ==> not_fresh_at cc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv cc q` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`u`,`cb`] >> fs[expr_post_def]) >>
  `(bop = Exp ==>
     (IS_SOME (NONE:int option) \/
        ?n. (if bop = Exp then expr_int_literal e else NONE) = SOME n /\ 0 <= n) /\
     (!n. (NONE:int option) = SOME n ==> cur = IntV n) /\
     (!n. (if bop = Exp then expr_int_literal e else NONE) = SOME n ==> rhs = IntV n))` by
    (disch_tac >> qpat_assum `bop = Exp ==> _` drule >> simp[]) >>
  reverse (Cases_on `evaluate_binop
    (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
    ptv bop cur rhs`)
  >- suspend "nested_operator_error" >>
  suspend "nested_operator_success"
QED

Resume body_augassign_nested_immutable_full[nested_operator_error]:
  drule_all augassign_operator_source_runtime_error >>
  disch_then (qspec_then `ee` (qx_choose_then `msg` STRIP_ASSUME_TAC)) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    augassign_operator_joint_error) >>
  disch_then (qspec_then `shadow_ctx` (mp_tac o
    SRULE [bodyPtrDefsTheory.stmt_exit_ptr_def])) >>
  disch_then (qspecl_then [`ee`,`PG`]
    (qx_choosel_then [`abortState`,`Gabort`,`tnabort`] (mk_asm "opAbort"))) >>
  irule (Q.INST [`ee` |-> `ee`,`res` |-> `INR (Error (RuntimeError msg))`,
                 `r` |-> `Abort Revert_abort abortState`,
                 `G'` |-> `Gabort`,`tn'` |-> `tnabort`]
    gasOutcomeFullComposeTheory.gas_outcome_full_exit) >>
  simp[bind_def,lift_sum_def,raise_def,fragExecTheory.exit_result_def,Abbr `stmtR`] >>
  qexistsl_tac [`Gabort`,`abortState`,`ee`,`msg`,`tnabort`] >>
  simp[bodyPtrDefsTheory.stmt_exit_ptr_def] >>
  qx_gen_tac `H` >> disch_tac >>
  asm "opAbort" (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> simp[haltExitProjTheory.halt_exit_not_halt]
QED

Resume body_augassign_nested_immutable_full[nested_operator_success]:
  rename1 `evaluate_binop _ ptv bop cur rhs = INL value` >>
  `bop_result cx aty bop [aty;expr_type e] cur rhs ee = INL value` by
    (drule_all augassign_operator_source_representation >> simp[]) >>
  `value_has_type ptv value` by (drule_all augassign_operator_source_value_type >> simp[]) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    augassign_operator_joint_success) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`w`,`Gw`,`tnw`] (mk_asm "opSuccess"))) >>
  `!gs. eval_stmt cx (AugAssign aty t bop e)
       (es with gas_obs := (reads ++ rhsReads) ++ gs) =
       write_place cx p value (ee with gas_obs := gs)` by
    (asm "sourceReplay" (qspecl_then [`aty`,`bop`] (fn th =>
       simp[APPEND_ASSOC,th,bind_def,lift_sum_def,return_def]))) >>
  `gas_admissible (write_place cx p value) (stmt_res_ok lctx) ee` by
    (qpat_assum `!gs. eval_stmt cx _ _ = write_place cx _ _ _` mp_tac >>
     qpat_assum `gas_admissible (eval_stmt cx _) _ es` mp_tac >>
     qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_replay_admissible]) >>
  simp[lift_sum_def,vyperStateTheory.bind_return] >>
  irule (Q.INST [`s1` |-> `w`,`G1` |-> `Gw`,`tn1` |-> `tnw`]
    gas_outcome_full_zero_prefix_guarded) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
  Cases_on `write_place cx p value ee` >>
  rename1 `write_place cx p value ee = (wr,ff)` >>
  suspend "nested_store"
QED


Resume body_augassign_nested_immutable_full[nested_store]:
  `stmt_res_ok lctx wr` by
    (qpat_assum `gas_admissible (write_place cx p value) _ ee`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  drule bodyInvCodePropsTheory.body_inv_main_code >> strip_tac >>
  drule_then assume_tac body_inv_contract >>
  `cenv.ce_modules = [(NONE,tops)]` by metis_tac[contract_inv_cenv_modules] >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx env st /\
   expr_sim_inv_mods [(NONE,tops)] cenv cx env ee` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_split_def] >>
  `!H. dead_lo_ok_mods H (DF H) lo cenv cx` by
    fs[GSYM bodyFullShadowBodyInvTheory.dead_lo_ok_mods_singleton] >>
  qpat_assum `!H. dead_lo_ok_mods H (DF H) lo cenv cx`
    (qspec_then `H0` assume_tac) >>
  drule_all (Q.INST [`es` |-> `st`,`rt` |-> `itv`,`v` |-> `iv`,`H` |-> `H0`]
    immutable_region_value_layout_mods) >> strip_tac >>
  drule_all immutable_region_mods_type >>
  disch_then (qx_choosel_then [`regionTops`,`regionTy`,`regionTv`] STRIP_ASSUME_TAC) >>
  `regionTy = root_ty /\ regionTv = itv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `regionTy = root_ty` SUBST_ALL_TAC >>
  qpat_x_assum `regionTv = itv` SUBST_ALL_TAC >>
  `regionTops = tops` by
    (qpat_x_assum `ALOOKUP [(NONE,tops)] NONE = SOME regionTops` mp_tac >>
     simp[NoAsms]) >>
  qpat_x_assum `regionTops = tops` SUBST_ALL_TAC >>
  `~MEM (WriteAcc (StateRef (NONE,id))) (expr_accesses cenv.ce_modules e)` by
    suspend "nested_rhs_access" >>
  `?currentImms. ALOOKUP ee.immutables cx.txn.target = SOME currentImms /\
       FLOOKUP (get_source_immutables NONE currentImms) id = SOME (itv,iv)` by
    suspend "nested_rhs_immutable" >>
  `write_place cx (ImmutablePlace NONE id path) value ee = (wr,ff)` by
    fs[Abbr `p`] >>
  drule_all immutable_augassign_path_write_source >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC (qx_choose_then `new` STRIP_ASSUME_TAC)) >>
  `ff.scopes = ee.scopes /\ ff.storage_trace = ee.storage_trace /\ ff.gas_obs = []` by
    (qpat_assum `write_place cx (ImmutablePlace NONE id path) value ee = (INL (),ff)`
       (strip_assume_tac o MATCH_MP vyperPlaceFramesTheory.write_immutable_place_frame) >>
     simp[]) >>
  `ff with gas_obs := [] = ff` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  `store_lays_out ptv ptv value` by metis_tac[store_lays_out_typed] >>
  `value_has_type itv iv` by
    (`state_well_typed ee` by
       (qpat_assum `expr_sim_inv cenv cx env ee`
          (MAP_FIRST ACCEPT_TAC o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def])) >>
     `imms_well_typed currentImms` by
       (irule vyperTypeEnvTheory.state_well_typed_immutables_ALOOKUP >>
        qexistsl_tac [`cx.txn.target`,`ee`] >> simp[]) >>
     qpat_assum `FLOOKUP (get_source_immutables NONE currentImms) id = SOME (itv,iv)`
       (ACCEPT_TAC o cj 1 o MATCH_MP vyperTypeEnvTheory.imms_well_typed_get_source_immutables o
        CONJ (ASSUME ``imms_well_typed currentImms``))) >>
  `value_has_type itv new` by
    (drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
     irule placeMemoryPathRebuildTheory.assign_subscripts_type_path_preserves_type >> simp[] >>
     qexistsl_tac [`iv`,`path`,`ptv`,`value`] >> simp[]) >>
  qabbrev_tac `Hstore = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 Hstore ee.storage_trace` by simp[Abbr `Hstore`] >>
  asm "opSuccess" (qspec_then `Hstore` (drule_then strip_assume_tac)) >>
  suspend "nested_store_exec"
QED

Resume body_augassign_nested_immutable_full[nested_rhs_access]:
  `~constant_decl id tops` by
    (fs[cx_const_name_def] >> metis_tac[constant_decl_mem_consts]) >>
  `MEM (StateRef (NONE,id)) (nonconstant_reads cenv.ce_modules
    (expr_accesses cenv.ce_modules (target_to_expr t)))` by
    (irule target_root_state_nonconstant_read >> simp[]) >>
  `t <> TopLevelNameTarget (NONE,id)` by simp[] >>
  `~is_word_type root_ty` by
    (drule_all typed_nested_immutable_root_nonword >> simp[]) >>
  `~var_is_prim_word cenv (StateRef (NONE,id))` by
    (simp[var_is_prim_word_def,target_place_type_def] >>
     Cases_on `cenv.ce_hashmap_info (NONE,id)` >> simp[] >>
     rename1 `cenv.ce_hashmap_info (NONE,id) = SOME entry` >>
     PairCases_on `entry` >> simp[]) >>
  `~aug_assign_overlap cenv t e` by
    (qpat_assum `stmt_exprs_ok cenv (AugAssign aty t bop e)` mp_tac >>
     simp[NoAsms,stmt_exprs_ok_def,alloc_limits_stmt_def] >> strip_tac >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `~aug_assign_overlap cenv t e` mp_tac >>
  simp_tac std_ss [aug_assign_overlap_def,LET_THM,EXISTS_MEM,NOT_EXISTS_THM] >>
  disch_then (qspec_then `StateRef (NONE,id)` mp_tac) >> simp[]
QED

Resume body_augassign_nested_immutable_full[nested_rhs_immutable]:
  qpat_assum `bind (eval_expr cx e) (read_result cx) (st with gas_obs := rhsReads) = _`
    (qx_choosel_then [`tv`,`readState`] strip_assume_tac o
     MATCH_MP (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL)) >>
  qpat_assum `read_result cx tv readState = (INL rhs,ee)`
    (assume_tac o MATCH_MP vyperStateTheory.read_result_state) >>
  `FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
      NONE => FEMPTY | SOME observedImms => get_source_immutables NONE observedImms)
      id = SOME (itv,iv)` by
    (mp_tac (BETA_RULE (Q.SPECL [`cx`,`e`,`st with gas_obs := rhsReads`,
       `INL tv`,`readState`,`[(NONE,tops)]`,`NONE`,`id`]
       eval_expr_immutable_access_frame)) >>
     impl_tac
     >- (simp[] >> conj_tac
         >- (rpt gen_tac >> strip_tac >>
             mp_tac (Q.SPECL [`[(NONE,tops)]`,`[]`,`ctx`,`cenv`,`cx`,
               `src`,`ts`,`fn`,`mut`,`nr`,`args`,`dflts`,`ret`,`body`]
               immutable_index_callable_closed_mods) >> simp[]) >>
         qpat_assum `cenv.ce_modules = [(NONE,tops)]` (SUBST1_TAC o SYM) >>
         first_assum ACCEPT_TAC) >>
     simp[]) >>
  pop_assum mp_tac >> Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  simp[NoAsms,finite_mapTheory.FLOOKUP_EMPTY]
QED

Resume body_augassign_nested_immutable_full[nested_store_exec]:
  `compile_imm_store_word cenv.ce_imm_alloca (FST r) dst cd = ((),sb)` by
    fs[compile_ptr_store_def] >>
  `w2n (n2w (off+k):bytes32) + 32 <= lo` by simp[] >>
  `!x. FST r = Var x ==> not_fresh_at cd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,exprLoweringPropsTheory.ci_mono_def] >>
  `!x. dst = Var x ==> not_fresh_at cd x` by
    (qpat_assum `compile_binop _ _ _ _ _ _ cc = (dst,cd)`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [safe_operand_def] o
        MATCH_MP compile_binop_safe_operand)) >>
  `op_prov Gw (FST r) = NONE` by
    suspend "nested_store_provenance" >>
  `op_taint tnw (FST r) = {}` by fs[target_ptr_ok_def] >>
  qpat_assum `ghost_inv_at (DF Hstore) lo d cenv cx ee Gw tnw w`
    (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region w = SOME 0w /\
     op_taint tnw region = {} /\ op_prov Gw region = NONE` by
    suspend "nested_store_base" >>
  drule_all immutable_word_store_path_clean >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`Gf`,`tf`,`rawStore`] strip_assume_tac)))))) >>
  qabbrev_tac `endState = rawStore with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl_tac [`Gw`,`tnw`,`w`] >>
  conj_tac >- (asm "opSuccess" (ACCEPT_TAC o cj 1)) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`ff`,`INL ()`,`endState`,`tf`] >>
  conj_tac
  >- (simp[Abbr `p`] >>
      qpat_assum `write_place cx (ImmutablePlace NONE id path) value ee = (INL (),ff)`
        (ACCEPT_TAC o MATCH_MP bodyImmutableAugAssignExecTheory.immutable_write_place_gas_obs)) >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[Abbr `endState`] >>
  qpat_assum `ff with gas_obs := [] = ff` (fn th => simp_tac bool_ss [th]) >>
  suspend "nested_store_post"
QED

Resume body_augassign_nested_immutable_full[nested_store_provenance]:
  Cases_on `FST r` >> simp[ptrDisciplineTheory.op_prov_def] >>
  rename1 `FST r = Var x` >>
  `not_fresh_at cb x /\ not_fresh_at cc x` by simp[] >>
  qpat_assum `ghost_kept_at lo cenv ee cc Gq tnq q Gw tnw`
    (drule_then (SUBST1_TAC o cj 1) o Q.SPEC `x` o cj 1 o
     REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
  qpat_assum `ghost_kept_at lo cenv st cb Gload tnload u Gq tnq`
    (drule_then (SUBST1_TAC o cj 1) o Q.SPEC `x` o cj 1 o
     REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
  qpat_assum `op_prov Gload (Var x) = NONE` mp_tac >>
  simp[NoAsms,ptrDisciplineTheory.op_prov_def]
QED

Resume body_augassign_nested_immutable_full[nested_store_base]:
  `lo <> 0` by decide_tac >>
  `immutable_base_zero cenv w` by metis_tac[stmt_state_rel_immutable_base_zero] >>
  qpat_assum `immutable_base_zero cenv w`
    (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.immutable_base_zero_def]) >>
  qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> _`
    (assume_tac o REWRITE_RULE [ptrDisciplineTheory.op_taint_def]) >>
  Cases >> simp[ptrDisciplineTheory.op_taint_def,ptrDisciplineTheory.op_prov_def] >>
  metis_tac[]
QED


Resume body_augassign_nested_immutable_full[nested_store_post]:
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_assum `ff.storage_trace = ee.storage_trace` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  asm "opSuccess" (qspec_then `H` (drule_then strip_assume_tac)) >>
  `rawStore.vs_current_bb = w.vs_current_bb /\ rawStore.vs_halted = w.vs_halted /\
   rawStore.vs_allocas = w.vs_allocas /\ rawStore.vs_alloca_next = w.vs_alloca_next` by
    (qpat_assum `rawStore with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = w`
       mp_tac >> simp[venomStateTheory.venom_state_component_equality]) >>
  `(endState with <|vs_vars := w.vs_vars; vs_memory := w.vs_memory;
     vs_immutables := w.vs_immutables; vs_prev_bb := w.vs_prev_bb;
     vs_current_bb := w.vs_current_bb; vs_inst_idx := w.vs_inst_idx|>) = w` by
    (qpat_assum `rawStore with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = w`
       mp_tac >>
     simp[Abbr `endState`,venomStateTheory.venom_state_component_equality]) >>
  `endState.vs_memory = (mstore (off+k) (typed_val_to_w256 ptv value) w).vs_memory`
    by simp[Abbr `endState`] >>
  `endState.vs_alloca_next = w.vs_alloca_next /\ endState.vs_allocas = w.vs_allocas /\
    endState.vs_current_bb = w.vs_current_bb /\ endState.vs_halted = w.vs_halted` by
    simp[Abbr `endState`] >>
  `!x. not_fresh_at cd x ==>
     lookup_var x endState = lookup_var x w /\ FLOOKUP Gf x = FLOOKUP Gw x /\
     op_taint tf (Var x) = op_taint tnw (Var x)` by
    (qpat_assum `!x. not_fresh_at cd x ==> lookup_var x rawStore = lookup_var x w`
       (mp_tac o REWRITE_RULE [venomStateTheory.lookup_var_def]) >>
     simp[Abbr `endState`,venomStateTheory.lookup_var_def]) >>
  `type_memory_size ptv = 32` by
    (mp_tac (Q.SPECL [`get_tenv cx`,`aty`,`ptv`] exprSimPropsTheory.word_tv_memory_size) >>
     simp[]) >>
  `k + 32 <= type_memory_size itv` by
    (qpat_assum `mem_path_offset itv path = SOME (k,ptv)`
       (mp_tac o cj 2 o MATCH_MP exprSimPropsTheory.mem_path_offset_sound) >> simp[]) >>
  `!mem. mem_agree_outside tnw.t_mem w.vs_memory mem ==>
     val_in_memory itv iv off mem` by suspend "nested_store_robust" >>
  `tf.t_mem SUBSET tnw.t_mem` by simp[pred_setTheory.SUBSET_DEF,pred_setTheory.IN_DIFF] >>
  `!i. i < lo /\ i IN tf.t_mem ==>
    imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo endState.vs_memory) i` by
    suspend "nested_store_dead" >>
  `local_ptrs_reserved cenv cd /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cd x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cd x)` by
    (`cc.cs_next_var <= cd.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,freshWritesTheory.not_fresh_at_mono]) >>
  `dead_lo_ok H (DF H) lo cenv cx` by
    (qpat_assum `!K. dead_lo_ok K (DF K) lo cenv cx` (qspec_then `H` ACCEPT_TAC)) >>
  `ghost_inv_at (DF H) lo d cenv cx ff Gf tf endState` by
    (irule (INST_TYPE [alpha |-> ``:256``] immutable_ctor_word_store_ghost) >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w` (irule_at Any) >>
     qexistsl_tac [`typed_val_to_w256 ptv value`,`tops`,`cd`,`off+k`,
       `func`,`env`,`ctx`,`H`] >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx ff endState` by suspend "nested_store_rel" >>
  `alloca_frame cenv es sa s0 cenv ff endState /\
   s0.vs_alloca_next <= endState.vs_alloca_next /\
   (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
     lookup_var x endState = SOME z) /\
   (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP endState.vs_allocas aid = SOME b) /\
   (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
      op_taint tf (Var x) = op_taint tn0 (Var x)) /\
   (!aid b sz i. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
     (!n c len. local_region cenv es.scopes s0 n c len ==>
                 b+sz <= c \/ c+len <= b) /\
     b <= i /\ i < b+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)` by
     suspend "nested_store_frames" >>
  `return_buf_frame d cenv sb endState` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`w`,`cd`] >>
     `cd.cs_next_var <= sb.cs_next_var` by
       qpat_assum `ci_mono cd sb`
         (ACCEPT_TAC o cj 2 o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]) >>
     simp[]) >>
  `alloca_history func endState` by suspend "nested_store_history" >>
  `endState.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[Abbr `endState`] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp endState` by
    simp[Abbr `endState`,exprPtrUnwrapFramesTheory.copy_allocas_inst_idx] >>
  `storage_well_formed_on cx ff (FST H)` by
    (qpat_assum `write_place cx (ImmutablePlace NONE id path) value ee = (INL (),ff)`
       (qx_choose_then `newImms` SUBST1_TAC o
        MATCH_MP vyperPlaceFramesTheory.write_immutable_place_frame) >>
     qpat_assum `storage_well_formed_on cx ee (FST H)` mp_tac >>
     simp[NoAsms,storage_well_formed_on_def,FORALL_BOOL,
          vyperStorageBackendTheory.get_storage_def]) >>
  simp[Abbr `stmtQ`,stmt_lands_def,cenv_top_ext_refl,IgnAsm `tf.t_mem = _`] >>
  rpt strip_tac >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==>
       i IN tn0.t_mem` (drule_all_then ACCEPT_TAC)
QED

Resume body_augassign_nested_immutable_full[nested_store_robust]:
  `cenv.ce_modules = [(NONE,cx_tops cx)]` by simp[] >>
  `ghost_inv_at_mods (DF H) lo d cenv cx ee Gw tnw w` by
    (qpat_assum `cenv.ce_modules = [(NONE,cx_tops cx)]`
       (fn th => PURE_REWRITE_TAC
         [MATCH_MP bodyFullShadowBodyInvTheory.ghost_inv_at_mods_singleton th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!K. dead_lo_ok_mods K (DF K) lo cenv cx`
    (qspec_then `H` assume_tac) >>
  mp_tac (Q.INST [`entry` |-> `ee`,`es` |-> `ee`,`H` |-> `H`,`D` |-> `DF H`,
        `mods` |-> `[(NONE,tops)]`,`exps` |-> `[]`,`rt` |-> `itv`,`v` |-> `iv`,
        `s` |-> `w`,`tn` |-> `tnw`,`G` |-> `Gw`,`imms` |-> `currentImms`]
       (INST_TYPE [alpha |-> ``:256``] immutable_ctor_frame_mods)) >>
  (impl_tac >- simp[]) >>
  disch_then (ACCEPT_TAC o cj 2)
QED

Resume body_augassign_nested_immutable_full[nested_store_dead]:
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w`
    (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
  mp_tac (Q.INST [`itv` |-> `itv`,`old` |-> `iv`,`path` |-> `path`,`k` |-> `k`,
    `ptv` |-> `ptv`,`v` |-> `value`,`new` |-> `new`,
    `dirty` |-> `tnw.t_mem`,`s` |-> `w`,`off` |-> `off`]
    augassign_immutable_path_robust_write) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  `cenv.ce_modules = [(NONE,cx_tops cx)]` by simp[] >>
  qpat_assum `cenv.ce_modules = [(NONE,cx_tops cx)]`
    (fn th =>
      let val dead = GSYM (MATCH_MP bodyInvSplitTheory.imm_section_dead_mods_singleton th) in
        qpat_assum `!i. i < lo /\ i IN tnw.t_mem ==> _`
          (assume_tac o REWRITE_RULE [dead]) >>
        PURE_REWRITE_TAC [dead]
      end) >>
  qpat_assum `endState.vs_memory = _` SUBST1_TAC >>
  qpat_assum `tf.t_mem = _` SUBST1_TAC >>
  qpat_assum `w2n (n2w (off+k):bytes32) = off+k`
    (fn th => PURE_REWRITE_TAC [th]) >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`,`exps` |-> `[]`,
    `ctx` |-> `ctx`,`cx` |-> `cx`,`env` |-> `env`,`es` |-> `ee`,
    `src` |-> `NONE`,`id` |-> `id`,`off` |-> `off`,`ty` |-> `root_ty`,`itv` |-> `itv`,
    `path` |-> `path`,`k` |-> `k`,`ptv` |-> `ptv`,`new` |-> `new`,
    `dirty` |-> `tnw.t_mem`,`lo` |-> `lo`,`cenv` |-> `cenv`]
    (INST [``w:bytes32`` |-> ``typed_val_to_w256 ptv value``,
           ``s:venom_state`` |-> ``w:venom_state``]
      augassign_immutable_path_dead_mask)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Resume body_augassign_nested_immutable_full[nested_store_rel]:
  `val_in_memory ptv value (off+k) endState.vs_memory` by
    (qpat_assum `endState.vs_memory = _` SUBST1_TAC >>
     drule assignTuplePtrStoreWordTheory.store_lays_out_robust_ptr >>
     disch_then irule >> qexistsl_tac [`{}`,`w`] >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `LENGTH w.vs_memory <= LENGTH endState.vs_memory` by
    simp[venomMemPropsTheory.LENGTH_mstore_eq] >>
  `!a n. regions_disjoint a n (off+k) (type_memory_size ptv) ==>
    mem_bytes_at a n endState.vs_memory = mem_bytes_at a n w.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `endState.vs_memory = _` SUBST1_TAC >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     qpat_assum `regions_disjoint a n (off+k) (type_memory_size ptv)` mp_tac >>
     simp_tac bool_ss [loweringStateRelDefsTheory.regions_disjoint_def,
       ASSUME ``type_memory_size ptv = 32``] >> decide_tac) >>
  MATCH_MP_TAC (Q.INST [`env` |-> `env`,`es` |-> `ee`,`id` |-> `id`,
    `itv` |-> `itv`,`k` |-> `k`,`off` |-> `off`,`path` |-> `path`,
    `ptv` |-> `ptv`,`s` |-> `w`,`sa` |-> `cd`,`src` |-> `NONE`,
    `ty` |-> `root_ty`,`v` |-> `value`] immutable_path_store_stmt_state_rel) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Resume body_augassign_nested_immutable_full[nested_store_history]:
  `?bb rest. lookup_block w.vs_current_bb func.fn_blocks = SOME bb /\
     DROP w.vs_inst_idx bb.bb_instructions = emitted_insts cd sb ++ rest` by
    (qpat_assum `fn_has_code cd sb func`
       (qx_choose_then `bb` strip_assume_tac o cj 2 o REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
     qpat_assum `isPREFIX sb.cs_current_insts bb.bb_instructions`
       (qx_choose_then `rest` assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
     `w.vs_current_bb = sb.cs_current_bb` by simp[] >>
     qexistsl_tac [`bb`,`rest`] >>
     conj_tac
     >- (qpat_assum `w.vs_current_bb = sb.cs_current_bb` SUBST1_TAC >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `bb.bb_instructions = sb.cs_current_insts ++ rest` SUBST1_TAC >>
     qpat_assum `sb.cs_current_insts = cd.cs_current_insts ++ emitted_insts cd sb` SUBST1_TAC >>
     qpat_assum `w.vs_inst_idx = LENGTH cd.cs_current_insts` SUBST1_TAC >>
     ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] >>
     simp_tac std_ss [DROP_APPEND2,arithmeticTheory.LESS_EQ_REFL,
                      arithmeticTheory.SUB_EQUAL_0,listTheory.DROP_0]) >>
  mp_tac (Q.SPECL [`func`,`w`,`rawStore`,`bb`,`emitted_insts cd sb`,`rest`]
    bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `endState`]
QED

Resume body_augassign_nested_immutable_full[nested_store_frames]:
  `valid_horizon cx st0 H st.storage_trace` by
    (mp_tac (Q.INST [`st` |-> `st with gas_obs := rhsReads`,
       `f` |-> `bind (eval_expr cx e) (read_result cx)`,`res` |-> `INL rhs`,
       `st'` |-> `ee`,`H` |-> `H`,`st0` |-> `st0`,`cx` |-> `cx`]
       (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame)) >>
     simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (mp_tac (Q.INST [`st` |-> `es with gas_obs := reads`,
       `f` |-> `eval_target_place cx t`,`res` |-> `INL p`,
       `st'` |-> `st`,`H` |-> `H`,`st0` |-> `st0`,`cx` |-> `cx`]
       (INST_TYPE [alpha |-> ``:place``] valid_horizon_frame)) >>
     simp[cj 8 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!K. valid_horizon cx st0 K es.storage_trace ==> _`
       (qspec_then `H` (drule_then (ACCEPT_TAC o cj 1)))) >>
  `imm_target_post H ctx func cenv cx es sa ca s0 st id path aty r v` by
    (qpat_assum `Abbrev (targetQ = _)` (fn abbreviation =>
       qpat_assum `!K. valid_horizon _ _ K st.storage_trace ==> targetQ K _ _ _ _ _ /\ _`
         (qspec_then `H` (drule_then
           (strip_assume_tac o BETA_RULE o
            REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] abbreviation])))) >>
     `path' = path` by
       (qpat_assum `INL p = INL (ImmutablePlace NONE id path')` mp_tac >>
        simp[Abbr `p`]) >>
     qpat_x_assum `path' = path` SUBST_ALL_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `imm_target_post H _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [imm_target_post_def]) >>
  `MAP FDOM st.scopes = MAP FDOM es.scopes` by
    (qpat_assum `eval_target_place cx t (es with gas_obs := reads) = _`
       (mp_tac o SYM o MATCH_MP vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom) >>
     simp[NoAsms]) >>
  `alloca_frame cenv es sa s0 cenv st v` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `u.vs_memory = v.vs_memory /\ u.vs_allocas = v.vs_allocas` by
    (conj_tac
     >- (qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``venom_state_vs_memory``) >>
         simp[NoAsms,stateFrameTheory.state_frame_def]) >>
     qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``venom_state_vs_allocas``) >>
     simp[NoAsms,stateFrameTheory.state_frame_def]) >>
  `alloca_frame cenv st ca v cenv st u` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx st v` (irule_at Any) >>
     simp[]) >>
  `sa.cs_next_var <= ca.cs_next_var /\ ca.cs_next_var <= cb.cs_next_var /\
   cb.cs_next_var <= cc.cs_next_var /\ cc.cs_next_var <= cd.cs_next_var /\
   sa.cs_next_id <= ca.cs_next_id /\ ca.cs_next_id <= cb.cs_next_id /\
   cb.cs_next_id <= cc.cs_next_id` by
    (MAP_EVERY (fn term => qpat_assum term
       (strip_assume_tac o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]))
       [`ci_mono sa ca`, `ci_mono ca cb`, `ci_mono cb cc`, `ci_mono cc cd`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv st u` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`st`,`v`,`ca`] >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM st.scopes` by
    (drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx st u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload` by
    (asm "loadPost" (qspec_then `H` mp_tac) >> simp[]) >>
  `(!x y. not_fresh_at sa x /\ lookup_var x s0 = SOME y ==>
      lookup_var x u = SOME y) /\
   (!aid block. FLOOKUP s0.vs_allocas aid = SOME block ==>
      FLOOKUP u.vs_allocas aid = SOME block) /\
   s0.vs_alloca_next <= u.vs_alloca_next` by
    (simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==>
       expr_post K ctx func cenv cx e st cb cc u ee rhs rhsop q /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `sa.cs_next_id <= cb.cs_next_id /\ sa.cs_next_var <= cb.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`sa0` |-> `sa`,`sc` |-> `cb`,`sd` |-> `cc`,`se` |-> `cd`,
    `es0` |-> `es`,`s0` |-> `s0`,`Gu` |-> `Gload`,`tnu` |-> `tnload`,
    `u` |-> `u`,`q` |-> `q`,`w` |-> `w`,`G0` |-> `G0`,`tn0` |-> `tn0`,
    `H` |-> `H`,`ctx` |-> `ctx`,`func` |-> `func`,`cx` |-> `cx`,`cenv` |-> `cenv`,
    `st` |-> `st`,`ee` |-> `ee`,`e` |-> `e`,`v` |-> `rhs`,`op` |-> `rhsop`,
    `Gq` |-> `Gq`,`tnq` |-> `tnq`,`Gw` |-> `Gw`,`tnw` |-> `tnw`,
    `lo` |-> `lo`,`d` |-> `d`]
    (INST_TYPE [alpha |-> ``:num # num``] augassign_prefix_operator_frame)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >> strip_tac >>
  `alloca_frame cenv ee cd w cenv ff endState` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx ee w` (irule_at Any) >>
     simp[IgnAsm `w.vs_memory = q.vs_memory`,IgnAsm `w.vs_allocas = q.vs_allocas`] >>
     rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     rename1 `FLOOKUP w.vs_allocas aid = SOME (savedOff,savedSize)` >>
     `lo <= savedOff` by
       (qpat_assum `allocas_from lo w`
          (drule_then ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
     decide_tac) >>
  conj_tac
  >- (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`ee`,`w`,`cd`] >>
      `ci_mono sa cd` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
      qpat_assum `ci_mono sa cd`
        (assume_tac o cj 3 o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==> not_fresh_at cd x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> _`
        (drule_all_then assume_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cd x` (drule_then assume_tac) >>
      qpat_assum `!x. not_fresh_at cd x ==> lookup_var x endState = _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gw x = _ /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at cd x` (drule_then assume_tac) >>
      qpat_assum `!x. not_fresh_at cd x ==> lookup_var x endState = _ /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `tf.t_mem SUBSET tnw.t_mem`
    (drule_then assume_tac o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Finalise body_augassign_nested_immutable_full

(* Every other base target. *)
Theorem body_augassign_other_full:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `immutable_root cx t /\ ~(?nsid. t = TopLevelNameTarget nsid)`
  >- (drule_all bodySimTheory.body_inv_stmt_const_name_free >> strip_tac >>
      irule body_augassign_nested_immutable_full >> metis_tac[]) >>
  `target_mutable env t` by
    (qpat_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[NoAsms, Once type_stmt_def, AllCaseEqs()]) >>
  `immutable_root cx t ==> ?nsid. t = TopLevelNameTarget nsid` by
    metis_tac[] >>
  drule_all augassign_other_target_routes >>
  disch_then (DISJ_CASES_THEN STRIP_ASSUME_TAC)
  >- suspend "ordinary" >>
  suspend "immutable"
QED

(* Shared composition for the ordinary target-place route. *)
Theorem augassign_ordinary_full[local]:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    (?pt. supported_target_info tops bindings t = SOME pt) /\
    ~immutable_root cx t ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `target_pre cenv cx env t es` by
    (drule_all augassign_entry_target_pre >> simp[]) >>
  `target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t es` by
    (irule body_target_place_sim_full >> simp[] >> qexists_tac `tops` >> simp[]) >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule augassign_sep_outcome >>
  qexistsl_tac [`cenv`,`d`,`sa`] >> simp[] >>
  drule (cj 1 aug_place_typing) >> strip_tac >>
  drule_all (cj 1 aug_place_typing_word) >> strip_tac >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    ((simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >> Cases_on `res` >>
     simp[target_place_res_ok_def] >>
     `no_control_exc y` by metis_tac[vyperExprNoControlTheory.eval_target_place_no_control] >>
     qpat_assum `gas_admissible _ _ _` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     simp[augassign_source_bind, bind_def, stmt_res_ok_def, no_control_exc_def] >> (gvs[gas_admissible_def, target_place_res_ok_def, vyperExprNoControlTheory.eval_target_place_no_control, augassign_source_bind, bind_def, stmt_res_ok_def, no_control_exc_def]))) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choose_then `r` (qx_choose_then `ca` (qx_choose_then `shadow_ca`
      (fn th =>
        case rev (CONJUNCTS th) of
          cases::slices => map_every assume_tac (rev slices) >> assume_tac cases
        | [] => NO_TAC))))) >>
  qpat_x_assum `target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`aty`,`sa`,`ca`,`shadow_sa`,`shadow_ca`,
                           `r`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx t) _ targetQ targetR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
     (\H res ee G tn v. targetQ H res ee G tn v /\
       (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z))
     targetR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` kall_tac >>
  qmatch_goalsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ _ stmtQ stmtR` >>
  rewrite_tac[augassign_source_bind] >>
  irule augassign_target_bind_full >>
  qexists_tac `\H res ee G tn u. targetQ H res ee G tn u /\
    ~u.vs_halted /\ ee.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z)` >>
  reverse conj_tac
  >- ((irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ targetR` (irule_at Any) >>
      conj_tac >- (simp[] >> rpt strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
      simp[Abbr `targetR`, Abbr `stmtR`] >>
      rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[] >> drule_all augassign_expr_exit_to_stmt_exit >>
      disch_then (qspecl_then [`gt`,`RetQ`] strip_assume_tac) >> simp[] >> (gvs[]))) >>
  qx_genl_tac [`marks`,`res`,`st`,`Gtarget`,`tnt`,`v`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon st.storage_trace) st.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `!H. valid_horizon _ _ H st.storage_trace ==> targetQ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon st.storage_trace` (drule_then strip_assume_tac)) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H st.storage_trace ==> _`
    (qspec_then `storage_trace_horizon st.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (targetQ = _)` (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) >>
  disj1_tac >> qexists_tac `p` >> simp[] >>
  qpat_x_assum `_ \/ ?loc cur rhs result s1 s2 s3 ss1 ss2 ss3. _`
    (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (qx_choosel_then [`loc`,`old`,`rhsop`,`dst`,`cb`,`cc`,`cd`,
                         `shadow_cb`,`shadow_cc`,`shadow_cd`] STRIP_ASSUME_TAC))
  >- (Cases_on `p` >> fs[target_post_def, place_ptr_rel_def]) >>
  `sa.cs_next_var <= ca.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv ca` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv ca v` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[target_post_def]) >>
  `eval_target_place cx t (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p,st)` by
    (`st with gas_obs := [] = st` by simp[vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum (fn upd =>
       qpat_assum `!tail. eval_target_place _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,upd])))) >>
  qmatch_asmsub_abbrev_tac `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)` >>
  `body_const_cells_agree [(NONE,tops)] cx env st` by
    (irule body_const_cells_agree_target >>
     qpat_assum `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)`
       (irule_at Any) >> simp[]) >>
  `!id path. p = MemoryPlace id path ==>
    ?entry v. lookup_scopes id st.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v` by
    fs[Abbr `targetQ`] >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
     target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
     target_ptr_ok cenv (PlaceR p) r Gtarget tnt v /\
     ghost_inv_at (DF H) lo d cenv cx st Gtarget tnt v /\
     ghost_kept_at lo cenv (es with gas_obs := reads) sa G0 tn0 s0 Gtarget tnt /\
     dead_lo_ok H (DF H) lo cenv cx /\
     return_buf_frame d cenv ca v /\ alloca_history func v /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
     ~v.vs_halted /\ v.vs_current_bb = ca.cs_current_bb /\
     v.vs_inst_idx = LENGTH ca.cs_current_insts` by
    (((qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon cx st0 K st.storage_trace ==>
                     targetQ K (INL p) st Gtarget tnt v /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[Abbr `targetQ`] >> strip_tac >>
     simp[] >> fs[bodyPtrDefsTheory.ghost_kept_at_def] >>> NTH_GOAL (gvs[]) 1) >> (metis_tac[]))) >>
  `loc <> LocCode` by
    (`!tr. slot_loc tr <> LocCode` by (Cases >> simp[slot_loc_def]) >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon st.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o cj 3 o REWRITE_RULE [target_post_def] o CONJUNCT1) >>
     Cases_on `p` >> simp[place_ptr_rel_def] >>
     rpt strip_tac >> gvs[]) >>
  qpat_assum `loc <> LocCode` (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th])) >>
  reverse (qsuff_tac `((FST (SND r) = NONE /\ emit_void INVALID [] ca = ((),sb)) \/
    (?loc' old' cb'. FST (SND r) = SOME loc' /\
      emit_op (case loc' of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r] ca = (old',cb') /\ fn_has_code ca cb' func))`)
  >- (disj2_tac >> qexistsl_tac [`loc`,`old`,`cb`] >> fs[]) >>
  disch_tac >>
  drule_all (REWRITE_RULE [expr_sim_inv_gas_obs, tuple_place_target_post_gas_obs]
    (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
             `es` |-> `es with gas_obs := reads`] augassign_load_joint)) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`loadloc`,`loadop`,`loadcs`,`addr`,`cur`,`ptv`,`u`,
      `Gload`,`tnload`] (mk_asm "loadPost"))) >>
  asm "loadPost" (qspec_then `storage_trace_horizon st.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `loadloc = loc /\ loadop = old /\ loadcs = cb` by
    metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `loadloc = loc` SUBST_ALL_TAC >>
  qpat_x_assum `loadop = old` SUBST_ALL_TAC >>
  qpat_x_assum `loadcs = cb` SUBST_ALL_TAC >>
  `expr_body_pre cenv cx env e es` by
    (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `target_indices_pre cenv cx env t` by fs[target_pre_def] >>
  `expr_body_pre cenv cx env e st` by
    (drule_all aug_place_rhs_pre_target_gas_obs >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok st` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `gas_origin_ptr_path _ (v,Gtarget,tnt) [] (OK u,Gload,tnload)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func v fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    stmt_state_rel H ctx func cenv cx st u /\
    storage_well_formed_on cx st (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx st Gload tnload u` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "loadPost" (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     simp[] >>
     qpat_assum `!K. valid_horizon cx st0 K st.storage_trace ==> target_post K ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o cj 2 o REWRITE_RULE [target_post_def] o CONJUNCT1)) >>
  drule_all (Q.INST [`target` |-> `t`, `es` |-> `st`, `sa` |-> `cb`, `sb` |-> `cc`,
                    `old` |-> `old`, `place` |-> `r`] augassign_rhs_saved_outcome) >>
  disch_then (qspecl_then [`RetQ`,`PG`] assume_tac) >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ rhsQ rhsR` >>
  `!gs. read_place cx p (st with gas_obs := gs) = (INL cur,st with gas_obs := gs)` by
    (`read_result cx (PlaceR p) st = (INL cur,st)` by simp[read_result_def] >>
     drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[read_result_def]) >>
  drule_then assume_tac exprSimIfExpWidenedAdapterTheory.place_type_value_gas_obs >>
  qabbrev_tac `goRhs = bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))` >>
  reverse (qsuff_tac `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 goRhs (st,v,Gtarget,tnt) stmtQ stmtR`)
  >- (irule (Q.INST [`s1` |-> `u`,`G1` |-> `Gload`,`tn1` |-> `tnload`]
        gas_outcome_full_zero_prefix_guarded) >>
      simp[] >> conj_tac
      >- (simp[Abbr `goRhs`] >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
      qexistsl_tac [`Gload`,`tnload`,`u`] >> conj_tac
      >- (qx_gen_tac `H` >> disch_tac >>
          asm "loadPost" (qspec_then `H` mp_tac) >> simp[]) >>
      simp[Abbr `goRhs`] >> irule augassign_rhs_bind_full >>
      qexists_tac `\H res ee G tn q. rhsQ H res ee G tn q /\ ~q.vs_halted /\ ee.gas_obs = []` >>
      reverse conj_tac
      >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ rhsQ rhsR` (irule_at Any) >>
          simp[Abbr `rhsR`,Abbr `stmtR`] >> metis_tac[]) >>
      suspend "ordinary_rhs") >>
  disch_tac >>
  irule (Q.INST_TYPE [`:'a` |-> `:unit`]
    gasOutcomeFullStmtsTheory.gas_outcome_full_handler_transport) >>
  qexistsl_tac [`stmtQ`,`stmtR`,`st`,`goRhs`] >> simp[] >>
  `!gs. bind (read_place cx p) (\cur.
      bind (place_type_value cx p) (\ptv.
        bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p)))) (st with gas_obs := gs) =
    goRhs (st with gas_obs := gs)` by simp[bind_def,Abbr `goRhs`] >>
  simp[gasStorageTheory.gas_bad_storage_at_def] >> conj_tac
  >- (qx_genl_tac [`ms`,`err`,`ee`,`leaf`,`fin`] >> disch_tac >>
      qexistsl_tac [`err`,`ee`] >>
      simp[Once ignore_bind_def,bind_assoc] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[vyperStateTheory.evaluation_state_component_equality] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[vyperStateTheory.evaluation_state_component_equality] >>
      `st with gas_obs := [] = st` by
        simp[vyperStateTheory.evaluation_state_component_equality] >>
      qpat_x_assum `gas_exempt_cert _ _ _ (ignore_bind goRhs _) _ _ _ _` mp_tac >>
      simp[Abbr `goRhs`,ignore_bind_def,bind_assoc]) >>
  qx_genl_tac [`ms`,`res`,`ee`,`result`,`G'`,`tn'`] >> strip_tac >>
  qexistsl_tac [`ms`,`res`,`ee`,`result`,`G'`,`tn'`] >> simp[]
QED

Resume augassign_ordinary_full[ordinary_rhs]:
  qx_genl_tac [`ms`,`res`,`ee`,`Gq`,`tnq`,`q`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (rhsQ = _)` (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `rhs` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) >>
  disj1_tac >> qexists_tac `rhs` >> simp[] >>
  qabbrev_tac `rhsReads = gas_explicit ms u.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (st with gas_obs := rhsReads) = (INL rhs,ee)` by
    (pop_assum (fn upd =>
       qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,upd])))) >>
  `is_word_type (expr_type e)` by
    (drule_all aug_place_typing_word >> simp[]) >>
  `expr_body_pre cenv cx env e (st with gas_obs := rhsReads)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >>
  simp[] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME tvR` >>
  drule_all (REWRITE_RULE [ETA_AX] augassign_joint_operand_ready) >>
  strip_tac >>
  drule_all augassign_source_prefix_replay >>
  disch_then (mk_asm "sourceReplay") >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e st cb cc u ee rhs rhsop q /\
       ghost_inv_at (DF H) lo d cenv cx ee Gq tnq q /\
       ghost_kept_at lo cenv st cb Gload tnload u Gq tnq /\
       u.vs_alloca_next <= q.vs_alloca_next` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> rhsQ K _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (rhsQ = _)` (fn th =>
       CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
     BETA_TAC >>
     disch_then (CONJUNCTS_THEN2
       (qx_choose_then `rhs'` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) >>
     `rhs' = rhs` by fs[] >>
     qpat_x_assum `rhs' = rhs` SUBST_ALL_TAC >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee q /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gq tnq q` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> expr_post K ctx func cenv cx e st cb cc u ee rhs rhsop q /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2
       (STRIP_ASSUME_TAC o REWRITE_RULE [expr_post_def]) STRIP_ASSUME_TAC) >>
     simp[]) >>
  qpat_assum `expr_post _ ctx func cenv cx e st cb cc u ee rhs rhsop q`
    (STRIP_ASSUME_TAC o REWRITE_RULE [expr_post_def]) >>
  `type_bits aty MOD 8 = 0` by
    (drule (cj 3 aug_place_typing) >>
     metis_tac[assignable_type_well_formed,stmtSimAugAssignTheory.well_formed_type_bits]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `post_value_type cenv e = expr_type e` SUBST_ALL_TAC >>
  `eval_operand rhsop q = SOME (typed_val_to_w256 tvR rhs)` by
    (irule exprBopSimPropsTheory.expr_val_rel_typed >>
     qexistsl_tac [`cx`,`expr_type e`] >> simp[]) >>
  `op_prov Gq rhsop = NONE /\ op_taint tnq rhsop = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `?x. old = Var x` by metis_tac[compilerInstructionSuffixTheory.added_insts_emit_op] >>
  `!l. old <> Label l /\ rhsop <> Label l` by simp[] >>
  `cb.cs_next_var <= cc.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv cc` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. old = Var x ==> not_fresh_at cc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. FST r = Var x ==> not_fresh_at cc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv cc q` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`u`,`cb`] >> fs[expr_post_def]) >>
  `(bop = Exp ==>
     (IS_SOME (NONE:int option) \/
        ?n. (if bop = Exp then expr_int_literal e else NONE) = SOME n /\ 0 <= n) /\
     (!n. (NONE:int option) = SOME n ==> cur = IntV n) /\
     (!n. (if bop = Exp then expr_int_literal e else NONE) = SOME n ==> rhs = IntV n))` by
    (disch_tac >> qpat_assum `bop = Exp ==> _` drule >> simp[]) >>
  reverse (Cases_on `evaluate_binop
    (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
    ptv bop cur rhs`)
  >- suspend "ordinary_operator_error" >>
  suspend "ordinary_operator_success"
QED

Resume augassign_ordinary_full[ordinary_operator_error]:
  drule_all augassign_operator_source_runtime_error >>
  disch_then (qspec_then `ee` (qx_choose_then `msg` STRIP_ASSUME_TAC)) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    augassign_operator_joint_error) >>
  disch_then (qspec_then `shadow_ctx` (mp_tac o
    SRULE [bodyPtrDefsTheory.stmt_exit_ptr_def])) >>
  disch_then (qspecl_then [`ee`,`PG`]
    (qx_choosel_then [`abortState`,`Gabort`,`tnabort`] (mk_asm "opAbort"))) >>
  irule (Q.INST [`ee` |-> `ee`,`res` |-> `INR (Error (RuntimeError msg))`,
                 `r` |-> `Abort Revert_abort abortState`,
                 `G'` |-> `Gabort`,`tn'` |-> `tnabort`]
    gasOutcomeFullComposeTheory.gas_outcome_full_exit) >>
  simp[bind_def,lift_sum_def,raise_def,fragExecTheory.exit_result_def,Abbr `stmtR`] >>
  qexistsl_tac [`Gabort`,`abortState`,`ee`,`msg`,`tnabort`] >>
  simp[bodyPtrDefsTheory.stmt_exit_ptr_def] >>
  qx_gen_tac `H` >> disch_tac >>
  asm "opAbort" (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> simp[haltExitProjTheory.halt_exit_not_halt]
QED

Resume augassign_ordinary_full[ordinary_operator_success]:
  rename1 `evaluate_binop _ ptv bop cur rhs = INL value` >>
  `bop_result cx aty bop [aty;expr_type e] cur rhs ee = INL value` by
    (drule_all augassign_operator_source_representation >> simp[]) >>
  `value_has_type ptv value` by (drule_all augassign_operator_source_value_type >> simp[]) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    augassign_operator_joint_success) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`w`,`Gw`,`tnw`] (mk_asm "opSuccess"))) >>
  `!gs. eval_stmt cx (AugAssign aty t bop e)
       (es with gas_obs := (reads ++ rhsReads) ++ gs) =
       write_place cx p value (ee with gas_obs := gs)` by
    (asm "sourceReplay" (qspecl_then [`aty`,`bop`] (fn th =>
       simp[APPEND_ASSOC,th,bind_def,lift_sum_def,return_def]))) >>
  `gas_admissible (write_place cx p value) (stmt_res_ok lctx) ee` by
    (qpat_assum `!gs. eval_stmt cx _ _ = write_place cx _ _ _` mp_tac >>
     qpat_assum `gas_admissible (eval_stmt cx _) _ es` mp_tac >>
     qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_replay_admissible]) >>
  simp[lift_sum_def,vyperStateTheory.bind_return] >>
  irule (Q.INST [`s1` |-> `w`,`G1` |-> `Gw`,`tn1` |-> `tnw`]
    gas_outcome_full_zero_prefix_guarded) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
  Cases_on `write_place cx p value ee` >>
  rename1 `write_place cx p value ee = (wr,ff)` >>
  suspend "ordinary_stage_frame"
QED

Resume augassign_ordinary_full[ordinary_stage_frame]:
  asm "opSuccess" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `u.vs_memory = v.vs_memory /\ u.vs_allocas = v.vs_allocas` by
    (conj_tac
     >- (qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``venom_state_vs_memory``) >>
         simp[stateFrameTheory.state_frame_def] >> gvs[stateFrameTheory.state_frame_def]) >>
     qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``venom_state_vs_allocas``) >>
     simp[stateFrameTheory.state_frame_def] >> gvs[stateFrameTheory.state_frame_def]) >>
  `!x z. not_fresh_at ca x /\ lookup_var x v = SOME z ==> lookup_var x u = SOME z` by
    (rpt strip_tac >> simp[]) >>
  `eval_target_place cx t (es with gas_obs := reads ++ rhsReads) =
      (INL p,st with gas_obs := rhsReads)` by
    (qpat_assum `!tail. eval_target_place cx t _ = _` (qspec_then `rhsReads` ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon cx st0 K es.storage_trace ==> _` (qspec_then `H` mp_tac) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
       target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
       stmt_state_rel H ctx func cenv cx st u /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "loadPost" (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!K. valid_horizon cx st0 K st.storage_trace ==>
       target_post K ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload` by
       (simp[NoAsms,bodyPtrDefsTheory.ghost_kept_at_def] >>
        qpat_assum `ghost_kept_at lo cenv (es with gas_obs := reads) sa G0 tn0 s0 Gload tnload`
          (ACCEPT_TAC o SRULE [bodyPtrDefsTheory.ghost_kept_at_def])) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e st cb cc u ee rhs rhsop q /\
       ghost_kept_at lo cenv st cb Gload tnload u Gq tnq /\
       ghost_kept_at lo cenv ee cc Gq tnq q Gw tnw /\
       stmt_state_rel H ctx func cenv cx ee w /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "opSuccess" (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==>
       expr_post K ctx func cenv cx e st cb cc u ee rhs rhsop q /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  suspend "ordinary_join_frame"
QED

Resume augassign_ordinary_full[ordinary_join_frame]:
  `ca.cs_next_var <= cb.cs_next_var /\ cc.cs_next_var <= cd.cs_next_var /\
   sa.cs_next_id <= ca.cs_next_id /\ ca.cs_next_id <= cb.cs_next_id /\
   cb.cs_next_id <= cc.cs_next_id /\ cd.cs_next_var <= sb.cs_next_var`
    by fs[exprLoweringPropsTheory.ci_mono_def] >>
  qpat_assum `!H. valid_horizon cx st0 H st.storage_trace ==>
    target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
    stmt_state_rel H ctx func cenv cx st u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload`
    (assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e st cb cc u ee rhs rhsop q /\
    ghost_kept_at lo cenv st cb Gload tnload u Gq tnq /\
    ghost_kept_at lo cenv ee cc Gq tnq q Gw tnw /\ _`
    (assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
  Q_TAC (C SUBGOAL_THEN (mk_asm "writeFrame"))
    `!H. valid_horizon cx st0 H ff.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee w /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w /\
       return_buf_frame d cenv cd w /\ alloca_history func w /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
       s0.vs_alloca_next <= w.vs_alloca_next /\
       (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
         lookup_var x w = SOME z) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP w.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa x ==> FLOOKUP Gw x = FLOOKUP G0 x /\
         op_taint tnw (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es sa s0 cenv ee w /\
       (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
           off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tnw.t_mem ==> i IN tn0.t_mem)`
  >- (qx_gen_tac `H` >> disch_tac >>
      `(es with gas_obs := reads ++ rhsReads).scopes = es.scopes /\
       (es with gas_obs := reads ++ rhsReads).storage_trace = es.storage_trace /\
       (st with gas_obs := rhsReads).scopes = st.scopes /\
       (st with gas_obs := rhsReads).storage_trace = st.storage_trace` by simp[] >>
      irule (PURE_REWRITE_RULE [tuple_place_target_post_gas_obs,
         exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs,
         exprLoweringPropsTheory.stmt_state_rel_start_gas_obs,
         alloca_frame_gas_obs, vyperStateTheory.evaluation_state_accfupds,
         combinTheory.K_THM, bodyPtrDefsTheory.ghost_kept_at_def]
      (Q.INST [`es0` |-> `es with gas_obs := reads ++ rhsReads`,
               `st` |-> `st with gas_obs := rhsReads`]
        augassign_staged_store_frame)) >>
      qpat_assum `eval_target_place cx t (es with gas_obs := reads ++ rhsReads) = _`
        (irule_at Any) >>
      qpat_assum `bind (eval_expr cx e) (read_result cx) (st with gas_obs := rhsReads) = _`
        (irule_at Any) >>
      qpat_assum `write_place cx p value ee = _` (irule_at Any) >>
      qpat_assum `supported_stmt tops bindings (AugAssign aty t bop e)` (irule_at Any) >>
      qpat_assum `supported_target_info tops bindings t = _` (irule_at Any) >>
      qexistsl_tac [`Type aty`,`u`,`tnload`,`tnq`,`v`,`st0`,`cc`,`cb`,
                    `ca`,`r`,`q`,`PlaceR p`,`rhsop`,`env`,`Gload`,`Gq`] >>
      simp[] >>
      conj_tac
      >- (qx_gen_tac `Hnext` >> disch_tac >>
          qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
            expr_post H ctx func cenv cx e st cb cc u ee rhs rhsop q /\
            (( !x. not_fresh_at cb x ==> _) /\ _) /\ _`
            (qspec_then `Hnext` mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >>
          disch_then (fn th => qpat_assum `u.vs_allocas = v.vs_allocas`
            (fn eq => STRIP_ASSUME_TAC (PURE_REWRITE_RULE [eq] th))) >>
          rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qx_gen_tac `Hnext` >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H st.storage_trace ==>
        target_post H ctx func cenv cx es sa ca s0 st (PlaceR p) (Type aty) r v /\
        stmt_state_rel H ctx func cenv cx st u /\
        (( !x. not_fresh_at sa x ==> _) /\ _)`
        (qspec_then `Hnext` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gw`,`tnw`,`w`] >>
  conj_tac >- (asm "opSuccess" (ACCEPT_TAC o cj 1)) >>
  Cases_on `p`
  >- suspend "ordinary_storage_write"
  >- suspend "ordinary_memory_write" >>
  fs[target_post_def, place_ptr_rel_def]
QED

Resume augassign_ordinary_full[ordinary_storage_write]:
  rename1 `write_place cx (StoragePlace tr slot tv) value ee = (wr,ff)` >>
  `addr = slot /\ loc = slot_loc tr /\ evaluate_type (get_tenv cx) aty = SOME tv` by
    (qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ (PlaceR (StoragePlace tr slot tv)) _ _ _`
       (mp_tac o cj 3 o REWRITE_RULE [target_post_def]) >>
     simp[place_ptr_rel_def]) >>
  `ptv = tv` by fs[] >>
  qpat_x_assum `ptv = tv` SUBST_ALL_TAC >>
  asm "opSuccess" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `op_taint tnw (FST r) = {}` by fs[target_ptr_ok_def] >>
  `emit_void (if tr then TSTORE else SSTORE) [FST r;dst] cd = ((),sb)` by
    (qpat_assum `loc = slot_loc tr` (fn eq =>
       qpat_assum `emit_void _ [FST r;dst] cd = ((),sb)`
         (mp_tac o PURE_REWRITE_RULE [eq])) >>
     Cases_on `tr` >> simp[slot_loc_def,NoAsms]) >>
  qpat_assum `eval_target_place cx t (es with gas_obs := reads ++ rhsReads) = _`
    (qx_choosel_then [`root`,`rtv`,`path`,`delta`] STRIP_ASSUME_TAC o
     MATCH_MP vyperFiniteStoragePreservationTheory.eval_target_place_observed_region) >>
  `MEM (StorageRoot tr root rtv) ee.storage_trace` by
    (irule (cj 1 augassign_storage_current_root) >>
     qpat_assum `eval_target_place cx t (es with gas_obs := reads ++ rhsReads) = _`
       (irule_at Any) >>
     qpat_assum `bind (eval_expr cx e) (read_result cx) (st with gas_obs := rhsReads) = _`
       (irule_at Any) >>
     qpat_assum `storage_subregion rtv path delta tv` (irule_at Any) >> simp[]) >>
  simp[Abbr `stmtR`] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at Any augassign_storage_writeback_full >>
  simp[] >>
  qexistsl_tac [`aty`,`rtv`,`tn0`,`sb`,`sa`,`cd`,`s0`,`wr`,`path`,`dst`,`root`,
                `lctx`,`es`,`ff`,`FST r`,`delta`,`d`,`cenv`,`cenv`,`RetQ`,`G0`] >>
  `write_place cx (StoragePlace tr (n2w root + n2w delta) tv) value ee = (wr,ff)` by
    (qpat_assum `slot = n2w root + n2w delta` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  simp[] >>
  conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      asm "writeFrame" (qspec_then `H` mp_tac) >> simp[] >>
      disch_then (ACCEPT_TAC o cj 8)) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[Abbr `stmtQ`] >>
      strip_tac >> qexists_tac `cenv` >> simp[] >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> disch_tac >>
  qpat_assum `ctx_has_dalloca ctx ==> !u. _` mp_tac >> simp[]
QED

Resume augassign_ordinary_full[ordinary_memory_write]:
  rename1 `write_place cx (MemoryPlace id path) value ee = (wr,ff)` >>
  `read_place cx (MemoryPlace id path) (st with gas_obs := rhsReads) =
      (INL cur,st with gas_obs := rhsReads) /\
   place_type_value cx (MemoryPlace id path) (st with gas_obs := rhsReads) =
      (INL ptv,st with gas_obs := rhsReads)` by simp[] >>
  `~aug_assign_overlap cenv t e` by fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `target_pre cenv cx env t (es with gas_obs := reads ++ rhsReads)` by
    (pure_rewrite_tac[targetSubscriptSplitTheory.target_subscript_pre_gas_obs] >>
     first_assum ACCEPT_TAC) >>
  drule_all (REWRITE_RULE [ETA_AX] augassign_memory_current_source_ready) >>
  strip_tac >>
  `stmt_res_ok lctx wr` by
    (qpat_assum `gas_admissible (write_place cx _ value) _ ee`
       (qspec_then `[]` mp_tac o REWRITE_RULE [gas_admissible_def]) >> simp[]) >>
  `store_lays_out ptv ptv value` by
    (irule stmtSimDeclStoreTheory.store_lays_out_typed >>
     simp[] >> qexistsl_tac [`aty`,`get_tenv cx`] >> simp[]) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ (PlaceR (MemoryPlace id path)) _ _ _`
    (qx_choose_then `a` STRIP_ASSUME_TAC o cj 3 o REWRITE_RULE [target_post_def]) >>
  `a = addr` by fs[] >>
  qpat_x_assum `a = addr` SUBST_ALL_TAC >>
  `loc = LocMemory` by
    (qpat_assum `FST (SND r) = SOME loc` (fn eq =>
       qpat_assum `place_ptr_rel cenv cx v _ _ _ _`
         (mp_tac o PURE_REWRITE_RULE [eq])) >>
     simp[place_ptr_rel_def] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  `place_ptr_rel cenv cx v (PlaceR (MemoryPlace id path)) addr (SOME LocMemory) (Type aty)` by
    (qpat_assum `FST (SND r) = SOME loc` (fn eq =>
       qpat_assum `place_ptr_rel cenv cx v _ _ _ _`
         (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[]) >>
  `!x z. not_fresh_at ca x /\ lookup_var x v = SOME z ==> lookup_var x w = SOME z` by
    (qx_genl_tac [`rootVar`,`rootWord`] >> strip_tac >>
     `not_fresh_at cb rootVar /\ not_fresh_at cc rootVar` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `lookup_var rootVar u = SOME rootWord` by
       (qpat_assum `!x z. not_fresh_at ca x /\ lookup_var x v = SOME z ==> _`
         (qspecl_then [`rootVar`,`rootWord`] mp_tac) >> simp[]) >>
     `lookup_var rootVar q = SOME rootWord` by
       (qpat_assum `!x z. not_fresh_at cb x /\ lookup_var x u = SOME z ==> lookup_var x q = SOME z`
         (qspecl_then [`rootVar`,`rootWord`] mp_tac) >> simp[]) >>
     qpat_assum `!x z. not_fresh_at cc x /\ lookup_var x q = SOME z ==> lookup_var x w = SOME z`
       (qspecl_then [`rootVar`,`rootWord`] mp_tac) >> simp[]) >>
  `place_ptr_rel cenv cx w (PlaceR (MemoryPlace id path)) addr (SOME LocMemory) (Type aty)` by
    (irule aug_place_memory_ptr_frame >>
     qpat_assum `place_ptr_rel cenv cx v _ _ _ _`
       (irule_at Any o SRULE []) >>
     qexists_tac `ca` >> simp[] >> first_assum ACCEPT_TAC) >>
  `emit_void MSTORE [FST r;dst] cd = ((),sb)` by
    (qpat_assum `loc = LocMemory` (fn eq =>
       qpat_assum `emit_void _ [FST r;dst] cd = ((),sb)`
         (mp_tac o PURE_REWRITE_RULE [eq])) >> simp[NoAsms]) >>
  `target_ptr_ok cenv (PlaceR (MemoryPlace id path))
     (FST r,FST (SND r),SND (SND r)) Gw tnw w` by simp[] >>
  asm "writeFrame" assume_tac >>
  drule_all (REWRITE_RULE [pairTheory.PAIR, boolTheory.REFL_CLAUSE, boolTheory.AND_CLAUSES]
    (Q.INST [`u` |-> `(mstore (w2n a) (typed_val_to_w256 etv v) s
                         with vs_inst_idx := LENGTH sb.cs_current_insts)`,
             `un` |-> `tn with t_mem := tn.t_mem DIFF {q | w2n a <= q /\ q < w2n a + 32}`]
      augassign_memory_writeback_full)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`stmtR`,`PG`] assume_tac) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  simp[Abbr `stmtQ`] >>
  strip_tac >> qexists_tac `cenv` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise augassign_ordinary_full

Resume body_augassign_local_full[use_ordinary]:
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac augassign_name_target_info >>
  `~immutable_root cx (NameTarget id)` by
    simp[immutable_root_def,target_root_def] >>
  irule augassign_ordinary_full >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise body_augassign_local_full

Resume body_augassign_toplevel_word_full[use_ordinary]:
  rpt gen_tac >> strip_tac >>
  `FST nsid = NONE` by
    (PairCases_on `nsid` >>
     gvs[Once type_stmt_def, well_typed_target_def] >>
     metis_tac[body_inv_toplevel_target_main, optionTheory.IS_SOME_EXISTS]) >>
  drule_all (Q.INST [`bindings` |-> `bindings`] augassign_scalar_target_route) >>
  disch_then strip_assume_tac >>
  irule augassign_ordinary_full >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise body_augassign_toplevel_word_full

Resume body_augassign_attr_local_full[use_ordinary]:
  rpt gen_tac >> strip_tac >>
  `?pt. supported_target_info tops bindings (AttributeTarget (NameTarget id) fld) = SOME pt` by
    (irule bodyAugPlaceTargetTheory.aug_place_supported_stmt_target_info >>
     qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
     qpat_assum `body_inv _ _ _ _` (irule_at Any) >> simp[]) >>
  `~immutable_root cx (AttributeTarget (NameTarget id) fld)` by
    simp[immutable_root_def,target_root_def] >>
  irule augassign_ordinary_full >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise body_augassign_attr_local_full

Resume body_augassign_attr_storage_full[use_ordinary]:
  rpt gen_tac >> strip_tac >>
  `?pt. supported_target_info tops bindings
          (AttributeTarget (TopLevelNameTarget nsid) fld) = SOME pt` by
    (irule bodyAugPlaceTargetTheory.aug_place_supported_stmt_target_info >>
     qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
     qpat_assum `body_inv _ _ _ _` (irule_at Any) >> simp[]) >>
  `~immutable_root cx (AttributeTarget (TopLevelNameTarget nsid) fld)` by
    metis_tac[bodyAugPlaceTargetTheory.aug_place_storage_field_root] >>
  irule augassign_ordinary_full >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise body_augassign_attr_storage_full

Resume body_augassign_other_full[ordinary]:
  irule augassign_ordinary_full >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Resume body_augassign_other_full[immutable]:
  qpat_x_assum `t = TopLevelNameTarget nsid` SUBST_ALL_TAC >>
  PairCases_on `nsid` >> rename1 `supported_immutable_type tops (src,id) = SOME ity` >>
  `call_evaluation_safe cx []` by
    (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
     goal_assum (drule_at (Pat `call_evaluation_safe _ _`)) >> simp[]) >>
  `cx.in_deploy` by (drule_all augAssignFullImmutableSetupTheory.augassign_immutable_in_deploy >> simp[]) >>
  drule_all bodyImmutableAugAssignFactsTheory.immutable_augassign_metadata >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `off` STRIP_ASSUME_TAC)))))) >>
  drule_all bodyImmutableAugAssignFactsTheory.immutable_augassign_entry >>
  disch_then (qx_choosel_then [`ts`,`imms`,`ptv`,`cur`] STRIP_ASSUME_TAC) >>
  qpat_x_assum `aty = ity` SUBST_ALL_TAC >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule augassign_sep_outcome >>
  qexistsl_tac [`cenv`,`d`,`sa`] >> simp[] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_bad_nil >> simp[] >>
      `gas_bad_storage_at cx st0
         (eval_stmt cx (AugAssign ity (TopLevelNameTarget (cenv.ce_module,id)) bop e)) es s0 []` by
        (irule gasStorageTheory.gas_bad_storage_at_initial >>
         simp[cj 1 vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
      fs[gasStorageTheory.gas_bad_storage_at_def, gasSummaryTheory.gas_explicit_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all augassign_immutable_entry_certificate >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`pre`,`post`,`vis`,`slot`] STRIP_ASSUME_TAC)))) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`,`ca`,`shadow_ca`] (fn th =>
       case rev (CONJUNCTS th) of
         cases::slices => map_every assume_tac (rev slices) >> assume_tac cases
       | [] => NO_TAC))) >>
  `FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
   cenv.ce_module_var_type (cenv.ce_module,id) = SOME ity` by
    metis_tac[] >>
  qpat_x_assum `compile_get_target_ptr _ _ (TopLevelNameTarget _) sa = _` mp_tac >>
  simp[Once compile_get_target_ptr_def, comp_return_def,
       IgnAsm `off = _`, IgnAsm `tops = _`] >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) shadow_sa = _` mp_tac >>
  once_rewrite_tac [cj 14 gasShadowTheory.gas_shadow_expr_def] >>
  simp[Once compile_get_target_ptr_def, comp_return_def,
       IgnAsm `off = _`, IgnAsm `tops = _`] >>
  strip_tac >>
  qpat_x_assum `(Lit _, SOME LocCode, SOME (ValPT _)) = r` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `sa = ca` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `shadow_sa = shadow_ca` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ \/ ?loc cur rhs result s1 s2 s3 ss1 ss2 ss3. _` mp_tac >>
  simp[IgnAsm `off = _`, IgnAsm `tops = _`] >>
  disch_then (qx_choosel_then [`old`,`rhsop`,`dst`,`cb`,`cc`,`cd`,
     `shadow_cb`,`shadow_cc`,`shadow_cd`] STRIP_ASSUME_TAC) >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    dead_lo_ok H (DF H) lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s0 /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G0 tn0` by
    (rpt gen_tac >> strip_tac >> simp[wordArgsPtrTheory.ghost_kept_at_refl] >>
     first_x_assum drule >> simp[]) >>
  drule_all bodyImmutableAugAssignExecTheory.immutable_augassign_prefix_obs >>
  disch_then (mk_asm "immPrefix") >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  suspend "immutable_load"
QED

Resume body_augassign_other_full[immutable_load]:
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by simp[Abbr `H0`] >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
    dead_lo_ok H (DF H) lo cenv cx /\ _` (qspec_then `H0` (drule_then strip_assume_tac)) >>
  drule_all augassign_immutable_load_resources >>
  disch_then (qx_choosel_then [`off'`,`ptv'`,`cur'`] strip_assume_tac) >>
  `off' = off` by
    (qpat_assum `FLOOKUP _ _ = SOME (ImmutableLoc off')` mp_tac >>
     qpat_assum `FLOOKUP _ (src,id) = SOME (ImmutableLoc off)` mp_tac >>
     simp[NoAsms] >> metis_tac[]) >>
  `ptv' = ptv` by metis_tac[optionTheory.SOME_11] >>
  `cur' = cur` by
    (asm "immPrefix" (qspec_then `es.gas_obs` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality, IgnAsm `src = _`]) >>
  qpat_x_assum `off' = off` SUBST_ALL_TAC >>
  qpat_x_assum `ptv' = ptv` SUBST_ALL_TAC >>
  qpat_x_assum `cur' = cur` SUBST_ALL_TAC >>
  `compile_imm_load_word T cenv.ce_imm_alloca (Lit (n2w off)) sa = (old,cb)` by
    fs[compile_ptr_load_def] >>
  `lo <> 0` by
    (qpat_assum `off + 32 <= lo` mp_tac >>
     Cases_on `lo` >> simp[arithmeticTheory.ADD_EQ_0]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s0 = SOME 0w /\
    copy_old_operand sa region /\ op_taint tn0 region = {} /\ op_prov G0 region = NONE` by
    (`immutable_base_zero cenv s0` by metis_tac[stmt_state_rel_immutable_base_zero] >>
     qpat_assum `ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     qpat_assum `immutable_base_zero cenv s0`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.immutable_base_zero_def]) >>
     qpat_assum `local_ptrs_reserved cenv sa`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
     qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> _`
       (assume_tac o REWRITE_RULE [ptrDisciplineTheory.op_taint_def]) >>
     Cases >> simp[copy_old_operand_def, ptrDisciplineTheory.op_taint_def,
                   ptrDisciplineTheory.op_prov_def] >> metis_tac[]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `mem_word_taint tn0.t_mem (w2n (n2w off:bytes32)) = {}` by
    (qpat_assum `w2n (n2w off:bytes32) = off` (fn eq => rewrite_tac[eq]) >>
     simp[ptrDisciplineTheory.mem_word_taint_def, pred_setTheory.EXTENSION,
          IgnAsm `off = _`] >> qx_gen_tac `k` >>
     Cases_on `k < 32` >> simp[IgnAsm `off = _`] >>
     qpat_assum `!j. off <= j /\ j < off + 32 ==> j NOTIN tn0.t_mem` irule >>
     simp[arithmeticTheory.LESS_EQ_ADD, IgnAsm `off = _`]) >>
  `w2n (n2w off:bytes32) + 32 <= lo` by
    (qpat_assum `w2n (n2w off:bytes32) = off` (fn eq => rewrite_tac[eq]) >>
     first_assum ACCEPT_TAC) >>
  drule_all augassign_ctor_word_load >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`u`,`Gload`,`tnload`] strip_assume_tac)))))) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es u /\
     ghost_inv_at (DF H) lo d cenv cx es Gload tnload u /\
     target_ptr_ok cenv (PlaceR (ImmutablePlace src id []))
       (Lit (n2w off),SOME LocMemory,SOME (ValPT ity)) Gload tnload u /\
     ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload /\
     return_buf_frame d cenv cb u /\ alloca_history func u /\
     u.vs_alloca_next = s0.vs_alloca_next /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) [] (OK u,Gload,tnload)` by suspend "immutable_load_post" >>
  pop_assum (mk_asm "immLoadPost") >>
  `local_ptrs_reserved cenv cb` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand old u = SOME (typed_val_to_w256 ptv cur)` by
    (qpat_assum `w2n (n2w off:bytes32) = off` (fn off_word =>
       qpat_assum `mload off s0 = _` (fn loaded =>
         qpat_assum `eval_operand old u = SOME (mload _ s0)`
           (ACCEPT_TAC o REWRITE_RULE [off_word,loaded])))) >>
  `eval_operand (Lit (n2w off)) u = SOME (n2w off)` by simp[venomStateTheory.eval_operand_def] >>
  suspend "immutable_rhs_setup"
QED

Resume body_augassign_other_full[immutable_load_post]:
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!K. valid_horizon cx st0 K es.storage_trace ==>
    dead_lo_ok K (DF K) lo cenv cx /\ _` (qspec_then `H` (drule_then strip_assume_tac)) >>
  `target_ptr_ok cenv (PlaceR (ImmutablePlace src id []))
    (Lit (n2w off),SOME LocMemory,SOME (ValPT ity)) G0 tn0 s0` by
    simp[target_ptr_ok_def, ptrDisciplineTheory.op_taint_def] >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (fn related =>
    qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` (fn ghost =>
      let
        val frame = augassign_load_endpoint_frame
        fun var name th = first (fn x => fst (dest_var x) = name) (free_vars (concl th))
        val horizon = hd (snd (strip_comb (concl related)))
        val dead = hd (snd (strip_comb (concl ghost)))
        val frame = INST_TYPE (match_type (type_of (var "H" frame)) (type_of horizon)) frame
        val frame = INST [var "H" frame |-> horizon, var "D" frame |-> dead] frame
      in
        mp_tac (Q.INST
          [`es` |-> `es`, `s0` |-> `s0`, `G0` |-> `G0`, `tn0` |-> `tn0`,
           `entry` |-> `sa`, `sb` |-> `cb`, `G1` |-> `Gload`, `tn1` |-> `tnload`,
           `p` |-> `ImmutablePlace src id []`,
           `r` |-> `(Lit (n2w off),SOME LocMemory,SOME (ValPT ity))`,
           `s` |-> `s0`, `st` |-> `es`, `G` |-> `G0`, `tn` |-> `tn0`,
           `addr` |-> `n2w off`] frame)
      end)) >>
  impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
     simp[venomStateTheory.eval_operand_def, IgnAsm `off = _`]]) >>
  strip_tac >> simp[IgnAsm `off = _`]
QED

Resume body_augassign_other_full[immutable_rhs_setup]:
  asm "immLoadPost" (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) [] (OK u,Gload,tnload)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i z. frag_reachable ctx func s0 fn i z ==> _`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es u /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es Gload tnload u` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "immLoadPost" (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!K. valid_horizon cx st0 K es.storage_trace ==>
            stmt_state_rel K ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST K) /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST
    [`target` |-> `TopLevelNameTarget (src,id)`, `es` |-> `es`,
     `sa` |-> `cb`, `sb` |-> `cc`, `old` |-> `old`,
     `place` |-> `(Lit (n2w off),SOME LocMemory,SOME (ValPT ity))`]
    augassign_rhs_saved_outcome)) >>
  disch_then (qspecl_then [`RetQ`,`PG`] assume_tac) >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ rhsQ rhsR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ stmtQ stmtR` >>
  qabbrev_tac `p = ImmutablePlace src id []` >>
  qabbrev_tac `goRhs = bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ity of SOME n => n | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p))` >>
  reverse (qsuff_tac `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 goRhs (es,s0,G0,tn0) stmtQ stmtR`)
  >- (irule (Q.INST [`s1` |-> `u`,`G1` |-> `Gload`,`tn1` |-> `tnload`]
        gas_outcome_full_zero_prefix_guarded) >>
      simp[IgnAsm `off = _`, IgnAsm `tops = _`, IgnAsm `cx_tops cx = _`] >> conj_tac
      >- (simp[Abbr `goRhs`] >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
          simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
      qexistsl_tac [`Gload`,`tnload`,`u`] >> conj_tac
      >- (qx_gen_tac `H` >> disch_tac >>
          asm "immLoadPost" (qspec_then `H` mp_tac) >> simp[]) >>
      simp[Abbr `goRhs`, IgnAsm `cx_tops cx = _`] >> irule augassign_rhs_bind_full >>
      qexists_tac `\H res ee G tn q. rhsQ H res ee G tn q /\ ~q.vs_halted /\ ee.gas_obs = []` >>
      reverse conj_tac
      >- (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
          qpat_assum `gas_outcome_full _ _ _ _ _ _ rhsQ rhsR` (irule_at Any) >>
          simp[Abbr `rhsR`,Abbr `stmtR`] >> metis_tac[]) >>
      suspend "immutable_rhs") >>
  disch_tac >>
  irule (Q.INST_TYPE [`:'a` |-> `:unit`]
    gasOutcomeFullStmtsTheory.gas_outcome_full_handler_transport) >>
  qexistsl_tac [`stmtQ`,`stmtR`,`es`,`goRhs`] >> simp[IgnAsm `tops = _`] >>
  qpat_assum `src = cenv.ce_module` (fn eq =>
    asm "immPrefix" (STRIP_ASSUME_TAC o REWRITE_RULE [FORALL_AND_THM] o SUBS [eq])) >>
  `!gs. eval_stmt cx (AugAssign ity (TopLevelNameTarget (cenv.ce_module,id)) bop e)
      (es with gas_obs := gs) = goRhs (es with gas_obs := gs)` by
    simp[augassign_source_bind,bind_def,Abbr `goRhs`] >>
  simp[gasStorageTheory.gas_bad_storage_at_def, IgnAsm `tops = _`] >> conj_tac
  >- (qx_genl_tac [`ms`,`err`,`ee`,`leaf`,`fin`] >> disch_tac >>
      qexistsl_tac [`err`,`ee`] >>
      simp[augassign_source_bind,Once ignore_bind_def,bind_assoc] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[gasOutcomeInitialObsPtrTheory.gas_exempt_cert_initial_obs] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[gasOutcomeInitialObsPtrTheory.gas_exempt_cert_initial_obs] >>
      irule gasExemptPurePrefixTheory.gas_exempt_cert_pure_prefix >>
      simp[gasOutcomeInitialObsPtrTheory.gas_exempt_cert_initial_obs] >>
      qpat_x_assum `gas_exempt_cert _ _ _ (ignore_bind goRhs _) _ _ _ _` mp_tac >>
      simp[Abbr `goRhs`,ignore_bind_def,bind_assoc,
           gasOutcomeInitialObsPtrTheory.gas_exempt_cert_initial_obs]) >>
  reverse conj_tac
  >- (qpat_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`ms`,`res`,`ee`,`result`,`G'`,`tn'`] >> strip_tac >>
  qexistsl_tac [`ms`,`res`,`ee`,`result`,`G'`,`tn'`] >> simp[]
QED

Resume body_augassign_other_full[immutable_rhs]:
  qx_genl_tac [`ms`,`res`,`ee`,`Gq`,`tnq`,`q`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (rhsQ = _)` (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  BETA_TAC >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `rhs` (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))
    STRIP_ASSUME_TAC) >>
  disj1_tac >> qexists_tac `rhs` >> simp[] >>
  qabbrev_tac `rhsReads = gas_explicit ms u.vs_gas_readings` >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := rhsReads) = (INL rhs,ee)` by
    (pop_assum (fn upd =>
       qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,upd])))) >>
  `is_word_type (expr_type e)` by (drule_all aug_place_typing_word >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := rhsReads)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >>
  simp[] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME tvR` >>
  drule_all (REWRITE_RULE [ETA_AX] augassign_joint_operand_ready) >> strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e es cb cc u ee rhs rhsop q /\
       ghost_inv_at (DF H) lo d cenv cx ee Gq tnq q /\
       ghost_kept_at lo cenv es cb Gload tnload u Gq tnq /\
       u.vs_alloca_next <= q.vs_alloca_next` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K ee.storage_trace ==> rhsQ K _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (rhsQ = _)` (fn th =>
       CONV_TAC (LAND_CONV (REWRITE_CONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
     BETA_TAC >>
     disch_then (CONJUNCTS_THEN2
       (qx_choose_then `rhs'` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) >>
     `rhs' = rhs` by fs[] >>
     qpat_x_assum `rhs' = rhs` SUBST_ALL_TAC >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee q /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gq tnq q` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> expr_post K ctx func cenv cx e es cb cc u ee rhs rhsop q /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2
       (STRIP_ASSUME_TAC o REWRITE_RULE [expr_post_def]) STRIP_ASSUME_TAC) >>
     simp[]) >>
  qpat_assum `expr_post _ ctx func cenv cx e es cb cc u ee rhs rhsop q`
    (STRIP_ASSUME_TAC o REWRITE_RULE [expr_post_def]) >>
  `type_bits ity MOD 8 = 0` by
    (drule (cj 3 aug_place_typing) >>
     metis_tac[assignable_type_well_formed,stmtSimAugAssignTheory.well_formed_type_bits]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `post_value_type cenv e = expr_type e` SUBST_ALL_TAC >>
  `eval_operand rhsop q = SOME (typed_val_to_w256 tvR rhs)` by
    (irule exprBopSimPropsTheory.expr_val_rel_typed >>
     qexistsl_tac [`cx`,`expr_type e`] >> simp[]) >>
  `op_prov Gq rhsop = NONE /\ op_taint tnq rhsop = {}` by
    fs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `!l. old <> Label l /\ rhsop <> Label l` by
    (qpat_assum `compile_imm_load_word T cenv.ce_imm_alloca _ _ = _`
       (mp_tac o MATCH_MP fragFuelExprHelpersTheory.compile_ptr_load_not_label o
        ONCE_REWRITE_RULE [GSYM (cj 5 compile_ptr_load_def)]) >> simp[]) >>
  `cb.cs_next_var <= cc.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv cc` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cc x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. old = Var x ==> not_fresh_at cc x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `return_buf_frame d cenv cc q` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`u`,`cb`] >> fs[expr_post_def]) >>
  `(bop = Exp ==>
     (IS_SOME (NONE:int option) \/
        ?n. (if bop = Exp then expr_int_literal e else NONE) = SOME n /\ 0 <= n) /\
     (!n. (NONE:int option) = SOME n ==> cur = IntV n) /\
     (!n. (if bop = Exp then expr_int_literal e else NONE) = SOME n ==> rhs = IntV n))` by
    (disch_tac >> qpat_assum `bop = Exp ==> _` drule >> simp[]) >>
  reverse (Cases_on `evaluate_binop
    (case type_to_int_bound ity of SOME n => n | NONE => Unsigned 0)
    ptv bop cur rhs`)
  >- suspend "immutable_operator_error" >>
  suspend "immutable_operator_success"
QED

Resume body_augassign_other_full[immutable_operator_error]:
  drule_all augassign_operator_source_runtime_error >>
  disch_then (qspec_then `ee` (qx_choose_then `msg` STRIP_ASSUME_TAC)) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    augassign_operator_joint_error) >>
  disch_then (qspec_then `shadow_ctx` (mp_tac o
    SRULE [bodyPtrDefsTheory.stmt_exit_ptr_def])) >>
  disch_then (qspecl_then [`ee`,`PG`]
    (qx_choosel_then [`abortState`,`Gabort`,`tnabort`] (mk_asm "opAbort"))) >>
  irule (Q.INST [`ee` |-> `ee`,`res` |-> `INR (Error (RuntimeError msg))`,
                 `r` |-> `Abort Revert_abort abortState`,
                 `G'` |-> `Gabort`,`tn'` |-> `tnabort`]
    gasOutcomeFullComposeTheory.gas_outcome_full_exit) >>
  simp[bind_def,lift_sum_def,raise_def,fragExecTheory.exit_result_def,Abbr `stmtR`] >>
  qexistsl_tac [`Gabort`,`abortState`,`ee`,`msg`,`tnabort`] >>
  simp[bodyPtrDefsTheory.stmt_exit_ptr_def] >>
  qx_gen_tac `H` >> disch_tac >>
  asm "opAbort" (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> simp[haltExitProjTheory.halt_exit_not_halt]
QED

Resume body_augassign_other_full[immutable_operator_success]:
  rename1 `evaluate_binop _ ptv bop cur rhs = INL value` >>
  `bop_result cx ity bop [ity;expr_type e] cur rhs ee = INL value` by
    (drule_all augassign_operator_source_representation >> simp[]) >>
  `value_has_type ptv value` by (drule_all augassign_operator_source_value_type >> simp[]) >>
  drule_all (SIMP_RULE (srw_ss()) [pairTheory.FST] (Q.INST
    [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
     `r` |-> `(Lit (n2w off),SOME LocMemory,SOME (ValPT ity))`]
    augassign_operator_joint_success)) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`w`,`Gw`,`tnw`] (mk_asm "opSuccess"))) >>
  simp[lift_sum_def,vyperStateTheory.bind_return] >>
  irule (Q.INST [`s1` |-> `w`,`G1` |-> `Gw`,`tn1` |-> `tnw`]
    gas_outcome_full_zero_prefix_guarded) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_write_place] >>
  Cases_on `write_place cx p value ee` >>
  rename1 `write_place cx p value ee = (wr,ff)` >>
  suspend "immutable_stage_frame"
QED

Resume body_augassign_other_full[immutable_stage_frame]:
  asm "opSuccess" (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `u.vs_memory = s0.vs_memory /\ u.vs_allocas = s0.vs_allocas` by
    (conj_tac
     >- (qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``venom_state_vs_memory``) >>
         simp[stateFrameTheory.state_frame_def] >> gvs[stateFrameTheory.state_frame_def]) >>
     qpat_assum `state_frame u = _` (mp_tac o AP_TERM ``venom_state_vs_allocas``) >>
     simp[stateFrameTheory.state_frame_def] >> gvs[stateFrameTheory.state_frame_def]) >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x u = SOME z` by
    (rpt strip_tac >> simp[]) >>
  `supported_expr tops e` by
    (drule_then ACCEPT_TAC (cj 1 supportedStmtsTheory.supported_augassign_contract)) >>
  `local_ptrs_reserved cenv cd` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def,exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `sa.cs_next_var <= cb.cs_next_var /\ cc.cs_next_var <= cd.cs_next_var /\
   sa.cs_next_id <= cb.cs_next_id /\ cb.cs_next_id <= cc.cs_next_id`
    by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\ stmt_state_rel H ctx func cenv cx es u` by
    (qx_gen_tac `H` >> disch_tac >>
     asm "immLoadPost" (qspec_then `H` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee w /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w` by
    (qx_gen_tac `H` >> disch_tac >> asm "opSuccess" (qspec_then `H` mp_tac) >> simp[]) >>
  suspend "immutable_join_frame"
QED

Resume body_augassign_other_full[immutable_join_frame]:
  qpat_x_assum `Abbrev (p = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `cd.cs_next_var <= sb.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> expr_post H ctx func cenv cx e es cb cc u ee rhs rhsop q /\ _`
    (assume_tac o cj 1) >>
  Q_TAC (C SUBGOAL_THEN (mk_asm "writeFrame"))
    `!H. valid_horizon cx st0 H ff.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee w /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w /\
       return_buf_frame d cenv cd w /\ alloca_history func w /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
       s0.vs_alloca_next <= w.vs_alloca_next /\
       (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
         lookup_var x w = SOME z) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
         FLOOKUP w.vs_allocas aid = SOME b) /\
       (!x. not_fresh_at sa x ==> FLOOKUP Gw x = FLOOKUP G0 x /\
         op_taint tnw (Var x) = op_taint tn0 (Var x)) /\
       alloca_frame cenv es sa s0 cenv ee w /\
       (!aid off sz i.
         FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
           off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tnw.t_mem ==> i IN tn0.t_mem)`
  >- (qx_gen_tac `H` >> disch_tac >>
      irule (PURE_REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_start_gas_obs,
          alloca_frame_gas_obs, vyperStateTheory.evaluation_state_accfupds,
          combinTheory.K_THM, bodyPtrDefsTheory.ghost_kept_at_def,
          exprSimExtract32PostTheory.extract32_expr_post_start_gas_obs]
        (Q.INST [`es0` |-> `es with gas_obs := rhsReads`]
          augassign_immutable_staged_store_frame)) >>
      qpat_assum `bind (eval_expr cx e) (read_result cx) (es with gas_obs := rhsReads) = _`
        (irule_at Any) >>
      qpat_assum `write_place cx _ value ee = _` (irule_at Any) >>
      qexistsl_tac [`u`,`tops`,`tnload`,`tnq`,`st0`,`cc`,`cb`,`q`,`rhsop`,`Gload`,`Gq`] >>
      map_every (fn g => qpat_assum g
         (STRIP_ASSUME_TAC o PURE_REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]))
        [`ghost_kept_at lo cenv ee cc Gq tnq q Gw tnw`,
         `ghost_kept_at lo cenv es sa G0 tn0 s0 Gload tnload`,
         `ghost_kept_at lo cenv es cb Gload tnload u Gq tnq`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "immutable_writeback"
QED

Resume body_augassign_other_full[immutable_writeback]:
  qexistsl_tac [`Gw`,`tnw`,`w`] >>
  conj_tac >- (asm "opSuccess" (ACCEPT_TAC o cj 1)) >>
  `expr_body_pre cenv cx env e (es with gas_obs := rhsReads)` by simp[] >>
  `FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ity` by
    (qpat_assum `src = cenv.ce_module` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule_all (REWRITE_RULE [ETA_AX] (Q.INST [`src` |-> `cenv.ce_module`]
    augassign_immutable_current_source_ready)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`currentImms`,`currentVal`] STRIP_ASSUME_TAC)) >>
  `write_place cx (ImmutablePlace cenv.ce_module id []) value ee = (wr,ff)` by
    (qpat_assum `src = cenv.ce_module` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_assum `tops = pre ++ VariableDecl vis Immutable id ity slot :: post`
    (SUBST1_TAC o SYM) >>
  qpat_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
  qpat_assum `src = cenv.ce_module` SUBST1_TAC >>
  drule_all bodyImmutableAugAssignStoreTheory.immutable_augassign_write_source >>
  disch_then (qspec_then `value` strip_assume_tac) >>
  `wr = INL ()` by fs[] >>
  qpat_x_assum `wr = INL ()` SUBST_ALL_TAC >>
  `ff.storage_trace = ee.storage_trace /\ ff.gas_obs = []` by
    (qpat_assum `write_place cx (ImmutablePlace cenv.ce_module id []) value ee = (INL (),ff)`
       (strip_assume_tac o MATCH_MP vyperPlaceFramesTheory.write_immutable_place_frame) >>
     simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ff.storage_trace) ff.storage_trace` by fs[] >>
  qabbrev_tac `Hwrite = storage_trace_horizon ff.storage_trace` >>
  `valid_horizon cx st0 Hwrite ff.storage_trace` by simp[Abbr `Hwrite`] >>
  asm "writeFrame" (qspec_then `Hwrite` (drule_then strip_assume_tac)) >>
  `compile_imm_store_word cenv.ce_imm_alloca (Lit (n2w off)) dst cd = ((),sb)` by
    fs[compile_ptr_store_def] >>
  `compile_assign_value cenv (Lit (n2w off)) LocCode dst T NONE ity ity 32 cd = ((),sb)` by
    simp[compile_assign_value_def, comp_bind_def, comp_return_def,
         IgnAsm `off = _`, IgnAsm `tops = _`] >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region w = SOME 0w /\
    op_taint tnw region = {} /\ op_prov Gw region = NONE` by
    (`immutable_base_zero cenv w` by metis_tac[stmt_state_rel_immutable_base_zero] >>
     qpat_assum `ghost_inv_at (DF Hwrite) lo d cenv cx ee Gw tnw w`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     qpat_assum `immutable_base_zero cenv w`
       (strip_assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.immutable_base_zero_def]) >>
     qpat_assum `!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> _`
       (assume_tac o REWRITE_RULE [ptrDisciplineTheory.op_taint_def]) >>
     Cases >> simp[ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
     metis_tac[]) >>
  `off < dimword (:256) /\ allocas_from lo w /\ lo <= w.vs_alloca_next` by
    (conj_tac
     >- (qpat_assum `w2n (n2w off:bytes32) = off`
           (fn th => ACCEPT_TAC (REWRITE_RULE [th] (ISPEC ``n2w off:bytes32`` w2n_lt)))) >>
     qpat_assum `ghost_inv_at (DF Hwrite) lo d cenv cx ee Gw tnw w`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (Lit (n2w off)) w = SOME (n2w off)` by simp[venomStateTheory.eval_operand_def] >>
  `!x. dst = Var x ==> not_fresh_at cd x` by
    (qpat_assum `compile_binop _ _ _ _ _ _ cc = (dst,cd)`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [safe_operand_def] o
        MATCH_MP compile_binop_safe_operand)) >>
  drule_all body_assign_word_store_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`rawStore`,`Gf`,`tf`] strip_assume_tac))))) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region w = SOME 0w` by
    (qx_gen_tac `region` >> disch_tac >>
     qpat_assum `!r. cenv.ce_imm_alloca = SOME r ==> eval_operand r w = SOME 0w /\ _`
       (qspec_then `region` (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  drule_all immutable_assign_word_store >>
  disch_then (qspec_then `ctx` (qx_choose_then `storeResult` strip_assume_tac)) >>
  `storeResult = rawStore` by metis_tac[venomExecSemanticsTheory.exec_result_11] >>
  qpat_x_assum `storeResult = rawStore` SUBST_ALL_TAC >>
  qpat_x_assum `write_place cx (ImmutablePlace cenv.ce_module id []) value ee =
    (INL (),ee with immutables := _)` kall_tac >>
  suspend "immutable_store_post"
QED

Resume body_augassign_other_full[immutable_store_post]:
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qabbrev_tac `endState = rawStore with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl_tac [`Gf`,`ff`,`INL ()`,`endState`,`tf`] >>
  conj_tac
  >- (qpat_assum `write_place cx (ImmutablePlace cenv.ce_module id []) value ee = (INL (),ff)`
        (ACCEPT_TAC o MATCH_MP bodyImmutableAugAssignExecTheory.immutable_write_place_gas_obs)) >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[Abbr `endState`] >>
  `ff with gas_obs := [] = ff` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qpat_assum `ff with gas_obs := [] = ff` (fn th => simp_tac bool_ss [th]) >>
  asm "writeFrame" (qspec_then `H` (drule_then strip_assume_tac)) >>
  `dead_lo_ok H (DF H) lo cenv cx` by metis_tac[] >>
  `!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at cd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at cd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS] >>
  `!i. i < lo /\ i IN tf.t_mem ==>
     imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo rawStore.vs_memory) i` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gw tnw w`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
     qpat_assum `rawStore.vs_memory = _` SUBST1_TAC >>
     qpat_assum `tf.t_mem = _` (fn th => rewrite_tac[th]) >>
     rpt gen_tac >> strip_tac >>
     irule (INST_TYPE [alpha |-> ``:256``] augassign_immutable_word_dead_mask) >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `tops = _`)) >>
     simp[IgnAsm `off = _`, IgnAsm `tops = _`] >>
     qexists_tac `tnw.t_mem` >>
     fs[IgnAsm `off = _`, IgnAsm `tops = _`] >> metis_tac[]) >>
  drule_all immutable_word_store_endpoint >>
  disch_then (qspec_then `lctx` mp_tac) >>
  qpat_assum `Abbrev (endState = _)`
    (fn th => simp_tac bool_ss [LET_THM,GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  strip_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL rhs,ee)`
       (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >>
     simp[]) >>
  `ci_mono sa cd` by metis_tac[exprLoweringPropsTheory.ci_mono_trans] >>
  `sa.cs_next_var <= cd.cs_next_var /\ sa.cs_next_id <= cd.cs_next_id` by
    (qpat_assum `ci_mono sa cd`
       (ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def])) >>
  `alloca_frame cenv es sa s0 cenv ff endState` by
    (irule alloca_frame_trans >> qexistsl [`cenv`,`ee`,`w`,`cd`] >> simp[]) >>
  qpat_assum `stmt_post H ctx func cx lctx cenv cenv cd sb ee w (INL ()) ff endState`
    (STRIP_ASSUME_TAC o REWRITE_RULE [stmt_post_def]) >>
  qpat_x_assum `cenv'' = cenv` SUBST_ALL_TAC >>
  `!x. not_fresh_at sa x ==> not_fresh_at cd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
     lookup_var x endState = SOME z` by
    (qx_genl_tac [`x`,`z`] >> strip_tac >>
     qpat_assum `!x z. not_fresh_at cd x /\ lookup_var x w = SOME z ==> _`
       (qspecl_then [`x`,`z`] mp_tac) >>
     qpat_assum `!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x w = SOME z`
       (qspecl_then [`x`,`z`] mp_tac) >> simp[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G0 x /\
     op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> FLOOKUP Gw x = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     `not_fresh_at cd x` by simp[] >>
     qpat_assum `!x. not_fresh_at cd x ==> lookup_var x endState = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> simp[]) >>
  `!i. i IN tf.t_mem ==> i IN tnw.t_mem` by
    (qpat_assum `tf.t_mem = _` (fn th => simp_tac (srw_ss()) [th, pred_setTheory.IN_DIFF])) >>
  simp[Abbr `stmtQ`, IgnAsm `tf.t_mem = _`] >>
  rpt conj_tac >> TRY (qexists_tac `cenv`) >> simp[IgnAsm `tf.t_mem = _`] >>
  rpt strip_tac >>
  qpat_assum `!i. i IN tf.t_mem ==> i IN tnw.t_mem` (drule_then assume_tac) >>
  qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> i IN tn0.t_mem`
    (drule_all_then ACCEPT_TAC)
QED

Finalise body_augassign_other_full
