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
  stateRelProj
  augAssignFullTargetRoutes augAssignFullEntryPre augAssignFullCodeStages
  augAssignFullBindStages augAssignFullSourceReplay augAssignFullRhsSaved
  augAssignFullLoad augAssignFullImmutableValidLoad augAssignFullImmutableCertificate
  augAssignFullStageFrames augAssignFullImmutableStageFrames augAssignFullWriteback
  augAssignFullOperandReady augAssignFullOperatorSource
  augAssignFullCurrentSource augAssignFullOperator bodyFullBuiltinWordPowCompose
  bodyInvNoDalloca exprSimSource targetPlaceSim
  bodyFullTarget bodyFullTargetDefs bodyPtrPopTargetFragTransport
  stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory stmtSimProps loweringPosts
  gasContext targetPlaceSimCases stmtSimDefs vyperExprNoControl
  augAssignStorageFieldSource tuplePlaceHeadGas gasOutcomeFullGuarded
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  bodyFullShared vyperEvalExprPreservesScopesDom vyperScopePreservation
  vyperStatePreservation vyperStorageFootprint vyperStorageTrace

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
    supported_stmt tops bindings (AugAssign aty (NameTarget id) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\
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
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (NameTarget id) bop e)))
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
    supported_stmt tops bindings (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (TopLevelNameTarget nsid) bop e) ==>
       occurs_abi_decode_target target tops) /\
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
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)))
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
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
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
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)))
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
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
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
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) es
Proof
  suspend "use_ordinary"
QED

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
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
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
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
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
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
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
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
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
  qmatch_goalsub_abbrev_tac
    `gas_outcome_full _ _ _ _ _ _ stmtQ stmtR` >>
  rewrite_tac[augassign_source_bind] >>
  irule augassign_target_bind_full >>
  qexists_tac `\H res ee G tn u. targetQ H res ee G tn u /\
    ~u.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- ((irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
      simp[Abbr `targetR`, Abbr `stmtR`] >>
      rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[] >> drule_all augassign_expr_exit_to_stmt_exit >>
      disch_then (qspecl_then [`gt`,`RetQ`] strip_assume_tac) >> simp[] >> (gvs[]))) >>
  qx_genl_tac [`marks`,`res`,`st`,`Gtarget`,`tnt`,`v`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon st.storage_trace) st.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
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
  reverse (qsuff_tac `((FST (SND r) = NONE /\ emit_void INVALID [] ca = ((),sb)) \/
    (?loc' old' cb'. FST (SND r) = SOME loc' /\
      emit_op (case loc' of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r] ca = (old',cb') /\ fn_has_code ca cb' func))`)
  >- (disj2_tac >> qexistsl_tac [`loc`,`old`,`cb`] >> simp[]) >>
  disch_tac >>
  qmatch_asmsub_abbrev_tac `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)` >>
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
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_no_wrap inst q` by
    metis_tac[pow_compose_reachable_no_wrap] >>
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
    metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_root_not_immutable] >>
  irule augassign_ordinary_full >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Finalise body_augassign_local_full

Resume body_augassign_toplevel_word_full[use_ordinary]:
  rpt gen_tac >> strip_tac >>
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
    metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_root_not_immutable] >>
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
    metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_root_not_immutable] >>
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
  drule_all (Q.INST [`s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`]
    augassign_immutable_load_valid_framed_joint) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`off'`,`ptv'`,`cur'`] STRIP_ASSUME_TAC)) >>
  `off' = off /\ ptv' = ptv` by
    (conj_tac >- (qpat_assum `FLOOKUP _ _ = SOME (ImmutableLoc off')` mp_tac >>
                   qpat_assum `FLOOKUP _ (src,id) = SOME (ImmutableLoc off)` mp_tac >>
                   simp[NoAsms] >> metis_tac[]) >>
     metis_tac[optionTheory.SOME_11]) >>
  qpat_x_assum `off' = off` SUBST_ALL_TAC >>
  qpat_x_assum `ptv' = ptv` SUBST_ALL_TAC >>
  qpat_x_assum `!sa' old' sb'. emit_op MLOAD _ sa' = (old',sb') /\ _ ==> _`
    (qspecl_then [`sa`,`old`,`cb`] mp_tac) >>
  (impl_tac >- simp[IgnAsm `off = _`, IgnAsm `tops = _`]) >>
  disch_then (qx_choosel_then [`u`,`Gload`,`tnload`] (mk_asm "immLoadPost")) >>
  drule_all bodyImmutableAugAssignExecTheory.immutable_augassign_prefix_obs >>
  disch_then (mk_asm "immPrefix") >>
  `cur' = cur` by
    (asm "immPrefix" (qspec_then `es.gas_obs` mp_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality, IgnAsm `src = _`]) >>
  qpat_x_assum `cur' = cur` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  asm "immLoadPost" (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_no_wrap inst q` by
    metis_tac[pow_compose_reachable_no_wrap] >>
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
  `?x. old = Var x` by metis_tac[compilerInstructionSuffixTheory.added_insts_emit_op] >>
  `!l. old <> Label l /\ rhsop <> Label l` by simp[] >>
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
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at Any (REWRITE_RULE [boolTheory.REFL_CLAUSE, boolTheory.AND_CLAUSES]
    (Q.INST [`u` |-> `(mstore off (typed_val_to_w256 tv v) s
                         with vs_inst_idx := LENGTH sb.cs_current_insts)`,
             `un` |-> `tn with t_mem := tn.t_mem DIFF {q | off <= q /\ q < off + 32}`]
      augassign_immutable_writeback_full)) >>
  qpat_assum `write_place cx (ImmutablePlace cenv.ce_module id []) value ee = _`
    (irule_at Any) >>
  qpat_assum `FLOOKUP (get_source_immutables cenv.ce_module currentImms) id = SOME (ptv,currentVal)`
    (irule_at Any) >>
  qpat_assum `emit_void MSTORE [Lit (n2w off);dst] cd = ((),sb)` (irule_at Any) >>
  qexistsl_tac [`vis`,`ity`,`tops`,`tn0`,`slot`,`sa`,`s0`,`pre`,`post`,
                `lctx`,`es`,`env`,`d`,`cenv`,`stmtR`,`G0`] >>
  rpt (conj_tac >- FIRST [first_assum ACCEPT_TAC, asm "writeFrame" ACCEPT_TAC]) >>
  reverse conj_tac >- simp[NoAsms] >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  simp[Abbr `stmtQ`] >>
  strip_tac >> qexists_tac `cenv` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise body_augassign_other_full
