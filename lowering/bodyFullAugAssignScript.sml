(*
 * Augmented assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAugAssign
Ancestors bodyPtrDefs[qualified,ignore_grammar]
  stateRelProj
  augAssignFullTargetRoutes augAssignFullEntryPre augAssignFullCodeStages
  augAssignFullBindStages augAssignFullSourceReplay augAssignFullRhsSaved
  augAssignFullLoad augAssignFullImmutableValidLoad augAssignFullImmutableCertificate
  augAssignFullStageFrames augAssignFullImmutableStageFrames augAssignFullWriteback
  augAssignFullOperandReady augAssignFullOperatorSource augAssignFullMemoryResultSafety
  augAssignFullCurrentSource augAssignFullOperator bodyFullBuiltinWordPowCompose
  bodyInvNoDalloca exprSimSource targetPlaceSim
  bodyFullTarget bodyFullTargetDefs bodyPtrPopTargetFragTransport
  stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory stmtSimProps loweringPosts
  gasContext targetPlaceSimCases stmtSimDefs vyperExprNoControl
  augAssignStorageFieldSource tuplePlaceHeadGas gasOutcomeFullGuarded
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

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
  cheat
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
  cheat
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
  cheat
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
  cheat
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

Resume body_augassign_other_full[ordinary]:
  `target_pre cenv cx env t es` by
    (drule_all augassign_entry_target_pre >> simp[]) >>
  `target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx env t es` by
    (irule body_target_place_sim_full >> simp[] >> qexists_tac `tops` >> simp[]) >>
  simp[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
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

Resume body_augassign_other_full[ordinary_rhs]:
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
       ghost_kept_at lo cenv st cb Gload tnload u Gq tnq` by
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

Resume body_augassign_other_full[ordinary_operator_error]:
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

Resume body_augassign_other_full[ordinary_operator_success]:
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
  Cases_on `p`
  >- suspend "ordinary_storage_write"
  >- suspend "ordinary_memory_write" >>
  fs[target_post_def, place_ptr_rel_def]
QED
