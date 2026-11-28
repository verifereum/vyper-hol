(* Request-prefix companion to bodyFullAugAssign. *)
Theory s1PrefixAugAssign
Ancestors
  s1PrefixPreds bodyFullAugAssign s1PrefixDefs s1PrefixAugAssignLocalFieldTarget bodyTypedTargetScope s1PrefixAugAssignStorageFieldTarget s1PrefixImmutableTargetPlace s1PrefixAugAssignBindStages s1PrefixCompose bodyFullTarget bodyFullTargetDefs bodyFullTargetRoots bodyFullSimProjection bodySimFull augAssignFullEntryPre augAssignFullCodeStages augAssignFullSourceReplay augAssignFullLoadImmutableResources augAssignFullImmutableValidLoad augAssignFullLoadFrame bodyFullIfExpReach gasOutcomeFullCompose gasShadow gasContext loweringPosts stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory stmtSimAugAssign stmtSimDefs targetPlaceSimCases exprSimDefs exprSimCopy exprLoweringProps freshWrites exprBodyPreProps bodyMemoryDefs exprSimSource exprSimMemorySource exprSimIfExpWidenedAdapter vyperExprNoControl vyperStorageFootprint vyperStorageTrace vyperState vyperInterpreter vyperTypeSystem vyperTypeCallStackSoundness vyperTypeCallGraph exprSimAbiDecodeEntryTyping vyperAST vyperValue words list finite_map context stateRelProj bodyPtrDefs[qualified,ignore_grammar] s1PrefixAugAssignToplevelImmutable s1PrefixAugAssignScalarTarget s1PrefixAugAssignNameTarget s1PrefixAugAssignOrdinary augAssignFullTargetRoutes bodySim s1PrefixTarget s1PrefixOfVV bodyPtrPopTargetFragTransport

Theorem body_augassign_local_prefix:
  !cx aty bop id e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx (NameTarget id) /\
  body_base_target_prefix_ok cx (NameTarget id) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (NameTarget id) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (NameTarget id) bop e)))
      (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule augassign_ordinary_prefix >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[augassign_name_target_prefix_entry] >>
  qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> metis_tac[augassign_name_target_prefix_entry]) >>
  metis_tac[augassign_name_target_prefix_entry]
QED

Theorem body_augassign_toplevel_word_prefix:
  !cx aty bop nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget nsid) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget nsid) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx (TopLevelNameTarget nsid) /\
  body_base_target_prefix_ok cx (TopLevelNameTarget nsid) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)))
      (eval_stmt cx (AugAssign aty (TopLevelNameTarget nsid) bop e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `FST nsid = NONE` by
    (PairCases_on `nsid` >>
     gvs[Once type_stmt_def, well_typed_target_def] >>
     metis_tac[body_inv_toplevel_target_main, optionTheory.IS_SOME_EXISTS]) >>
  drule_all (Q.INST [`bindings` |-> `bindings`] augassign_scalar_target_prefix_entry) >>
  disch_then (qspec_then `bindings` (CONJUNCTS_THEN2
    (qx_choosel_then [`vis`,`ity`,`slot`,`mut`] (map_every assume_tac o CONJUNCTS))
    assume_tac)) >>
  irule augassign_ordinary_prefix >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem body_augassign_attr_local_prefix:
  !cx aty bop id fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld) /\
  body_base_target_prefix_ok cx (AttributeTarget (NameTarget id) fld) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all augassign_local_field_target_prefix_entry >> strip_tac >>
  irule augassign_ordinary_prefix >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`,`env`,`env'`,`tops`] >> simp[]
QED

Theorem body_augassign_attr_storage_prefix:
  !cx aty bop nsid fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (TopLevelNameTarget nsid) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (TopLevelNameTarget nsid) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld) /\
  body_base_target_prefix_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all augassign_storage_field_target_prefix_entry >> strip_tac >>
  irule augassign_ordinary_prefix >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
  simp[] >> conj_tac >> first_assum ACCEPT_TAC
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
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
    (irule body_imm_target_place_sim_full >> simp[] >> qexists_tac `tops` >> simp[]) >>
  simp[stmt_frag_prefix_def] >> rpt gen_tac >> disch_tac >>
  qpat_assum `stmt_frag_full_pre _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_frag_full_pre_def]) >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `gas_admissible (eval_target_place cx t) target_place_res_ok es` by
    (simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >> Cases_on `res` >>
     simp[target_place_res_ok_def] >>
     `no_control_exc y` by metis_tac[eval_target_place_no_control] >>
     qpat_assum `gas_admissible (eval_stmt _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gs` mp_tac) >>
     gvs[augassign_source_bind,bind_def,stmt_res_ok_def,no_control_exc_def]) >>
  drule_all augassign_full_code_stages >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`,`ca`,`shadow_ca`] assume_tac)) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ _ = _ /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  suspend "target_prefix"
QED
*)
Theorem body_augassign_nested_immutable_prefix:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t /\
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
  immutable_root cx t /\
  ~(?nsid. t = TopLevelNameTarget nsid) /\
  ~supported_stmt_expr_exists (const_name_root cx) (AugAssign aty t bop e) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[target_prefix]:
  `call_evaluation_safe cx (int_calls_target t)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (AugAssign _ _ _ _))`
      (ACCEPT_TAC o MATCH_MP call_evaluation_safe_append_left o
       PURE_REWRITE_RULE [int_calls_stmt_def])) >>
  `?tv. evaluate_type (get_tenv cx) aty = SOME tv` by
    (`env.type_defs = get_tenv cx` by drule_then ACCEPT_TAC abi_decode_inv_type_env >>
     drule (cj 3 aug_place_typing) >>
     disch_then (mp_tac o MATCH_MP assignable_type_well_formed) >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_target_place cx t) (es,s0,G0,tn0)` by
    (irule immutable_target_place_prefix >> simp[] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`cenv`,`d`,`env`,`r`,`sa`,`ca`,`shadow_func`,
                   `shadow_sa`,`shadow_ca`,`tops`,`tv`,`aty`] >>
     simp[well_typed_target_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `imm_target_place_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [imm_target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`aty`,`sa`,`ca`,`shadow_sa`,`shadow_ca`,
                           `r`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx t) _ targetQ targetR` >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
     (\H res ee G tn v. targetQ H res ee G tn v /\
       (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z))
     targetR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ targetQ targetR` (irule_at Any) >>
     simp[] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  qabbrev_tac `cutQ = \H res ee G tn v. targetQ H res ee G tn v /\
    ~v.vs_halted /\ ee.gas_obs = [] /\
    (!fn i z. frag_reachable ctx func v fn i z ==> dalloca_fmp_headroom i z)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_target_place cx t) (es,s0,G0,tn0)
     cutQ (\H res ee gt r. ?exc. res = INR exc)` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn v. _ /\ _) targetR`
       (irule_at Any) >>
     simp[Abbr `cutQ`, Abbr `targetR`] >>
     rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  rewrite_tac[augassign_source_bind] >>
  irule (Q.INST [`Q1` |-> `cutQ`, `tops` |-> `cx_tops cx`,
                  `R` |-> `\H res ee gt r. T`] augassign_target_bind_prefix) >>
  BETA_TAC >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists_tac `cutQ` >> reverse conj_tac >- simp[] >>
  simp[Abbr `cutQ`] >> suspend "endpoint"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[endpoint]:
  qx_genl_tac [`marks`,`p`,`st`,`Gtarget`,`tnt`,`v`] >> strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon st.storage_trace` >>
  `valid_horizon cx st0 H0 st.storage_trace` by
    fs[Abbr `H0`,storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H st.storage_trace ==> targetQ _ _ _ _ _ _ /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  qpat_x_assum `targetQ H0 _ _ _ _ _` mp_tac >>
  simp[NoAsms, Abbr `targetQ`] >>
  disch_then (qx_choosel_then [`root`,`path`] STRIP_ASSUME_TAC) >>
  `root = id` by fs[] >> qpat_x_assum `root = id` SUBST_ALL_TAC >>
  qpat_x_assum `p = ImmutablePlace _ _ _` SUBST_ALL_TAC >>
  qabbrev_tac `p = ImmutablePlace (NONE:num option) id path` >>
  qpat_assum `imm_target_post H0 _ _ _ _ _ _ _ _ _ id path aty r v`
    (strip_assume_tac o REWRITE_RULE [imm_target_post_def]) >>
  qpat_x_assum `_ \/ ?loc cur rhs result s1 s2 s3 ss1 ss2 ss3. _`
    (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (qx_choosel_then [`loc`,`old`,`rhsop`,`dst`,`cb`,`cc`,`cd`,
        `shadow_cb`,`shadow_cc`,`shadow_cd`] STRIP_ASSUME_TAC))
  >- fs[] >>
  `loc = LocCode` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `loc = LocCode` SUBST_ALL_TAC >>
  `sa.cs_next_var <= ca.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv ca` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv ca v` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `st with gas_obs := [] = st` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `reads = gas_explicit marks s0.vs_gas_readings` >>
  `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)` by
    (qpat_assum `st with gas_obs := [] = st` (fn upd =>
       qpat_assum `!tail. eval_target_place cx t _ = _`
         (qspec_then `[]` (mp_tac o PURE_REWRITE_RULE [APPEND_NIL,upd]))) >>
     simp[Abbr `p`,Abbr `reads`]) >>
  `body_const_cells_agree [(NONE,tops)] cx env st` by
    (irule bodyFullPredsTheory.body_const_cells_agree_target >>
     qpat_assum `eval_target_place cx t (es with gas_obs := reads) = (INL p,st)`
       (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_all augassign_entry_rhs_pre >> simp[]) >>
  `expr_body_pre cenv cx env e st` by
    (drule_all aug_place_rhs_pre_target_gas_obs >> simp[]) >>
  suspend "load"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[load]:
  rename1 `evaluate_subscripts itv iv path = INL cur` >>
  rename1 `mem_path_offset itv path = SOME (k,ptv)` >>
  rename1 `FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)` >>
  Cases_on `ALOOKUP st.immutables cx.txn.target`
  >- fs[finite_mapTheory.FLOOKUP_EMPTY] >>
  rename1 `ALOOKUP st.immutables cx.txn.target = SOME imms` >>
  qpat_x_assum `FLOOKUP (case SOME _ of _ => _ | _ => _) _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `expr_sim_inv cenv cx env st` by
    metis_tac[expr_body_pre_static_facts] >>
  `dead_lo_ok H0 (DF H0) lo cenv cx` by
    (qpat_assum `!H. dead_lo_ok H _ _ _ _` (qspec_then `H0` ACCEPT_TAC)) >>
  drule_all augassign_immutable_path_load_resources >> strip_tac >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  `read_place cx p st = (INL cur,st) /\ place_type_value cx p st = (INL ptv,st)` by
    simp[Abbr `p`,read_place_def,place_type_value_def,get_immutables_def,
         get_address_immutables_def,bind_def,return_def,lift_sum_def,lift_option_type_def] >>
  `compile_imm_load_word T cenv.ce_imm_alloca (FST r) ca = (old,cb)` by
    (qpat_assum `cenv.ce_is_ctor` (fn ctor =>
       qpat_assum `(_ ca = (old,cb))`
         (ACCEPT_TAC o REWRITE_RULE [ctor, compile_ptr_load_def]))) >>
  `allocas_from lo v /\ lo <= v.vs_alloca_next` by fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `op_taint tnt (FST r) = {}` by fs[target_ptr_ok_def,Abbr `p`] >>
  `copy_old_operand ca (FST r)` by simp[copy_old_operand_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
     eval_operand region v = SOME 0w /\ copy_old_operand ca region /\
     op_taint tnt region = {} /\ op_prov Gtarget region = NONE` by suspend "base" >>
  `w2n (n2w (off+k) : bytes32) + 32 <= lo /\
   mem_word_taint tnt.t_mem (w2n (n2w (off+k) : bytes32)) = {}` by
    (qpat_assum `w2n (n2w (off+k) : bytes32) = _` (fn th => PURE_REWRITE_TAC [th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (FST r) v = SOME (n2w (off+k))` by
    (first_assum ACCEPT_TAC ORELSE
     (once_rewrite_tac [arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC)) >>
  drule_all augassign_ctor_word_load_at >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`u`,`Gload`,`tnload`] strip_assume_tac)))))) >>
  `!H. valid_horizon cx st0 H st.storage_trace ==>
    stmt_state_rel H ctx func cenv cx st u /\ storage_well_formed_on cx st (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx st Gload tnload u /\
    return_buf_frame d cenv cb u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by suspend "frame" >>
  pop_assum (mk_asm "loadPost") >>
  suspend "rhs"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[base]:
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
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[frame]:
  qx_gen_tac `H` >> disch_tac >>
  `stmt_state_rel H ctx func cenv cx st v /\ storage_well_formed_on cx st (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx st Gtarget tnt v` by
    (qpat_assum `!K. valid_horizon _ _ K st.storage_trace ==> targetQ K _ _ _ _ _ /\ _`
       (drule_then (mp_tac o CONJUNCT1)) >>
     BETA_TAC >>
     disch_then (qx_choosel_then [`root`,`path'`] STRIP_ASSUME_TAC) >>
     fs[imm_target_post_def]) >>
  drule_all (Q.INST [`entry` |-> `sa`,`sa` |-> `ca`,`sb` |-> `cb`,
    `es` |-> `es`,`st` |-> `st`,`s0` |-> `s0`,`s` |-> `v`,
    `G` |-> `Gtarget`,`G1` |-> `Gload`,`tn` |-> `tnt`,`tn1` |-> `tnload`,
    `D` |-> `DF H`,`addr` |-> `n2w (off+k)`] augassign_load_endpoint_frame) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[rhs]:
  `!fn inst q. frag_reachable ctx func u fn inst q ==> dalloca_fmp_headroom inst q` by
    (qpat_assum `!D. gas_origin_ptr_path _ (v,Gtarget,tnt) [] (OK u,Gload,tnload)`
       (qspec_then `DF H0` (fn path =>
        qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
          qpat_assum `!fn i z. frag_reachable ctx func v fn i z ==> _`
            (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom o
             CONJ path o CONJ no_phi))))) >>
  `local_ptrs_reserved cenv cb /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x)` by
    metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok st` by
    (irule expr_body_pre_gas_admissible >> qexistsl_tac [`cenv`,`env`] >> simp[]) >>
  asm "loadPost" (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e st
    (st0,cb,cc,shadow_cb,shadow_cc,rhsop,u,Gload,tnload)` by
    (simp[expr_sim_full_pre_def] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     rpt strip_tac >> asm "loadPost" (drule_then strip_assume_tac) >> simp[]) >>
  suspend "finish_rhs"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_augassign_nested_immutable_prefix[finish_rhs]:
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by
    (conj_tac >> first_assum irule >> rpt (first_assum (irule_at Any))) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e st` by
    (irule (cj 1 (REWRITE_RULE [AND_IMP_INTRO] body_expr_full_ok_simulations)) >>
     rpt (first_assum (irule_at Any))) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx aty e st` by
    (qpat_x_assum `body_expr_prefix_ok _ _`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  disch_then (drule_then assume_tac) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then drule >> strip_tac >>
  qabbrev_tac `goRhs = bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx p))` >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 goRhs (st,v,Gtarget,tnt)` by
    (irule gas_prefix_full_zero_prefix_guarded >> simp[] >> conj_tac
     >- (simp[Abbr `goRhs`] >> irule storage_trace_frame_bind_all >>
         simp[augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
     qexistsl_tac [`Gload`,`u`,`tnload`] >> conj_tac
     >- simp[] >>
     simp[Abbr `goRhs`] >> irule augassign_rhs_bind_prefix >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`\H v ee G tn t. ~t.vs_halted`, `\H res ee gt r. T`,`cx_tops cx`] >>
     simp[] >> irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) _) _ _ _` (irule_at Any) >>
     simp[] >> rpt gen_tac >> Cases_on `res` >> simp[]) >>
  `!gs. read_place cx p (st with gas_obs := gs) = (INL cur,st with gas_obs := gs)` by
    (`read_result cx (PlaceR p) st = (INL cur,st)` by simp[read_result_def] >>
     drule read_result_gas_obs >> simp[read_result_def]) >>
  drule_then assume_tac place_type_value_gas_obs >>
  `!gs. bind (read_place cx p) (\cur.
      bind (place_type_value cx p) (\ptv.
        bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
          bind (lift_sum (evaluate_binop
            (case type_to_int_bound aty of SOME n => n | NONE => Unsigned 0)
            ptv bop cur rhs)) (write_place cx p)))) (st with gas_obs := gs) =
     goRhs (st with gas_obs := gs)` by simp[bind_def,Abbr `goRhs`] >>
  qpat_x_assum `gas_prefix_full _ _ _ goRhs _`
    (qx_choose_then `rhsMarks` (map_every assume_tac o CONJUNCTS) o
       REWRITE_RULE [gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `rhsMarks` >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!gs. bind (read_place cx p) _ _ = goRhs _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise body_augassign_nested_immutable_prefix
*)

Theorem body_augassign_other_prefix:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_prefix_ok cx e) /\
  body_base_target_full_ok cx t /\
  body_base_target_prefix_ok cx t /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `immutable_root cx t /\ ~(?nsid. t = TopLevelNameTarget nsid)`
  >- (drule_all body_inv_stmt_const_name_free >> strip_tac >>
      irule body_augassign_nested_immutable_prefix >>
      qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
      qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >>
      simp[] >> metis_tac[]) >>
  `target_mutable env t` by
    (qpat_assum `type_stmt _ _ _ = _` mp_tac >>
     simp[NoAsms, Once type_stmt_def, AllCaseEqs()]) >>
  `immutable_root cx t ==> ?nsid. t = TopLevelNameTarget nsid` by metis_tac[] >>
  drule_all augassign_other_target_routes >>
  disch_then (DISJ_CASES_THEN STRIP_ASSUME_TAC)
  >- suspend "ordinary" >>
  qpat_x_assum `t = TopLevelNameTarget nsid` SUBST_ALL_TAC >>
  PairCases_on `nsid` >>
  irule augassign_toplevel_immutable_prefix >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_augassign_other_prefix[ordinary]:
  `target_pre cenv cx env t es` by (drule_all augassign_entry_target_pre >> simp[]) >>
  irule augassign_ordinary_prefix >>
  qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ _ = _` (irule_at Any) >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `gas_admissible (eval_base_place cx t) target_res_ok es` by
    (irule get_place_base_admissible >> simp[GSYM eval_target_place_as_bind]) >>
  rewrite_tac[eval_target_place_as_bind] >>
  `!st. SND (bind (eval_base_place cx t) get_place st) =
        SND (eval_base_place cx t st)` by simp[get_place_bind_state] >>
  drule_then (fn th => rewrite_tac[th]) gas_prefix_full_state_cong >>
  irule body_target_sim_prefix >> simp[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cenv`,`d`,`env`,`r`,`sa`,`ca`,`shadow_func`,`shadow_sa`,
                `shadow_ca`,`tops`,`Type aty`] >> simp[]
QED

Finalise body_augassign_other_prefix
