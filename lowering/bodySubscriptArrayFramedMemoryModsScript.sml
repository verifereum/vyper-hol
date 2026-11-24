(* Linked execution of the fixed, read-only memory selector. *)
Theory bodySubscriptArrayFramedMemoryMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyFullPredsMods exprBodyPreProps
  exprSimSubscriptArraySource exprSimTopLevelProps supportedExprTraverse
  exprSimHypsDefs allocLimits vyperTypeSystem vyperTypeInvariants
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST pair list
  exprSimSubscriptArrayFramed exprLoweringProps gasShadowCompileStmtHelpers
  context compileEnv compilerInstructionSuffix exprSimUnwrap

Theorem framed_memory_base_pre[local]:
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocMemory ==>
  expr_body_pre_mods mods cenv cx env obj es
Proof
  strip_tac >>
  `~array_slot_base cenv obj` by metis_tac[array_slot_base_compile_location] >>
  `well_typed_expr env obj` by
    (`env_context_consistent env cx` by
       (drule_then assume_tac expr_body_pre_mods_inv >>
        drule_then mp_tac expr_sim_inv_mods_env >> simp[env_consistent_def]) >>
     drule_then mp_tac expr_body_pre_mods_well_typed >>
     simp[Once well_typed_expr_def] >> strip_tac >>
     drule type_place_expr_vtype_annotation >> simp[] >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def] >>
     strip_tac >> gvs[] >>
     irule type_place_expr_context_value_typed >>
     conj_tac >- (qexists_tac `ArrayT et bd` >> simp[]) >>
     qexists_tac `cx` >> simp[]) >>
  gvs[expr_body_pre_mods_def, alloc_limits_expr_def, byte_widths_expr_def, int_calls_expr_def,
      expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem framed_memory_cuts[local]:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = ValPT (ArrayT et (vyperAST$Fixed n)) /\
  ~copies_subscript_base cenv obj idx /\
  (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory) ==>
  ?bvv sm iop si dst.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    lower_value compile_expr cenv ty idx sm = (iop,si) /\
    vv_location bvv = SOME LocMemory /\
    compile_array_subscript (vv_operand bvv) iop F n (word_scale LocMemory)
      (elem_size_in_location cenv LocMemory et) (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst LocMemory) /\
    cs_extends sa sm /\ cs_extends sm si /\ cs_extends si sb
Proof
  strip_tac >> drule_all_then strip_assume_tac compile_expr_array_subscript >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `vv_location bvv = SOME LocMemory` by
    (qpat_assum `compile_expr cenv ty obj sa = (bvv,sm)` (fn cut =>
       qpat_assum `!ty st. vv_location _ = _`
         (qspecl_then [`ty`,`sa`] (ACCEPT_TAC o PURE_REWRITE_RULE [cut,SND,FST])))) >>
  gvs[] >>
  conj_tac >- (drule compile_expr_extends >> simp[]) >>
  conj_tac >- (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [FST,SND] o Q.AP_TERM `SND`) >>
  irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]
QED
