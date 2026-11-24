(* Linked runtime-code array subscript. *)
Theory bodySubscriptArrayFramedCodeMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyFullPredsMods bodyFullPostsMods
  exprSimHypsDefs exprBodyPreProps exprSimTopLevelProps
  exprSimSubscriptArrayFramed exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState gasShadowCompileBase
  gasShadow gasShadowCompilePure
  supportedExprTraverse allocLimits vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperTypeInvariants exprSimSubscriptArraySource
  fragExec compileEnv list

Theorem framed_code_subscript_base_pre[local]:
  expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode ==>
  expr_body_pre_mods mods ce cx env obj es
Proof
  strip_tac >>
  `~array_slot_base ce obj` by metis_tac[array_slot_base_compile_location] >>
  `well_typed_expr env obj` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_then assume_tac expr_body_pre_mods_inv >> drule expr_sim_inv_mods_env >>
     simp[env_consistent_def] >> strip_tac >>
     qpat_x_assum `well_typed_expr _ (Subscript _ _ _)` mp_tac >>
     simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >>
     drule type_place_expr_vtype_annotation >> simp[] >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def] >> strip_tac >> gvs[] >>
     irule type_place_expr_context_value_typed >>
     conj_tac
     >- (qexists_tac `ArrayT et bd` >> simp[]) >>
     qexists_tac `cx` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, byte_widths_expr_def, alloc_limits_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm, supported_expr_exists_def, EVERY_APPEND] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem framed_code_selector_extends[local]:
  compile_array_subscript bop iop dyn n ws esz signed_idx
    (compile_ptr_load ctor imm loc) st = (dst,sb) ==>
  cs_extends st sb
Proof
  strip_tac >>
  `ci_mono st sb` suffices_by simp[ci_mono_def] >>
  pop_assum (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
  irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]
QED

Theorem framed_code_subscript_base_shadow[local]:
  gas_shadow_state sa sha /\ compile_expr ce ty obj sa = (bvv,sm) ==>
  ?shm. compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
        gas_shadow_state sm shm
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_expr ce ty obj)
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj))` by
    irule gas_shadow_stmt_compile_expr_env >>
  pop_assum (qspecl_then [`sa`, `sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha` >> simp[]
QED

Theorem framed_code_subscript_index_shadow[local]:
  gas_shadow_state sm shm /\ lower_value compile_expr ce ty idx sm = (iop,sn) ==>
  ?shn. lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm = (iop,shn) /\
        gas_shadow_state sn shn
Proof
  strip_tac >>
  `gas_shadow_compiles (lower_value compile_expr ce ty idx)
    (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx))` by
    irule gas_shadow_stmt_lower_value_env >>
  pop_assum (qspecl_then [`sm`, `shm`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm` >> simp[]
QED

Theorem framed_code_subscript_cuts[local]:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc /\
  place_type ce obj = ValPT (ArrayT et bd) /\ ~copies_subscript_base ce obj idx /\
  (!ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode) ==>
  ?bvv iop dst sm sn shm shn.
    compile_expr ce ty obj sa = (bvv,sm) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    lower_value compile_expr ce ty idx sm = (iop,sn) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm = (iop,shn) /\
    vv_location bvv = SOME LocCode /\ vv = LocatedValue ann (mk_ptr dst LocCode) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale LocCode) (elem_size_in_location ce LocCode et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode) sn = (dst,sb) /\
    gas_shadow_state sm shm /\ gas_shadow_state sn shn /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    fn_has_code sha shm shfunc /\ fn_has_code shm shn shfunc
Proof
  strip_tac >> drule_all_then strip_assume_tac compile_expr_array_subscript >>
  rename1 `compile_expr ce ty obj sa = (bvv,sm)` >>
  rename1 `lower_value compile_expr ce ty idx sm = (iop,sn)` >>
  `vv_location bvv = SOME LocCode` by
    (qpat_assum `!ty st. vv_location _ = _` (qspecl_then [`ty`,`sa`] mp_tac) >>
     qpat_assum `compile_expr ce ty obj sa = _` (fn th => simp[NoAsms, th])) >>
  gvs[] >>
  drule_all_then (qx_choose_then `shm` strip_assume_tac) framed_code_subscript_base_shadow >>
  drule_all_then (qx_choose_then `shn` strip_assume_tac) framed_code_subscript_index_shadow >>
  `cs_extends shn shb` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     drule compile_expr_array_subscript >> disch_then (qspecl_then [`et`,`bd`] mp_tac) >>
     impl_tac >- fs[exprLoweringTheory.copies_subscript_base_def] >>
     strip_tac >> gvs[] >> drule framed_code_selector_extends >> simp[]) >>
  qpat_assum `compile_expr ce ty obj sa = _` (strip_assume_tac o MATCH_MP (cj 1 compile_expr_grows)) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr obj) sha = _`
    (strip_assume_tac o MATCH_MP (cj 1 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ idx sm = _` (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr idx) shm = _`
    (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
  drule_then assume_tac framed_code_selector_extends >>
  `cs_extends sm sb /\ cs_extends shm shb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sha shm shfunc /\ fn_has_code shm shb shfunc` by
    (qspecl_then [`sha`,`shm`,`shb`,`shfunc`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (qspecl_then [`sm`,`sn`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code shm shn shfunc` by
    (qspecl_then [`shm`,`shn`,`shb`,`shfunc`] mp_tac fn_has_code_split >> simp[]) >>
  qexistsl_tac [`shm`,`shn`] >> simp[]
QED
