(* Linked value-array subscripts with an overlapping index: materialize
   the base before starting the index computation. *)
Theory bodySubscriptArrayCopiedMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodySimModsProps
  exprSimSubscriptArraySource exprSimSubscriptArray exprCallbackContracts
  exprLowering exprLoweringProps vyperAST context compileEnv
  bodyFullShared gasShadowCompileStmtHelpers gasShadowCompileConvert
  gasShadowCompile gasShadowState gasShadow fragExec
  exprBodyPreProps exprBodyPreTypingProps exprSimHypsDefs
  vyperTypeSystem vyperTyping[qualified,ignore_grammar] vyperTypeInvariants
  vyperTypeExprSoundness vyperTypeEvalSoundness vyperPlaceResultTyping
  supportedExprTraverse bodyFullPostsMods bodyFullPredsMods
  exprSimDefs gasContext vyperState list allocLimits vyperTypeCallGraph
  vyperTypeCallStackSoundness exprBodyPreCallSafetyProps bodyWriteSubscriptSourceMods

Theorem copied_array_static[local]:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  subscript_reads_base cx obj idx ==>
  copies_subscript_base cenv obj idx /\ ~array_slot_base cenv obj /\
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
    read_result cx raw mid = (INL saved,mid) ==>
    body_expr_full_ok_mods mods exps cx idx)
Proof
  simp[linked_subscript_array_context_mods_def] >> strip_tac >>
  drule_all body_inv_copies_subscript_base_mods >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule copies_subscript_base_not_array_slot_base >> qexists_tac `idx` >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!s'' res t s3 res' t'. _ ==> _`
    (qspecl_then [`s`,`raw`,`mid`,`mid`,`Value saved`,`mid`] mp_tac) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def]
QED

Theorem copied_array_real_cuts[local]:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  copies_subscript_base ce obj idx ==>
  ?bvv sm cvv sc iop si dst loc.
    compile_expr ce ty obj sa = (bvv,sm) /\
    compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
    lower_value compile_expr ce ty idx sc = (iop,si) /\
    loc = (case vv_location cvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand cvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location ce loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (cj 1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_child_calls, compile_subscript_def,
       comp_bind_def, comp_return_def, expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _`
    (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem copied_array_interval[local]:
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv snapce T bvv sm = (cvv,sc) /\
  lower_value compile_expr ce ty idx sc = (iop,si) /\
  compile_array_subscript bop iop dyn cnt scale bytes signed
    (compile_ptr_load isc alloc loc) si = (dst,sb) /\
  fn_has_code sa sb func ==>
  cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
  fn_has_code sa sm func /\ fn_has_code sm sc func /\
  fn_has_code sc si func /\ fn_has_code si sb func
Proof
  strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends sm sc` by
    (`ci_mono sm sc` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_snapshot_vv _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_compile_snapshot_vv]) >>
  `cs_extends si sb` by
    (`ci_mono si sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load]) >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    (conj_tac >> irule cs_extends_trans >- (qexists_tac `sm` >> simp[]) >>
     qexists_tac `si` >> simp[]) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sc si func /\ fn_has_code si sb func` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

Theorem copied_array_paired_cuts[local]:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  place_type ce obj = ValPT (ArrayT et bd) /\ copies_subscript_base ce obj idx ==>
  ?bvv sm cvv sc iop si dst loc shm shc shi.
    compile_expr ce ty obj sa = (bvv,sm) /\
    compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
    lower_value compile_expr ce ty idx sc = (iop,si) /\
    loc = (case vv_location cvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand cvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location ce loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    compile_snapshot_vv ce T bvv shm = (cvv,shc) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shc = (iop,shi) /\
    gas_shadow_state sm shm /\ gas_shadow_state sc shc /\ gas_shadow_state si shi /\
    cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\
    fn_has_code sc si func /\ fn_has_code si sb func /\
    fn_has_code sha shm shadow_func /\ fn_has_code shm shc shadow_func /\
    fn_has_code shc shi shadow_func /\ fn_has_code shi shb shadow_func
Proof
  strip_tac >> drule_all copied_array_real_cuts >> strip_tac >>
  drule_all_then strip_assume_tac copied_array_interval >>
  `copies_subscript_base (gas_shadow_env T ce) (gas_shadow_expr obj) (gas_shadow_expr idx) /\
   place_type (gas_shadow_env T ce) (gas_shadow_expr obj) = ValPT (ArrayT et bd)` by
    gvs[copies_subscript_base_def] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >>
  drule_all copied_array_real_cuts >> strip_tac >>
  `gas_shadow_compiles (compile_expr ce ty obj)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj))` by
    irule gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  `gas_shadow_compiles (compile_snapshot_vv ce T bvv)
      (compile_snapshot_vv ce T bvv)` by
    simp[gas_shadow_compiles_snapshot_vv] >>
  rename1 `compile_snapshot_vv ce T bvv shm = (sh_cvv,shc)` >>
  `sh_cvv = cvv /\ gas_shadow_state sc shc` by
    (irule gas_shadow_step >>
     qpat_assum `gas_shadow_state sm shm` (irule_at Any) >>
     rpt (first_assum (irule_at Any))) >> gvs[] >>
  `gas_shadow_compiles (lower_value compile_expr ce ty idx)
     (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx))` by
    irule gas_shadow_stmt_lower_value_env >>
  rename1 `lower_value _ _ _ (gas_shadow_expr idx) shc = (sh_iop,shi)` >>
  `sh_iop = iop /\ gas_shadow_state si shi` by
    (irule gas_shadow_step >>
     qpat_assum `gas_shadow_state sc shc` (irule_at Any) >>
     rpt (first_assum (irule_at Any))) >>
  gvs[] >> drule_all_then strip_assume_tac copied_array_interval >>
  rpt (goal_assum (drule_at Any)) >> simp[mk_ptr_def]
QED

Theorem copied_array_base_typed[local]:
  expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd ==>
  well_typed_expr env obj
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def] >>
  strip_tac >> gvs[] >>
  drule type_place_expr_vtype_annotation >> simp[] >>
  Cases_on `vt` >> gvs[vtype_annotation_ok_def] >> strip_tac >> gvs[] >>
  irule type_place_expr_context_value_typed >>
  conj_tac >- (qexists_tac `ArrayT et bd` >> simp[]) >>
  qexists_tac `cx` >> fs[env_consistent_def]
QED

Theorem copied_array_base_pre[local]:
  expr_body_pre_mods mods ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~array_slot_base ce obj ==>
  expr_body_pre_mods mods ce cx env obj es
Proof
  strip_tac >> drule_all_then assume_tac copied_array_base_typed >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_mods_def, byte_widths_expr_def, alloc_limits_expr_def,
       int_calls_expr_def, expr_has_evm_run_thm, EVERY_APPEND,
       Once supported_expr_exists_def] >>
  strip_tac >> simp[] >>
  drule_then assume_tac call_evaluation_safe_append_left >>
  qpat_x_assum `~supported_expr_exists (unallocated_bare_global_root _ _) (Subscript _ _ _)`
    (strip_assume_tac o SIMP_RULE bool_ss [Once supported_expr_exists_def]) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!target. supported_expr_exists _ (Subscript _ _ _) ==> _` irule >>
  simp[Once supported_expr_exists_def]
QED

Theorem copied_array_base_admissible[local]:
  subscript_reads_base cx obj idx /\
  expr_body_pre_mods mods ce cx env obj es /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es ==>
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res`
  >- (rename1 `eval_expr cx obj _ = (INL raw,ee)` >>
      `expr_body_pre_mods mods ce cx env obj (es with gas_obs := gs)` by simp[] >>
      drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
      drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
      qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
      disch_then (qspecl_then [`env`,`es with gas_obs := gs`,`INL raw`,`ee`] mp_tac) >>
      Cases_on `raw` >> fs[runtime_consistent_def, expr_vv_res_ok_def,
                           eval_result_typed_def]) >>
  qpat_assum `subscript_reads_base _ _ _`
    (assume_tac o MATCH_MP eval_expr_subscript_copied_bind) >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[bind_def]
QED

Theorem copied_array_child_sim[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx ce cx /\ module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods ce cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es
Proof
  strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx sh fn sf ce env ty es.
                _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (irule o SPEC_ALL) >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

Theorem copied_array_next_source[local]:
  subscript_reads_base cx obj idx /\
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func ce env ty es et bd /\
  expr_body_pre_mods mods ce cx env obj es /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL saved,mid) ==>
  expr_body_pre_mods mods ce cx env idx mid /\
  body_const_cells_agree_mods mods cx env mid /\
  body_expr_full_ok_mods mods exps cx idx
Proof
  strip_tac >>
  drule_all_then strip_assume_tac copied_array_static >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  `expr_body_pre_mods mods ce cx env obj (es with gas_obs := gs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  `bind (eval_expr cx obj) (read_result cx) (es with gas_obs := gs) = (INL saved,mid)` by
    simp[bind_def] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  conj_tac
  >- (irule exprSimSubscriptMapTheory.expr_subscript_pre_index_mods >>
      simp[] >> qexistsl_tac [`ann`,`es`,`obj`] >> simp[]) >>
  simp[] >>
  qpat_assum `!s raw mid v. _ ==> body_expr_full_ok_mods _ _ _ _` drule_all >> simp[]
QED
