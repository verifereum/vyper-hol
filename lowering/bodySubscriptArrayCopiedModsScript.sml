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
  bodyCopiedArrayBindMods bodyCopiedArrayForcedAllocMods
  bodyCopiedArrayIdentityEntryMods bodyCopiedArraySlotEntryMods bodyCopiedArrayCodeEntryMods
  bodyCopiedArraySnapshotStoreMods bodyCopiedArrayIndexFrameMods
  bodyCopiedArrayFixedSelectMods bodyCopiedArrayDynamicSelectMods bodyCopiedArrayReadMods
  bodyCopiedArrayCutDefsMods bodyFullIfExpReach gasOutcomeFullPostMods
  exprPtrUnwrapMarked gasExplicitSites arithmeticProps valueEncoding words integer
  bodyAssignNameLinkedSetup vyperTypeConstantFold vyperTypeEvalCaseProofs
  vyperStorageTrace vyperStorageFootprint vyperExprNoControl
  bodySimStmtFacts vyperValue loweringPosts exprSimArith exprReasonOperand exprOperandVar

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
  expr_body_pre_mods mods ce cx env obj es ==>
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  `expr_body_pre_mods mods ce cx env obj (es with gas_obs := gs)` by simp[] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ _ es` kall_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  qspecl_then [`cx`,`obj`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
  disch_then (qspecl_then [`env`,`es with gas_obs := gs`,`res`,`ee`] mp_tac) >>
  fs[runtime_consistent_def] >> strip_tac >>
  Cases_on `res` >> gvs[expr_vv_res_ok_def]
  >- (rename1 `eval_result_typed _ raw _` >> Cases_on `raw` >> gvs[eval_result_typed_def]) >>
  drule (cj 1 eval_expr_no_control) >> rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
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

Theorem copied_array_store_entry[local]:
  copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (q,w) /\
  ci_mono sa sm /\ ci_mono sm k ==>
  ?t Gl tl sw. copied_store_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
    (sm,s,G,tn) (l,t,Gl,tl) (src,sw,sc,cvv) (q,w)
Proof
  strip_tac >> Cases_on `bvv`
  >- (drule copied_array_identity_store_entry_mods >> simp[] >>
      disch_then (qx_choose_then `sw` assume_tac) >>
      qexistsl_tac [`a`,`Ga`,`ta`,`sw`] >> simp[]) >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule copied_array_identity_store_entry_mods >> simp[vv_location_def] >>
      disch_then (qx_choose_then `sw` assume_tac) >>
      qexistsl_tac [`a`,`Ga`,`ta`,`sw`] >> simp[]) >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (irule copied_array_slot_store_entry_mods >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (irule copied_array_code_store_entry_mods >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `p.ptr_location = LocCalldata` by (Cases_on `p.ptr_location` >> fs[]) >>
  qhdtm_assum `copied_alloc_cut_mods`
    (strip_assume_tac o REWRITE_RULE [copied_alloc_cut_mods_def]) >>
  qhdtm_assum `copied_parent_frame_mods`
    (strip_assume_tac o REWRITE_RULE [copied_parent_frame_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  asm_simp_tac (srw_ss()) [vv_holds_mods_def, loweringPostsTheory.vv_holds_def]
QED

Theorem copied_array_forget_location[local]:
  copied_located_vv_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (ann,obj,idx) es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (Subscript ann obj idx) es
Proof
  rewrite_tac[copied_located_vv_mods_def, expr_vv_sim_full_mods_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_mods_post_source >>
  first_assum (irule_at Any) >>
  simp[copied_located_post_mods_def, copied_vv_exit_mods_def, mk_ptr_def, vv_location_def, vv_operand_def] >>
  rpt strip_tac >> gvs[vv_location_def, vv_operand_def]
QED

Theorem subscript_array_copied_full_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shctx fn shfn ce env ty es et bd /\
  subscript_reads_base cx obj idx ==>
  expr_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (Subscript ann obj idx) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (Subscript ann obj idx) es
Proof
  strip_tac >>
  drule_all_then strip_assume_tac copied_array_static >>
  qhdtm_assum `linked_subscript_array_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_subscript_array_context_mods_def]) >>
  drule_all_then assume_tac copied_array_base_pre >>
  `copied_located_vv_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx ty (ann,obj,idx) es` by
    (irule (Q.INST [`et` |-> `et`,`bd` |-> `bd`] copied_array_children_bind_mods) >>
     conj_tac
     >- (rpt strip_tac >> drule_all_then strip_assume_tac copied_array_next_source >>
         drule_all copied_array_child_sim >> simp[]) >>
     conj_tac
     >- (qexistsl_tac [`bd`,`et`] >> simp[] >> rpt gen_tac >> strip_tac >>
         drule_all_then strip_assume_tac copied_array_paired_cuts >>
         `ci_mono sa sm /\ ci_mono sm sc` by
           (conj_tac
            >- (qpat_assum `compile_expr _ _ obj sa = _`
                  (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
                simp[compile_expr_ci_mono]) >>
            qpat_assum `compile_snapshot_vv _ _ _ sm = _`
              (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
            simp[ci_mono_compile_snapshot_vv]) >>
         `sa.cs_next_var <= sc.cs_next_var` by
           (fs[ci_mono_def] >> decide_tac) >>
         qexistsl_tac [`bvv`,`sm`,`shm`,`cvv`,`sc`,`shc`,`iop`,`si`,`shi`] >>
         asm_rewrite_tac[] >> conj_tac >- suspend "snapshot" >> suspend "select") >>
     conj_tac
     >- (rpt strip_tac >> irule body_inv_no_phi_mods >>
         rpt (goal_assum (drule_at Any)) >> simp[]) >>
     drule_then assume_tac copied_array_base_admissible >>
     drule_all_then strip_assume_tac copied_array_child_sim >> simp[]) >>
  conj_tac
  >- (irule copied_array_read_located_mods >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule copied_array_forget_location >> simp[]
QED

Resume subscript_array_copied_full_mods[snapshot]:
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      vv_post_mods H ctx fn ce cx obj es sa sm s0 mid raw bvv s /\
      ghost_inv_at_mods (DF H) lo d ce cx mid G tn s` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       drule >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx fn ce cx es s0` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> valid_horizon _ _ H es.storage_trace`
       (drule_then assume_tac) >>
     qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _` drule >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ vv_store_bound _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `?atv buf k src l p w a Ga ta run.
    compile_alloc_buffer (type_memory_size atv) sm = (buf,k) /\
    buf.buf_operand = Var p /\ buf.buf_size = type_memory_size atv /\
    fn_has_code sm k fn /\ run_inst_seq (emitted_insts sm k) s = OK run /\
    a = run with vs_inst_idx := LENGTH k.cs_current_insts /\
    copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
      (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (p,w)` by
    (irule copied_array_forced_alloc_mods >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM] >>
     conj_tac >- (qexists_tac `xs` >> asm_rewrite_tac[]) >>
     conj_tac >- (qexists_tac `ty` >> asm_rewrite_tac[]) >>
     reverse conj_tac >- (qexistsl_tac [`env`,`mods`] >> asm_rewrite_tac[]) >>
     strip_tac >>
     qpat_assum `_ ==> ?v. read_result _ _ _ = _ /\ _` mp_tac >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (qx_choose_then `val` strip_assume_tac) >>
     gvs[arithmeticTheory.ADD_COMM]) >>
  `ci_mono sm k` by
    (qpat_assum `compile_alloc_buffer _ sm = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_compile_alloc_buffer]) >>
  drule_all_then strip_assume_tac copied_array_store_entry >>
  `ci_mono k l` by
    (qhdtm_assum `copied_alloc_cut_mods`
       (strip_assume_tac o REWRITE_RULE [copied_alloc_cut_mods_def]) >>
     qpat_assum `unwrap_value _ _ k = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_unwrap_value]) >>
  `sm.cs_next_var <= l.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  qhdtm_assum `copied_store_cut_mods` (mp_then Any mp_tac copied_array_finish_snapshot_mods) >>
  (impl_tac >- fs[ci_mono_def]) >>
  strip_tac >> rpt (goal_assum (drule_at Any))
QED

Theorem copied_array_index_word[local]:
  is_int_type (expr_type idx) /\
  evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key /\
  expr_post_mods H ctx fn ce cx idx mid sc si u fin key iop z ==>
  ?i iw. key = IntV i /\ eval_operand iop z = SOME iw /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  Cases_on `expr_type idx` >> gvs[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_int_type_def,evaluate_type_def,vyperTypingTheory.value_has_type_def,well_formed_type_def] >>
  Cases_on `key` >> gvs[vyperTypingTheory.value_has_type_def] >>
  fs[expr_post_mods_def,expr_post_def,expr_val_rel_def,evaluate_type_def,
     AllCaseEqs(),is_word_type_def,typed_val_to_w256_def,val_to_w256_def] >>
  mp_tac math_val_i2w >>
  disch_then (qspec_then `expr_type idx` (qspec_then `i` mp_tac)) >>
  gvs[math_val_def,is_signed_type_def,type_bits_def,within_int_bound_def]
QED

Resume subscript_array_copied_full_mods[select]:
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  qhdtm_assum `copied_saved_cut_mods`
    (strip_assume_tac o REWRITE_RULE [copied_saved_cut_mods_def]) >>
  `loc = LocMemory /\ vv_operand cvv = Var q` by
    fs[vv_location_def,vv_operand_def,mk_ptr_def] >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_post_mods H ctx fn ce cx idx mid sc si u fin key iop z /\
    ghost_inv_at_mods (DF H) lo d ce cx fin Gi ti z /\
    ptr_val_ok cx (post_value_type ce idx) key iop Gi ti z /\
    z.vs_current_bb = si.cs_current_bb /\ z.vs_inst_idx = LENGTH si.cs_current_insts /\
    alloca_history fn z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    u.vs_alloca_next <= z.vs_alloca_next /\ ghost_kept_at lo ce mid sc Gc tc u Gi ti` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       drule >> simp[]) >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  qpat_x_assum `vv_operand cvv = Var q` (SUBST_ALL_TAC) >>
  `vv = LocatedValue ann (mk_ptr dst LocMemory)` by first_assum ACCEPT_TAC >>
  drule_all_then assume_tac copied_array_hold_index_mods >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ (Subscript _ _ _) _`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     qpat_assum `expr_body_pre_mods _ _ _ _ obj es`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     drule_all constant_subscript_type_ok >> simp[subscript_type_ok_def]) >>
  `is_word_type (post_value_type ce idx)` by
    (`!t. is_int_type t ==> is_word_type t` by
       (Cases >> simp[is_int_type_def] >>
        rename1 `is_int_type (BaseT bt) ==> _` >> Cases_on `bt` >>
        simp[is_int_type_def,is_word_type_def]) >> simp[]) >>
  qhdtm_assum `copied_array_type_mods`
    (strip_assume_tac o REWRITE_RULE [copied_array_type_mods_def]) >>
  drule_all_then strip_assume_tac copied_array_next_source >>
  `expr_body_pre_mods mods ce cx env idx (mid with gas_obs := ys)` by simp[] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type idx) = SOME tv /\ value_has_type tv key` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ idx (mid with gas_obs := ys)`
       (mp_then Any assume_tac expr_body_pre_mods_inv) >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
     fs[value_runtime_typed_def] >> qexists_tac `tv` >>
     qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then (qx_choosel_then [`i`,`iw`] strip_assume_tac) copied_array_index_word >>
  qpat_assum `evaluate_type _ (ArrayT et bd) = SOME _`
    (mp_then Any (qx_choose_then `etv` strip_assume_tac)
       vyperTypeValuesTheory.evaluate_type_ArrayT_cases) >>
  `type_memory_bytes ce et = type_memory_size etv` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ obj es`
       (mp_then Any assume_tac expr_body_pre_mods_inv) >>
     drule_all assign_name_memory_bytes_mods >> simp[]) >>
  suspend "select_run"
QED

Resume subscript_array_copied_full_mods[select_run]:
  `ci_mono sc si` by
    (qpat_assum `lower_value compile_expr ce ty idx sc = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_lower_value_compile_expr]) >>
  `sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!x. iop = Var x ==> not_fresh_at si x` by
    (`local_ptrs_reserved ce sc` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `lower_value compile_expr ce ty idx sc = _`
       (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
  `!l. iop <> Label l` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ idx mid`
       (mp_then Any assume_tac expr_body_pre_mods_well_typed) >>
     qpat_assum `expr_body_pre_mods _ _ _ _ idx mid`
       (mp_then Any (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def])
          expr_body_pre_mods_inv) >>
     drule_all lower_compile_expr_not_label >> simp[]) >>
  `vv = LocatedValue ann (mk_ptr dst
      (case vv_location cvv of NONE => LocMemory | SOME l => l))` by
    simp[vv_location_def,mk_ptr_def] >>
  qpat_assum `vv = LocatedValue _ (mk_ptr _ (case _ of NONE => _ | SOME _ => _))`
    (SUBST1_TAC o SYM) >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  Cases_on `bd`
  >- (irule copied_array_fixed_select_mods >>
      qhdtm_assum `copied_select_cut_mods` (irule_at Any) >> simp[]) >>
  irule copied_array_dynamic_select_mods >>
  qhdtm_assum `copied_select_cut_mods` (irule_at Any) >> simp[]
QED

Finalise subscript_array_copied_full_mods
