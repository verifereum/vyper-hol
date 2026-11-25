(* Cuts for the copied array arm: base, snapshot, key, selection. *)
Theory entryCreateSubscriptCopied
Ancestors
  bodyFullSubscriptCopiedBind entryCreateFocusSpec s1PrefixDefs
  exprSimSubscriptArraySource exprSimSubscriptArray exprSimHyps
  vyperState vyperInterpreter vyperAST compileEnv fragExec gasShadow
  context exprLowering gasContext exprSimDefs bodyFullIfExpReach
  exprLoweringProps freshWrites fragGasOriginPtr exprSimSource
  vyperStorageFootprint gasShadowState gasExplicitSites bodySim venomInst list
  gasSummary entryCreateCompletedCut exprSimMemorySource bodyPtrAttributeSource
  bodyFullPreds exprBodyPreProps loweringPosts

Theorem copied_subscript_base_site:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
  copies_subscript_base ce obj idx /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Subscript ann obj idx) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  expr_body_pre ce cx env obj es /\
  ?bvv sm cvv sc iop si dst loc shm shc shi.
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
    compile_snapshot_vv ce T bvv shm = (cvv,shc) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shc = (iop,shi) /\
    gas_shadow_state sc shc /\ gas_shadow_state si shi /\
    cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
    cs_extends sha shm /\ cs_extends shm shc /\ cs_extends shc shi /\ cs_extends shi shb /\
    fn_has_code sm sc func /\ fn_has_code sc si func /\ fn_has_code si sb func /\
    fn_has_code shc shi shfunc /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty obj es
      (st0,sa,sm,sha,shm,bvv,s0,G0,tn0)
Proof
  strip_tac >>
  `expr_body_pre ce cx env obj es` by
    metis_tac[expr_body_pre_array_subscript_base,copies_subscript_base_not_array_slot_base] >>
  simp[] >>
  fs[expr_vv_sim_full_pre_def] >> drule_all copied_array_cuts >> strip_tac >>
  `cs_extends sm sb /\ cs_extends sc sb /\
   cs_extends shm shb /\ cs_extends shc shb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc si func /\
   fn_has_code si sb func /\ fn_has_code sha shm shfunc /\ fn_has_code shc shi shfunc` by
    (imp_res_tac fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qexistsl_tac [`bvv`,`sm`,`cvv`,`sc`,`iop`,`si`,`dst`,`shm`,`shc`,`shi`] >>
  gvs[] >> first_assum ACCEPT_TAC
QED

(* The guarded index is ready only at the result of the actual copy. *)
Theorem copied_subscript_index_site:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Subscript ann obj idx) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  lower_value compile_expr ce ty idx sc = (iop,si) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shc = (iop,shi) /\
  gas_shadow_state sc shc /\ gas_shadow_state si shi /\
  fn_has_code sc si func /\ fn_has_code shc shi shfunc /\
  sa.cs_next_var <= sc.cs_next_var /\ local_ptrs_reserved ce sc /\
  return_buf_frame d ce sc u /\ alloca_history func u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ create_operand_at sc u /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (s0,G0,tn0) marks (OK t,G1,tn1) /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (t,G1,tn1) [] (OK u,Gc,tnc) /\
     stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) ==>
  expr_body_pre ce cx env idx mid /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty idx mid
    (st0,sc,si,shc,shi,iop,u,Gc,tnc)
Proof
  strip_tac >>
  `expr_body_pre ce cx env idx mid` by
    (`expr_body_pre ce cx env (Subscript ann obj idx) (es with gas_obs := gs)` by simp[] >>
     drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  fs[expr_vv_sim_full_pre_def,create_operand_at_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi >> disch_then drule >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >> strip_tac >>
  `!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `!fn i z. frag_reachable ctx func u fn i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `gas_origin_ptr_path _ _ [] _`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  simp[expr_sim_full_pre_def] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (drule expr_body_pre_gas_admissible >> simp[]) >>
  rpt strip_tac >> res_tac >> fs[]
QED

(* Do not reconstruct a source read after the index has changed its place. *)
Theorem copied_subscript_source_landing:
  expr_body_pre ce cx env obj es /\ body_const_cells_agree mods cx env es /\
  mid.gas_obs = [] /\
  (!tail. eval_expr cx obj (es with gas_obs := gs ++ tail) =
    (INL raw,mid with gas_obs := tail)) /\
  vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv t ==>
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  body_const_cells_agree mods cx env mid /\
  ?saved. read_result cx raw mid = (INL saved,mid)
Proof
  strip_tac >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` mp_tac) >> pure_rewrite_tac[APPEND_NIL] >>
     asm_rewrite_tac[]) >>
  simp[] >> conj_tac
  >- (`vyperTypeSystem$well_typed_expr env obj` by
        (drule expr_body_pre_static_facts >> simp[]) >>
      `body_const_cells_agree mods cx env (es with gas_obs := gs)` by simp[] >>
      irule body_const_cells_agree_expr >>
      goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  fs[vv_post_def] >> drule attribute_vv_holds_read_operand >> metis_tac[]
QED

Theorem copied_subscript_read_scope:
  read_result cx raw mid = (INL saved,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  create_operand_full_scope sm sc E ctx func t [] (OK u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (t,G,tn) [] (OK u,Gc,tnc) /\
     Q H (INL saved) (mid with gas_obs := []) Gc tnc u) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sm sc
    (read_result cx raw) (mid,t,G,tn) Q R
Proof
  strip_tac >> simp[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL saved`,`mid`,`OK u`,`Gc`,`tnc`] >>
  simp[gas_explicit_def,read_result_gas_obs] >> metis_tac[]
QED
