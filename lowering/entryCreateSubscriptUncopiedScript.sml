(* The no-copy compiler has one caller cut after each evaluated child. *)
Theory entryCreateSubscriptUncopied
Ancestors
  exprSimSubscriptArrayFramed exprSimSubscriptArraySource
  exprSimUnwrap exprLoweringProps compileEnv fragExec
  gasShadowCompileStmtHelpers gasShadowCompileBase gasShadowCompilePure
  gasShadowState gasShadow vyperInterpreter vyperAST
  s1PrefixDefs entryCreateFocusSpec bodyFullIfExpReach bodyFullPreds
  bodyMemoryDefs freshWrites loweringPosts exprSimSource
  fragGasOriginPtr gasStorage vyperStorageFootprint vyperStorageTrace
  exprSimFullBundleProps vyperState

Theorem subscript_nocopy_shadow_landing[local]:
  gas_shadow_state s sh /\ f s = (v,t) /\ gas_shadow_compiles f g ==>
  ?th. g sh = (v,th) /\ gas_shadow_state t th
Proof
  strip_tac >> Cases_on `g sh` >> fs[gas_shadow_compiles_def] >>
  first_x_assum (qspecl_then [`s`, `sh`] mp_tac) >> simp[]
QED

Theorem subscript_nocopy_selected_layout:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\
  place_type ce obj = ValPT (ArrayT et bd) /\ ~copies_subscript_base ce obj idx /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc ==>
  ?bvv sm shm iop sn shn dst loc.
    compile_expr ce ty obj sa = (bvv,sm) /\
    lower_value compile_expr ce ty idx sm = (iop,sn) /\
    loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand bvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location ce loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) sn = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm = (iop,shn) /\
    gas_shadow_state sm shm /\ gas_shadow_state sn shn /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    cs_extends sha shm /\ cs_extends shm shn /\ cs_extends shn shb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    fn_has_code sha shm shfunc /\ fn_has_code shm shn shfunc /\ fn_has_code shn shb shfunc
Proof
  strip_tac >> drule_all compile_expr_array_subscript >> strip_tac >>
  `?shm. compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
         gas_shadow_state st1 shm` by
    (irule subscript_nocopy_shadow_landing >> first_assum (irule_at Any) >>
     simp[gas_shadow_stmt_compile_expr_env]) >>
  `?shn. lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm = (iop,shn) /\
         gas_shadow_state st2 shn` by
    (irule subscript_nocopy_shadow_landing >> first_assum (irule_at Any) >>
     qexists_tac `lower_value compile_expr ce ty idx` >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `cs_extends st2 sb /\ cs_extends shn shb` by
    (conj_tac
     >- (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
         qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
           (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
         simp[ci_mono_compile_array_subscript,ci_mono_compile_ptr_load]) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,NoAsms] >> strip_tac >>
     drule compile_expr_array_subscript >> simp[] >>
     impl_tac >- fs[exprLoweringTheory.copies_subscript_base_def] >>
     strip_tac >> gvs[] >>
     `ci_mono shn shb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ shn = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[ci_mono_compile_array_subscript,ci_mono_compile_ptr_load]) >>
  `cs_extends sa st1 /\ cs_extends st1 st2 /\ cs_extends sha shm /\ cs_extends shm shn` by
    metis_tac[compile_expr_extends,cj 2 compile_expr_grows] >>
  qexistsl_tac [`bvv`,`st1`,`shm`,`iop`,`st2`,`shn`,`dst`,`loc`] >> simp[] >>
  metis_tac[fn_has_code_split,cs_extends_trans]
QED

(* The index is enabled by a normal base result at its selected cursor. *)
Theorem subscript_nocopy_index_ready:
  body_inv tops ctx ce cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty obj es (st0,sa,sm,sha,shm,bvv,s0,G0,tn0) /\
  lower_value compile_expr ce ty idx sm = (iop,sn) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shm = (iop,shn) /\
  gas_shadow_state sn shn /\ fn_has_code sm sn func /\ fn_has_code shm shn shfunc /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  ~s.vs_halted /\ create_operand_at sm s /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     create_operand_vv_post (DF,lo,d,ctx,func) ce cx obj
       (es,sa,sm,s0,bvv,G0,tn0) H (INL raw) mid G1 tn1 s /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
  expr_body_pre ce cx env idx mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty idx mid (st0,sm,sn,shm,shn,iop,s,G1,tn1)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  `expr_body_pre ce cx env (Subscript ann obj idx) (es with gas_obs := gs)` by simp[] >>
  `expr_body_pre ce cx env idx mid` by
    metis_tac[expr_body_pre_array_subscript_index_after_base] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env obj` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  fs[expr_vv_sim_full_pre_def,create_operand_at_def] >>
  qpat_assum `compile_expr ce ty obj sa = _`
    (mp_then Any strip_assume_tac compile_expr_extends) >>
  `return_buf_frame d ce sm s /\ alloca_history func s /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    (fs[create_operand_vv_post_def] >> irule return_buf_frame_frame >>
     qexistsl_tac [`ce`,`s0`,`sa`] >> fs[vv_post_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst v. frag_reachable ctx func s fn inst v ==> dalloca_fmp_headroom inst v` by
    metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  simp[expr_sim_full_pre_def] >> rpt conj_tac
  >~ [`local_ptrs_reserved _ _`] >- metis_tac[local_ptrs_reserved_next_var]
  >~ [`not_fresh_at _ _`] >- metis_tac[not_fresh_at_mono]
  >~ [`not_fresh_at _ _`] >- metis_tac[not_fresh_at_mono]
  >~ [`gas_admissible _ _ _`] >- metis_tac[expr_body_pre_gas_admissible] >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
  fs[create_operand_vv_post_def,vv_post_def]
QED

(* Track the same initial state and ghosts while shortening the entry interval. *)
Theorem subscript_nocopy_base_ready:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty (Subscript ann obj idx) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
  gas_shadow_state sm shm /\ fn_has_code sa sm func /\ fn_has_code sha shm shfunc ==>
  (~array_slot_base ce obj ==> expr_body_pre ce cx env obj es) /\
  (array_slot_base ce obj ==> ~const_name_root cx obj /\
    well_typed_expr env obj /\ expr_sim_inv ce cx env es) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty obj es (st0,sa,sm,sha,shm,bvv,s0,G0,tn0)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_admissible >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  conj_tac >- metis_tac[expr_body_pre_array_subscript_base] >>
  conj_tac >- metis_tac[expr_body_pre_array_subscript_slot_base] >>
  fs[expr_vv_sim_full_pre_def] >> metis_tac[]
QED

Theorem subscript_nocopy_base_not_map:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) ==>
  ~(?tr slot kt vt. raw = HashMapRef tr slot kt vt)
Proof
  strip_tac >>
  `expr_body_pre ce cx env (Subscript ann obj idx) (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  `expr_sim_inv ce cx env (es with gas_obs := gs)` by simp[] >>
  drule_all expr_sim_inv_eval_result >>
  strip_tac >> Cases_on `raw` >> gvs[vyperTypeInvariantsTheory.eval_result_typed_def]
QED

(* At selection, a single final horizon restricts to both already evaluated
   children. This does not pick new execution or ghost witnesses. *)
Theorem subscript_nocopy_horizons:
  eval_expr cx obj (es with gas_obs := gs1) = (INL raw,mid) /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,func) ce cx obj
      (es,sa,sm,s0,bvv,G0,tn0) H (INL raw) mid G1 tn1 s) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    expr_sim_full_post (DF,lo,d,ctx,func) ce cx idx
      (mid,sm,sn,s,iop,G1,tn1) H (INL key) fin Gi tni it) ==>
  !H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0 /\
    vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
    ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s /\
    expr_post H ctx func ce cx idx mid sm sn s fin key iop it /\
    ghost_inv_at (DF H) lo d ce cx fin Gi tni it
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `storage_trace_frame (bind (eval_expr cx idx) (read_result cx))` by
    simp[storage_trace_frame_bind_all,cj 5 evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `storage_trace_frame (eval_expr cx obj)` by simp[cj 5 evaluate_storage_trace_frame] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  qpat_assum `!h. valid_horizon _ _ h es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!h. valid_horizon _ _ h fin.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  fs[create_operand_vv_post_def,expr_sim_full_post_def]
QED
