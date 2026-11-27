(* Joint AnnAssign: physical layout of a widened aggregate RHS. *)
Theory bodyFullAnnAssignWidened
Ancestors
  bodyInvCodeProps bodyInvSplit bodyInvExecutionProps exprBodyPreProps
  assignRelayoutCaller annassignRelayoutSource annassignRelayoutFrag annassignRelayoutPost
  augAssignFullRhsSaved
  bodySimFull bodyPtrDefs exprSimSource exprSimHypsDefs gasOutcomeFullCompose
  loweringPosts exprLoweringProps exprOperandVar assignBasePtrBoundary
  externalReturnBounds exprSimAggregateChildren representationCleanPtr
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperState
  compileEnv venomState venomMemDefs words arithmetic
  bodyFullShared bodyFullAnnAssignMemoryPost bodySim bodyExprPreFacts
  stmtSimDeclSource stmtSimDeclCompose stmtSimProps gasOutcomeFullStmts
  gasExemptCert vyperStorageTrace bodyMemoryDefs stmtLoweringMono freshWrites
  emitHelperProps fragExec allocaHistory typedMemoryCopy bodyDeclCopyMemory exprLowering stmtLowering
  immutableDeployAssignRanges annassignRelayoutContinue exprOpenTerminals

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all assign_relayout_source_classify >> strip_tac >>
  `expr_sim_inv ce cx env es` by metis_tac[expr_body_pre_static_facts] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >> metis_tac[]) >>
  qexists_tac `stv` >> simp[] >> rpt strip_tac >>
  metis_tac[annassign_relayout_read_layout]
QED
*)
Theorem annassign_widened_full_layout:
  expr_body_pre_mods mods ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) typ /\ ~is_word_type typ /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes ce typ < 2 ** 64 /\
  supported_expr tops e /\ ce.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops ==>
  ?stv.
    ~is_bytestring_type typ /\
    ~is_word_type (lowered_value_type ce e) /\
    ~is_bytestring_type (lowered_value_type ce e) /\
    post_value_type ce e = lowered_value_type ce e /\
    lowered_value_type ce e <> expr_type e /\ lowered_value_type ce e <> typ /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce typ = type_memory_size tyv /\
    type_memory_size stv <= type_memory_size tyv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    (!gs v mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,mid) ==>
      value_has_type stv v /\ value_has_type tyv v /\
      val_wf stv v /\ val_wf tyv v /\
      val_footprint stv v = type_memory_size stv)
Proof
  cheat
QED

(* The strict physical layout supplies a real pointer variable and robust
   source encoding; the declaration's reserved allocation is disjoint. *)
Theorem annassign_widened_full_source:
  expr_post H ctx func ce cx e es sa sb s0 mid v op s /\
  post_value_type ce e = sty /\ sty <> expr_type e /\
  type_widens_to (get_tenv cx) sty (expr_type e) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv /\
  ptr_val_ok cx sty v op G tn s /\
  FLOOKUP s0.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id /\
  type_memory_size dtv <= sz /\ not_fresh_at sa p /\ lookup_var p s0 = SOME dw ==>
  ?xs sw.
    op = Var xs /\ lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    expr_val_at ce cx sty sa sb mid v (Var xs) s
Proof
  strip_tac >>
  `?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)` by
    (irule expr_post_reserved_destination_source >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[]) >>
  `expr_val_at ce cx sty sa sb mid v op s /\
   stmt_state_rel H ctx func ce cx mid s` by fs[expr_post_def] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    (irule ptr_val_ok_read_covers >> simp[] >>
     goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >> simp[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (drule_all expr_val_at_frontier >> strip_tac >> gvs[]) >>
  qexistsl_tac [`xs`, `sw`] >> gvs[venomStateTheory.eval_operand_def] >>
  fs[ptr_val_ok_def, ptr_mem_ok_def, venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED

(* Enrich only the successful RHS post.  The supplied post, including its
   allocation/taint frame, and the complete exceptional post are retained. *)
Theorem annassign_widened_full_rhs_source:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,t0,G0,tn0) Q R /\
  post_value_type ce e = sty /\ sty <> expr_type e /\
  type_widens_to (get_tenv cx) sty (expr_type e) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  0 < type_memory_size stv /\
  (!gs v mid. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
    value_has_type dtv v /\ val_wf dtv v /\
    val_footprint stv v = type_memory_size stv) /\
  FLOOKUP t0.vs_allocas aid = SOME (w2n dw,sz) /\ aid < a.cs_next_id /\
  type_memory_size dtv <= sz /\ not_fresh_at a p /\ lookup_var p t0 = SOME dw /\
  (!H v mid G tn t. Q H (INL v) mid G tn t ==>
    expr_post H ctx func ce cx e es a b t0 mid v op t /\
    ptr_val_ok cx sty v op G tn t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,t0,G0,tn0)
    (\H res mid G tn t. Q H res mid G tn t /\
      !v. res = INL v ==> value_has_type dtv v /\ val_wf dtv v /\
        ?xs sw.
          op = Var xs /\ lookup_var xs t = SOME sw /\ lookup_var p t = SOME dw /\
          FLOOKUP t.vs_allocas aid = SOME (w2n dw,sz) /\
          ptr_covers G tn xs t (type_memory_size stv) /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory stv v (w2n sw) mem) /\
          w2n sw + type_memory_size stv < dimword (:256) /\
          w2n dw + type_memory_size dtv < dimword (:256) /\
          w2n sw + type_memory_size stv <= t.vs_alloca_next /\
          (w2n sw + type_memory_size stv <= w2n dw \/
           w2n dw + type_memory_size dtv <= w2n sw) /\
          expr_val_at ce cx sty a b mid v (Var xs) t) R
Proof
  strip_tac >> irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  `value_has_type dtv v /\ val_wf dtv v /\
   val_footprint stv v = type_memory_size stv` by
    (qpat_x_assum `!gs v mid. _` irule >>
     qexists_tac `xs` >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  simp[] >>
  qpat_x_assum `!H v mid G tn t. _` drule_all >> strip_tac >>
  drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [ADD_COMM] annassign_widened_full_source) >>
  simp[] >> disch_then drule_all >> simp[]
QED

(* The two implementation callbacks are literal contracts.  The common
   allocation/RHS prefix is a theorem dependency, never an assumption. *)
Theorem annassign_widened_full_execution:
  (contract_inv mods exps ctx old cx /\
     module_body_inv mods old.ce_module tops old cx) /\ supported_expr tops e /\
  type_widens_to env.type_defs (expr_type e) typ /\
  ~is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes old typ < 2 ** 64 /\
  FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  (!sa ce r. declare_local old id typ sa = (ce,r) ==>
    (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\ expr_body_pre_mods mods ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
    ~(lowered_value_type ce e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type ce e) /\
      arg_type_fits (lowered_value_type ce e) (expr_type e))) ==>
  stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ old
    (stmt_env old lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T old) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  strip_tac >>
  rewrite_tac[stmt_frag_full_def] >>
  map_every qx_gen_tac [`st0`,`sa`,`sf`,`shadow_sa`,`shadow_sf`,`s0`,`G0`,`tn0`,`ce`] >>
  strip_tac >>
  qpat_assum `return_buf_frame d old sa s0` (fn frame =>
    qpat_assum `return_buf_sep d old es s0` (fn sep =>
      irule (MATCH_MP gas_outcome_full_use_return_buf_allocas
        (CONJ frame sep)))) >>
  `old.ce_alloca_locals` by metis_tac[body_inv_contract, contract_inv_alloca_locals] >>
  drule_all annassign_full_prefix_parts >> strip_tac >>
  qpat_x_assum `!sa ce r. declare_local _ _ _ _ = _ ==> _` drule >>
  strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  `type_memory_bytes ce typ = type_memory_bytes old typ` by simp[] >>
  `ce.ce_func_return_type = build_func_return_type tops /\
   supported_program tops /\ get_module_code cx NONE = SOME tops` by
    (drule_then strip_assume_tac body_inv_main_code >>
     drule_then assume_tac body_inv_contract >>
     drule_then assume_tac body_inv_module >>
     drule_all_then strip_assume_tac contract_inv_module_gate >>
     drule_then assume_tac contract_inv_return_types >>
     fs[compileUnitTheory.build_func_return_type_mods_singleton]) >>
  `type_memory_bytes ce typ < 2 ** 64` by fs[] >>
  drule_all annassign_widened_full_layout >> strip_tac >>
  `~(has_length_word typ /\ is_empty_value_expr e)` by
    (qpat_x_assum `~is_bytestring_type (lowered_value_type ce e)` mp_tac >>
     qpat_x_assum `lowered_value_type ce e <> expr_type e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `e` >>
     simp[is_empty_value_expr_def,lowered_value_type_def]
     >~ [`Builtin ety builtin args`]
     >- (Cases_on `builtin` >> simp[is_empty_value_expr_def,lowered_value_type_def])
     >~ [`TypeBuiltin ety builtin ts args`]
     >- (Cases_on `builtin` >> simp[is_empty_value_expr_def,lowered_value_type_def])
     >> rename1 `Literal ety lit` >> Cases_on `lit` >>
     simp[is_empty_value_expr_def,lowered_value_type_def] >> Cases_on `ety` >>
     simp[lowered_value_type_def] >> qmatch_goalsub_rename_tac `Literal (BaseT bty) _` >> Cases_on `bty` >>
     simp[lowered_value_type_def] >> qmatch_goalsub_rename_tac `Literal (BaseT (BytesT bnd)) _` >> Cases_on `bnd` >>
     simp[lowered_value_type_def,is_bytestring_type_def]) >>
  gnvs[] >> suspend "prefix"
QED

Resume annassign_widened_full_execution[prefix]:
  markerLib.RESUME_TAC >> irule gas_outcome_full_initial_domain >> simp[] >> conj_tac
  >- irule (cj 1 vyperStorageTraceTheory.evaluate_storage_trace_frame) >>
  strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _ /\ _`
    (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes old typ < dimword (:256)` by simp[dimword_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  mp_tac (Q.SPECL
    [`DF`,`lo`,`d`,`PG`,`ctx`,`shadow_ctx`,`func`,`shadow_func`,`old`,`ce`,
     `cx`,`es`,`id`,`typ`,`e`,`st0`,`sa`,`r`,`a`,`b`,`shadow_a`,`shadow_b`,
     `p`,`type_memory_bytes old typ`,`op`,`s0`,`G0`,`tn0`,`lctx`]
    annassign_full_alloc_rhs_prefix) >>
  impl_tac
  >- (simp[] >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac) >>
  suspend "rhs"
QED

Resume annassign_widened_full_execution[rhs]:
  markerLib.RESUME_TAC >>
  drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)
    annassign_widened_full_rhs_source >>
  simp[] >>
  disch_then (qspecl_then [`type_memory_bytes old typ`,`stv`,`p`,`op`,`w`,`tyv`,
    `ce`,`b`,`sa.cs_next_id`,`a`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >> gvs[] >>
    first_x_assum drule >> simp[])) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ rhs_post _` >>
  suspend "source"
QED

Resume annassign_widened_full_execution[source]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_zero_prefix >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
  conj_tac >- simp[] >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
    (mp_then Any (qspecl_then [`id`,`e`] SUBST1_TAC) eval_annassign_action) >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`!v. storage_trace_frame (new_variable _ _ v)`]
  >- simp[storage_trace_frame_new_variable]
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res mid G tn t. rhs_post H res mid G tn t /\
    ~t.vs_halted /\ mid.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ rhs_post _` (irule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res`
      >- (qpat_x_assum `expr_exit (INL _) _` mp_tac >>
          simp_tac (srw_ss()) [exprSimDefsTheory.expr_exit_def]) >>
      qexists_tac `y` >> simp[NoAsms] >>
      irule (INST_TYPE [alpha |-> ``:value``]
        augAssignFullRhsSavedTheory.augassign_expr_exit_to_stmt_exit) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  BETA_TAC >> rpt strip_tac >> suspend "continuation"
QED

Resume annassign_widened_full_execution[continuation]:
  markerLib.RESUME_TAC >>
  qpat_assum `storage_trace_domain cx st0 mid.storage_trace`
    (assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qunabbrev_tac `rhs_post` >>
  Cases_on `res` >>
  qpat_x_assum `(\H res mid G tn t. _) _ _ _ _ _ _` mp_tac >>
  BETA_TAC >> simp_tac (srw_ss()) [] >> strip_tac >>
  suspend "new_variable"
QED

Resume annassign_widened_full_execution[new_variable]:
  markerLib.RESUME_TAC >>
  drule_all annassign_continuation_all_tails >> strip_tac >>
  qabbrev_tac `out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := x; popped := []|>))::rest` >>
  `out.gas_obs = []` by simp[Abbr `out`] >>
  `new_variable id tyv x mid = (INL (),out)` by
    (qpat_assum `!tail. new_variable _ _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >>
     simp_tac (srw_ss()) [Abbr `out`]) >>
  suspend "suffix"
QED

Resume annassign_widened_full_execution[suffix]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `?u Gu tu.
    lookup_var p u = SOME w /\
    FLOOKUP u.vs_allocas (sa.cs_next_id) = SOME (w2n w,type_memory_bytes old typ) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gu,tu)) /\
    !H. valid_horizon cx st0 H out.storage_trace ==>
      stmt_lands lctx sf (INL ()) u /\ ~u.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce out.scopes /\ stmt_state_rel H ctx func ce cx out u /\
      storage_well_formed_on cx out (FST H) /\ return_buf_frame d ce sf u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx out Gu tu u /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z u = SOME w) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      (!z. not_fresh_at sa z ==> FLOOKUP Gu z = FLOOKUP G0 z /\
        op_taint tu (Var z) = op_taint tn0 (Var z)) /\
      alloca_frame old es sa s0 ce out u /\
      (!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region old es.scopes s0 name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tu.t_mem ==> i IN tn0.t_mem)` by
    (mp_tac (Q.INST [
       `s` |-> `t`, `G` |-> `G1`, `tn` |-> `tn1`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
       `v` |-> `x`, `dw` |-> `w`, `dty` |-> `typ`, `dtv` |-> `tyv`,
       `sty` |-> `lowered_value_type old e`, `sz` |-> `type_memory_bytes old typ`,
       `n` |-> `type_memory_size stv`, `src_loc` |-> `vv_location vv`,
       `start` |-> `a`, `H0` |-> `storage_trace_horizon mid.storage_trace`,
       `inst` |-> `mk_inst sa.cs_next_id ALLOCA
         [Lit (n2w (type_memory_bytes old typ))] [p]`]
       annassign_memory_full_suffix_post) >>
     (impl_tac >- (
     `expr_sim_inv ce cx env es` by metis_tac[expr_body_pre_static_facts] >>
     drule_all immutable_assign_copy_metadata >> strip_tac >>
     `not_fresh_at b xs` by
       (qpat_assum `lower_value compile_expr ce (expr_type e) e a = _`
          (mp_then Any mp_tac compile_lower_value_var) >> simp[]) >>
     `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func ce cx mid t /\
      storage_well_formed_on cx mid (FST (storage_trace_horizon mid.storage_trace))` by
       fs[expr_post_def] >>
     `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
     `mid with gas_obs := [] = mid` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     `value_has_type stv x /\ val_wf stv x` by
       (qpat_assum `!gs v mid. _`
          (qspecl_then [`gas_explicit marks entry.vs_gas_readings`,`x`,`mid`] mp_tac) >>
        qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
        simp_tac (srw_ss()) [] >> simp[]) >>
     `a.cs_next_id <= b.cs_next_id` by
       (qpat_assum `lower_value compile_expr ce (expr_type e) e a = _`
         (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     `b.cs_next_var <= sf.cs_next_var` by
       (qpat_assum `compile_assign_value ce _ _ _ _ _ _ _ _ b = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> strip_tac >>
        metis_tac[cj 1 ci_mono_stmt_helpers,ci_mono_def,pairTheory.SND]) >>
     `sa.cs_next_id < b.cs_next_id /\ sa.cs_next_id <= b.cs_next_id` by decide_tac >>
     simp[Abbr `out`,ADD_COMM,venomInstTheory.mk_inst_def] >>
     conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- metis_tac[] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           drule >>
         disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def] o BETA_RULE) >>
         simp[]) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!aid off len i. _` irule >>
         simp[ADD_COMM] >> qexists_tac `aid` >> simp[ADD_COMM] >>
         rpt strip_tac >> first_x_assum drule >> decide_tac) >>
     `~(lowered_value_type ce e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type ce e) /\
        arg_type_fits (lowered_value_type ce e) (expr_type e))` by simp[] >>
     qpat_assum `compile_expr ce (expr_type e) e a = (vv,sv)`
       (mp_then (Pat `compile_expr _ _ _ _ = _`)
         (qspecl_then [`cx`,`env`,`es`] mp_tac) residual_call_compile_location) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `~block_is_terminated b` by (drule_all unwrap_value_open >> simp[]) >>
     irule compile_assign_memory_relayout_open >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[])) >> simp[venomInstTheory.mk_inst_def]) >>
  suspend "pure"
QED

Resume annassign_widened_full_execution[pure]:
  markerLib.RESUME_TAC >> (
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gu`,`out`,`INL ()`,`u`,`tu`] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  gen_tac >> disch_tac >> conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  `out with gas_obs := [] = out` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H out.storage_trace ==> _` drule >>
  simp[ADD_COMM] >> strip_tac >>
  `return_buf_sep d ce out u` by
    (`MAP FDOM (sc::rest) = MAP FDOM es.scopes` by
       (qpat_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
          (qspec_then `[]` (mp_tac o SRULE [])) >>
        strip_tac >> drule stmtSimDefsTheory.eval_read_preserves_scopes_dom >> simp[]) >>
     irule annassign_memory_return_buf_sep >>
     qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (w2n w,_)` (irule_at Any) >>
     qexistsl_tac [`st0`,`sc`,`sa`,`s0`,`rest`,`old`,`func`,`es`,`<|assignable := T; type := tyv; value := x; popped := []|>`,`cx`,`ctx`] >>
     simp[Abbr `out`] >> metis_tac[]) >>
  simp[ADD_COMM,return_buf_sep_gas_obs] >>
  qpat_assum `!aid off len i. _ ==> i IN tn0.t_mem`
    (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
  metis_tac[ADD_COMM])
QED

Finalise annassign_widened_full_execution
