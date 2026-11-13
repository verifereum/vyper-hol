(* A producer followed immediately by allocation, forcing, and typed store. *)
Theory bodyIntCallStageEndpointMemory
Ancestors
  bodyIntCallStageEndpointLanding bodyIntCallStageEndpointStore
  bodyIntCallCompilerTags bodyIntCallJointContract exprSimSubscriptMap
  bodyIntCallFamStmtReturnTypes bodyIntCallFamStmtLogArgsFrame
  exprSimAggregateChildren memoryLocalRhsProps typedMemoryCopy
  bodyIntCallJointForce exprSimSource exprSimMemDefs stmtSimForLoop
  exprBopSimProps exprSimHyps valueEncodingTyping exprLoweringProps
  exprSimIfExp bodyIntCallForcingReadOnly

Theorem stage_incompatible_geometry[local]:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  (!src:256 word. ~is_word_type sty /\ val_footprint stv v <> 0 /\
    eval_operand op u = SOME src ==>
    regions_disjoint (w2n src) (val_footprint stv v) (w2n dw) cap) /\
  type_memory_size dtv <= cap /\
  (sty <> NoneT /\ ~is_word_type sty /\ ~is_bytestring_type sty ==>
    ?src:256 word a k. eval_operand op u = SOME src /\ a <= w2n src /\
      w2n src + type_memory_size stv <= a+k /\ a+k < dimword (:256)) ==>
  ~(dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) ==>
  !src:256 word. eval_operand op u = SOME src ==>
    regions_disjoint (w2n src) (type_memory_size stv)
      (w2n dw) (type_memory_size dtv) /\
    w2n src + type_memory_size stv < dimword (:256)
Proof
  rpt strip_tac >>
  `~is_word_type sty` by metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type sty` by
    (fs[vyperTypeSystemTheory.type_widens_to_def] >>
     metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_target]) >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[evaluated_nonbytes_footprint] >>
  Cases_on `type_memory_size stv = 0`
  >- (drule_all widening_zero_memory_size >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def, wordsTheory.w2n_lt]) >>
  `sty <> NoneT` by
    (Cases_on `sty` >> gvs[vyperValueTheory.evaluate_type_def,
      valueEncodingTheory.type_memory_size_def]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Theorem stage_call_tag[local]:
  vv_type (FST (compile_call cfn ce ann ty target args drv st)) =
    (case target of IntCall fid => ce.ce_func_return_type (nsid_to_string fid)
      | _ => ann)
Proof
  Cases_on `target`
  >~ [`ExtCall b c p opts`] >-
    (PairCases_on `p` >> Cases_on `args` >>
     simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
          contextTheory.vv_type_def] >>
     rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def])) >>
  (namedCases_on `args` ["", "a rest"]
  >- (simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
           contextTheory.vv_type_def] >>
      rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def])) >>
  namedCases_on `rest` ["", "b rest2"]
  >- (simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
           contextTheory.vv_type_def] >>
      rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def])) >>
  Cases_on `rest2` >>
  simp[exprLoweringTheory.compile_call_def, pairTheory.ELIM_UNCURRY,
       contextTheory.vv_type_def] >>
  rpt (IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def]))
QED

Theorem stage_expr_root_tag[local]:
  vv_type (FST (compile_expr ce (expr_type e) e st)) =
    (case e of Call ann (IntCall fid) args drv =>
       ce.ce_func_return_type (nsid_to_string fid) | _ => expr_type e)
Proof
  Cases_on `expr_effect_root e`
  >- (Cases_on `e` >> gvs[supportedExprTraverseTheory.expr_effect_root_def] >>
      once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
      simp[exprLoweringTheory.compile_expr_body_def, stage_call_tag,
           pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def] >>
      Cases_on `t` >> simp[stage_call_tag]) >>
  `vv_type (FST (compile_expr ce (expr_type e) e st)) = expr_type e` by
    (once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
     irule intcall_expr_body_tag >> simp[] >> conj_tac >> rpt gen_tac >>
     IF_CASES_TAC >> simp[exprCallBoundsTheory.invalid_expr_call_def, contextTheory.vv_type_def] >>
     once_rewrite_tac[exprLoweringTheory.compile_expr_raw_def] >>
     simp[intcall_builtin_dispatch_body_tag, intcall_type_dispatch_body_tag,
          pairTheory.ELIM_UNCURRY, contextTheory.vv_type_def]) >>
  simp[] >> Cases_on `e` >> gvs[supportedExprTraverseTheory.expr_effect_root_def]
QED

Theorem stage_compiler_store_post_type[local]:
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  type_widens_to tenv (expr_type e) dty ==>
  compile_store_memory ce src dst dty (vv_type vv) =
  compile_store_memory ce src dst dty (post_value_type ce e)
Proof
  strip_tac >>
  Cases_on `is_word_type dty` >- simp[contextTheory.compile_store_memory_def] >>
  Cases_on `is_bytestring_type dty` >- simp[contextTheory.compile_store_memory_def] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[type_widens_from_word, typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `vv_type vv = (case e of Call ann (IntCall fid) args drv =>
     ce.ce_func_return_type (nsid_to_string fid) | _ => expr_type e)` by
    metis_tac[stage_expr_root_tag, pairTheory.FST] >>
  Cases_on `e` >> gvs[loweringPostsTheory.post_value_type_def,
                         vyperASTTheory.expr_type_def] >>
  rename1 `Call ann target args drv` >> Cases_on `target` >>
  gvs[loweringPostsTheory.post_value_type_def, vyperASTTheory.expr_type_def,
      exprLoweringTheory.lowered_value_type_def]
QED

Theorem intcall_stage_memory_arg_outcome:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  expr_body_pre ce fp.jc_cx env e es /\
  type_widens_to (get_tenv fp.jc_cx) (expr_type e) ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
  type_memory_bytes ce ty = type_memory_size dtv /\
  MAX 32 (type_memory_size dtv) + 64 < dimword (:256) /\
  compile_expr ce (expr_type e) e sa = (vv,s1) /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) s1 = (buf,s2) /\
  unwrap_value ce vv s2 = (op,s3) /\
  compile_store_memory ce op buf.buf_operand ty (vv_type vv) s3 = ((),sb) /\
  fn_has_code sa s1 fp.jc_func /\ fn_has_code s1 s2 fp.jc_func /\
  fn_has_code s2 s3 fp.jc_func /\ fn_has_code s3 sb fp.jc_func /\
  fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (vyperState$bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
    (\res ee u. ?v w. res = INL v /\
       eval_operand buf.buf_operand u = SOME w /\
       (!x. buf.buf_operand = Var x ==> not_fresh_at sb x) /\
       val_in_memory dtv v (w2n w) u.vs_memory /\ val_wf dtv v /\
       FLOOKUP u.vs_allocas s1.cs_next_id = SOME (w2n w,MAX 32 (type_memory_size dtv)) /\
       sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id < sb.cs_next_id /\
       w2n w + MAX 32 (type_memory_size dtv) <= u.vs_alloca_next /\
       w2n w + MAX 32 (type_memory_size dtv) < dimword (:256) /\
       (!name a k. local_region ce ee.scopes u name a k ==>
          regions_disjoint (w2n w) (MAX 32 (type_memory_size dtv)) a k) /\
       intcall_expr_cont fp ce env es sa t ee sb u /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  dxrule (iffLR intcall_expr_producer_def) >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then drule_all >> disch_tac >>
  irule gas_outcome_bind_result_exec >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (Cases >> simp[exprSimDefsTheory.expr_exit_INL,
                            stmtSimPropsTheory.expr_exit_INR_type]) >>
  reverse conj_tac >- metis_tac[] >>
  suspend "stage"
QED

Resume intcall_stage_memory_arg_outcome[stage]:
  rpt gen_tac >> strip_tac >>
  rename1 `gas_marked_exec _ _ _ _ marks (INL raw) mid (OK q)` >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa s1 t
     (mid with gas_obs := []) raw vv q` by
    (fs[loweringPostsTheory.vv_post_def, intcall_expr_cont_def, intcall_expr_res_def] >>
     metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env es /\ well_typed_expr env e` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  drule intcall_force_static_layout >> strip_tac >>
  `type_widens_to env.type_defs (expr_type e) ty` by metis_tac[] >>
  drule_all bodyIntCallJointAggCoreTheory.intcall_child_read_layout >> strip_tac >>
  `read_result fp.jc_cx raw (mid with gas_obs := []) =
     (INL v,mid with gas_obs := [])` by simp[] >>
  `vv_holds ce fp.jc_cx (post_value_type ce e) (Value v) vv
     (mid with gas_obs := []) q` by
    metis_tac[bodyIntCallForcingReadOnlyTheory.vv_holds_materialise] >>
  `vv_at ce fp.jc_cx (post_value_type ce e) sa s1
     (mid with gas_obs := []) (Value v) vv q` by
    metis_tac[exprSimIfExpTheory.ifexp_vv_at_conditional] >>
  `intcall_expr_res fp ce env (mid with gas_obs := []) s1 q /\
   ~q.vs_halted /\ q.vs_current_bb = s1.cs_current_bb /\
   q.vs_inst_idx = LENGTH s1.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `sa.cs_next_id <= s1.cs_next_id` by
    (mp_tac (cj 1 exprLoweringPropsTheory.compile_expr_ci_mono) >>
     disch_then (qspecl_then [`ce`, `expr_type e`, `e`, `sa`] mp_tac) >>
     simp[ci_mono_def]) >>
  `MAX 32 (type_memory_bytes ce ty) < dimword (:256)` by
    (qpat_x_assum `MAX 32 _ + 64 < _` mp_tac >> simp[arithmeticTheory.MAX_DEF]) >>
  `post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e) /\
   (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
   ?w a k. eval_operand (vv_operand vv) q = SOME w /\ a <= w2n w /\
     w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
     (fp.jc_lo <= a \/ ?d z. fp.jc_staged d z /\ d <= a /\ a+k <= d+z)` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all intcall_stage_alloc_force_landing >> strip_tac >>
  `type_widens_to (get_tenv fp.jc_cx) (post_value_type ce e) ty` by
    metis_tac[bodyIntCallFamStmtReturnEndpointTypesTheory.return_post_type_widens] >>
  `compile_store_memory ce op buf.buf_operand ty (post_value_type ce e) s3 = ((),sb)` by
    metis_tac[stage_compiler_store_post_type] >>
  `type_memory_size dtv <= MAX 32 (type_memory_bytes ce ty)` by simp[] >>
  `~(ty = post_value_type ce e \/
       is_bytestring_type ty /\ is_bytestring_type (post_value_type ce e)) ==>
   !sw. eval_operand op u = SOME sw ==>
    regions_disjoint (w2n sw) (type_memory_size tv) (w2n w) (type_memory_size dtv) /\
    w2n sw + type_memory_size tv < dimword (:256)` by
    (match_mp_tac (Q.INST [`tenv` |-> `get_tenv fp.jc_cx`,
       `cap` |-> `MAX 32 (type_memory_bytes ce ty)`] stage_incompatible_geometry) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `ci_mono s1 s3 /\ ci_mono s3 sb` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `s2`] ci_mono_unwrap_value) >>
     mp_tac (Q.SPECL [`ce`, `op`, `buf.buf_operand`, `ty`, `vv_type vv`, `s3`]
       ci_mono_compile_store_memory) >>
     mp_tac (Q.SPECL [`MAX 32 (type_memory_bytes ce ty)`, `s1`]
       ci_mono_compile_alloc_buffer) >>
     simp[] >> metis_tac[ci_mono_trans]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> disch_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts fp.jc_func)` >>
  `inst.inst_id = s1.cs_next_id /\ inst.inst_opcode = ALLOCA` by
    simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    intcall_stage_physical_store_cont >>
  disch_then (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_rel _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  FAIL_TAC "store premises"
QED
Finalise intcall_stage_memory_arg_outcome
