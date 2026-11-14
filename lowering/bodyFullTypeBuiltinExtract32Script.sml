Theory bodyFullTypeBuiltinExtract32
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  bodyFullExtract32Prepare bodyFullExtract32Suffix bodyMemTbExtract32Cuts
  bodyFullExtract32JoinFrame bodyPtrTypeBuiltinsSavedOperand
  gasShadowCompile gasShadowCompileStmtHelpers exprOperandVar exprLoweringProps stmtSimProps
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimExtract32Source
  vyperContext vyperInterpreter vyperState vyperAST

(* The current typing contract excludes fixed-byte sources and signed offsets.
   Keep this boundary local rather than narrowing the frozen expression case. *)
Theorem extract32_full_pre_shape[local]:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 t args) es ==>
  ?src off m k bt.
    args = [src;off] /\
    expr_type src = BaseT (BytesT (Dynamic m)) /\
    expr_type off = BaseT (UintT k) /\
    t = BaseT bt /\ extract32_result_base_ok bt /\ ann = t
Proof
  strip_tac >> drule extract32_body_pre_shape >> strip_tac >> gvs[] >>
  fs[exprSimHypsDefsTheory.expr_body_pre_def,
     vyperTypeSystemTheory.well_typed_expr_def,
     vyperTypeSystemTheory.well_typed_type_builtin_args_def,
     vyperTypeSystemTheory.is_uint_type_def] >> metis_tac[]
QED

Theorem extract32_vv_full[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  body_exprs_full_ok cx [src;off] ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Extract32 ret [src;off]) es
Proof
  strip_tac >> drule extract32_full_pre_shape >> strip_tac >> gvs[] >>
  simp[bodySimFullTheory.expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule extract32_compile_equations >> strip_tac >> gvs[] >>
  qpat_assum `expr_type src = _`
    (fn th => drule_all (REWRITE_RULE [th] extract32_compile_cuts)) >> strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_arg >>
     conj_tac >- fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type src) src es` by
    (fs[body_exprs_full_ok_def, body_expr_full_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (drule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_vv_first_admissible) >> simp[]) >>
  `?shadow_s1. lower_value compile_expr cenv (expr_type src)
      (gas_shadow_expr src) shadow_sa = (src_op,shadow_s1) /\
      gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type src`, `e` |-> `src`] gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv (expr_type src)
       (gas_shadow_expr src) shadow_sa` >> gvs[]) >>
  `fn_has_code shadow_sa shadow_s1 shadow_func` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_expr_def] >>
     strip_tac >> drule extract32_compile_equations >> strip_tac >>
     gvs[] >>
     `expr_type (gas_shadow_expr src) = BaseT (BytesT (Dynamic m))` by simp[] >>
     qpat_assum `expr_type (gas_shadow_expr src) = _`
       (fn th => drule_all (REWRITE_RULE [th]
         (Q.INST [`src` |-> `gas_shadow_expr src`] extract32_compile_cuts))) >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [bodySimFullTheory.expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
    `src_op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ srcQ srcR` >>
  rewrite_tac[eval_expr_extract32_vv_bind] >>
  irule gas_outcome_full_bind_all >>
  `!res : value + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=>
       expr_exit res r` by (Cases >> simp[stmtSimPropsTheory.expr_exit_INR_type]) >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_lifts,
       vyperStorageTraceTheory.storage_trace_frame_return] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> ho_match_mp_tac gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`v`, `mid`, `t`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. srcQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "source_continuation" >>
  irule gas_outcome_full_post_source >>
  qexistsl_tac [`srcQ`,`srcR`] >>
  asm_rewrite_tac[] >> rpt conj_tac >> simp[] >> metis_tac[]
QED

Resume extract32_vv_full[source_continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `srcQ`, NoAsms] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx src) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (`mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!tail. bind _ _ _ = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV) o Q.SPEC `[]`) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `expr_body_pre cenv cx env src
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_source_value) >>
  strip_tac >> gvs[] >>
  `sa.cs_next_var <= s1.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (drule expr_body_pre_type_evaluates >> simp[vyperValueTheory.evaluate_type_def]) >>
  `post_value_type cenv src = expr_type src` by
    simp[loweringPostsTheory.post_value_type_bytestring, compileEnvTheory.is_bytestring_type_def] >>
  `alloca_inv s` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> fs[loweringPostsTheory.expr_post_def, stmt_state_rel_def]) >>
  `?p. eval_operand src_op s = SOME (n2w p)` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule bodyMemTbExtract32SourceTheory.extract32_source_post_view >>
     simp[] >> metis_tac[]) >>
  `?sv. src_op = Var sv` by
    (fs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
        compileEnvTheory.is_word_type_def] >>
     `~is_word_type (expr_type src)` by
       (qpat_assum `expr_type src = _` (fn th => rewrite_tac[th]) >>
        simp[compileEnvTheory.is_word_type_def]) >>
     fs[loweringPostsTheory.val_footprint_def] >> metis_tac[]) >>
  gvs[] >>
  `not_fresh_at s1 sv` by metis_tac[compile_lower_value_var] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx src es sa s1 s0 mid (BytesV bs) (Var sv) s /\
    expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) s /\
    ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G1 tn1 s /\
    ptr_buf_ok cenv src (Var sv) G1 s /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (rpt strip_tac >> fs[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by simp[] >>
  drule_all (Q.INST
    [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    extract32_prepare_full) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  irule gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_lifts,
       vyperStorageTraceTheory.storage_trace_frame_return] >>
  qexistsl_tac [`G2`,`u`,`tn2`] >>
  conj_tac >- metis_tac[] >>
  suspend "offset_entry"

QED

Resume extract32_vv_full[offset_entry]:
  `expr_body_pre cenv cx env off mid` by
    (`expr_body_pre cenv cx env
       (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all bodyMemTbExtract32ActionTheory.extract32_offset_body_pre >> simp[]) >>
  `body_expr_full_ok cx off` by
    (qpat_x_assum `body_exprs_full_ok cx [src;off]` mp_tac >>
     simp[body_exprs_full_ok_def] >> strip_tac >>
     first_x_assum irule >>
     qpat_x_assum `bind _ _ _ = (INL _,mid)` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty off mid` by
    (fs[body_expr_full_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx off) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `?shadow_s2. compile_bytestring_src (Var sv) shadow_s1 = ((len,data),shadow_s2) /\
      gas_shadow_state s2 shadow_s2` by
    (mp_tac (Q.INST [`src_ptr` |-> `Var sv`] gasShadowCompileBuiltinBytesTheory.gas_shadow_compiles_bytestring_src) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`shadow_s1`] mp_tac) >> simp[] >>
     Cases_on `compile_bytestring_src (Var sv) shadow_s1` >> gvs[]) >>
  `?shadow_s3. lower_value compile_expr cenv ty (gas_shadow_expr off) shadow_s2 =
      (off_op,shadow_s3) /\ gas_shadow_state s3 shadow_s3` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `ty`, `e` |-> `off`]
      gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s2`,`shadow_s2`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv ty (gas_shadow_expr off) shadow_s2` >> gvs[]) >>
  `fn_has_code shadow_s2 shadow_s3 shadow_func` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gasShadowTheory.gas_shadow_expr_def] >>
     strip_tac >> drule extract32_compile_equations >> strip_tac >> gvs[] >>
     `expr_type (gas_shadow_expr src) = BaseT (BytesT (Dynamic m))` by simp[] >>
     qpat_assum `expr_type (gas_shadow_expr src) = _`
       (fn th => drule_all (REWRITE_RULE [th]
         (Q.INST [`src` |-> `gas_shadow_expr src`] extract32_compile_cuts))) >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ off _`
    (mp_tac o REWRITE_RULE [bodySimFullTheory.expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`s2`,`s3`,`shadow_s2`,`shadow_s3`,
    `off_op`,`u`,`G2`,`tn2`] mp_tac) >>
  impl_tac >- suspend "offset_inputs" >>
  strip_tac >> suspend "offset_continuation"
QED

Resume extract32_vv_full[offset_inputs]:
  `sa.cs_next_var <= s2.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid u /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G2 tn2 u` by
    (rpt strip_tac >> res_tac >> fs[loweringPostsTheory.expr_post_def]) >>
  `return_buf_frame d cenv s2 u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     fs[loweringPostsTheory.expr_post_def]) >>
  simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
  simp[fragExecTheory.exit_result_def]
QED

Resume extract32_vv_full[offset_continuation]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ offQ offR` >>
  irule gas_outcome_full_bind_all >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_lifts,
       vyperStorageTraceTheory.storage_trace_frame_return] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> ho_match_mp_tac gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`v`, `mid'`, `t`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. offQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "suffix_entry" >>
  irule gas_outcome_full_post_source >>
  qexistsl_tac [`offQ`,`offR`] >>
  asm_rewrite_tac[] >> rpt conj_tac >> simp[] >> metis_tac[]
QED

Resume extract32_vv_full[suffix_entry]:
  qx_genl_tac [`marks'`,`res`,`ee`,`G3`,`tn3`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `offQ`, NoAsms] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx off) (read_result cx)
     (mid with gas_obs := gas_explicit marks' u.vs_gas_readings) = (INL v,ee)` by
    (qpat_assum `!tail. bind (eval_expr cx off) _ _ = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV) o Q.SPEC `[]`) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  `expr_body_pre cenv cx env off
     (mid with gas_obs := gas_explicit marks' u.vs_gas_readings)` by simp[] >>
  `is_uint_type (expr_type off)` by simp[vyperTypeSystemTheory.is_uint_type_def] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_offset_value) >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env off
     (mid with gas_obs := gas_explicit marks' u.vs_gas_readings)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimExtract32PostTheory.extract32_offset_bounds) >> strip_tac >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     src es sa s2 s0 mid (BytesV bs) (Var sv) u` by metis_tac[] >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     off mid s2 s3 u ee (IntV i) off_op t` by metis_tac[] >>
  pop_assum (mk_asm "offset_post") >>
  `expr_sim_inv cenv cx env mid` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) (expr_type off) = SOME (BaseTV (UintT k))` by
    (qpat_assum `expr_body_pre _ _ _ off mid` (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H
       (mid with gas_obs := gas_explicit marks' u.vs_gas_readings).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl_tac [`bind (eval_expr cx off) (read_result cx)`,`INL (IntV i)`,`ee`] >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `expr_post (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     src es sa s2 s0 mid (BytesV bs) (Var sv) u` by metis_tac[] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by simp[] >>
  drule_all exprSimExtract32PostTheory.extract32_source_post_view >> strip_tac >>
  `p' + 32 + LENGTH bs < dimword (:256)` by
    (gvs[wordsTheory.n2w_11] >>
     `p' < dimword (:256)` by decide_tac >>
     gvs[arithmeticTheory.LESS_MOD]) >>
  `p' + (LENGTH bs + 32) < dimword (:256)` by decide_tac >>
  asm "offset_post" assume_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`src_op` |-> `Var sv`, `len` |-> `Var len'`, `dp` |-> `Var data'`]
      exprSimExtract32PostTheory.extract32_offset_post_view)) >> strip_tac >>
  `ghost_kept cenv mid s2 G2 tn2 u G3 tn3` by
    (qpat_assum `ghost_kept_at lo cenv mid s2 _ _ _ _ _`
       (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     simp[bodyPtrDefsTheory.ghost_kept_def, bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  `op_prov G3 (Var len') = NONE /\ op_taint tn3 (Var len') = {}` by
    (qpat_assum `ghost_kept_at lo cenv mid s2 _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     disch_then (qspec_then `len'` mp_tac) >>
     gvs[ptrDisciplineTheory.op_prov_def]) >>
  `!span. 0 < LENGTH bs /\ span <= LENGTH bs ==> ptr_covers G3 tn3 data' t span` by
    (rpt strip_tac >>
     qpat_assum `ghost_kept_at lo cenv mid s2 _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     disch_then (qspec_then `data'` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G2 tn2 data' u n`
       (qspec_then `span` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then assume_tac >>
     fs[bodyPtrDefsTheory.ptr_covers_def,
        venomStateTheory.eval_operand_def] >> gvs[] >> decide_tac) >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G2 tn2 u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def, compileEnvTheory.is_word_type_def]) >>
  `expr_val_at cenv cx (expr_type src) sa s2 mid (BytesV bs) (Var sv) u` by
    (qpat_assum `expr_post _ _ _ _ _ src es sa s2 s0 mid _ _ u`
       (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[] >> metis_tac[]) >>
  `~is_word_type (expr_type src) /\
   (!tv. evaluate_type (get_tenv cx) (expr_type src) = SOME tv ==> dynarray_free tv)` by
    simp[compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def,
         exprSimPropsTheory.dynarray_free_base] >>
  `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G3 tn3 t` by
    (irule (INST_TYPE [alpha |-> ``:256``]
       bodyPtrTypeBuiltinsSavedOperandTheory.saved_ptr_mem_ok) >>
     simp[] >>
     asm "offset_post" (irule_at Any) >>
     qexistsl_tac [`tn2`, `sa`, `env`, `G2`] >> gvs[]) >>
  `cs_extends s2 s3 /\ s2.cs_next_var <= s3.cs_next_var /\
   s2.cs_next_id <= s3.cs_next_id /\
   (!z. off_op = Var z ==> not_fresh_at s3 z) /\
   (!l. off_op <> Label l)` by
    (irule expr_body_pre_lower_value_word_shape >>
     qpat_assum `lower_value _ _ _ off s2 = _` (irule_at Any) >>
     qexistsl_tac [`mid`, `env`] >> simp[compileEnvTheory.is_word_type_def] >>
     qexists_tac `cx` >> simp[]) >>
  qpat_assum `expr_type src = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_assum `expr_type off = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at Any (Q.INST [`srcop` |-> `Var sv`] extract32_suffix_full) >>
  qpat_assum `compile_clamp_basetype _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_extract32_load _ _ _ _ = _` (irule_at Any) >>
  simp[] >>
  qexistsl_tac [`tn0`, `sv`, `sa`, `s0`, `p'`, `es`, `d`, `cenv`, `G0`] >>
  simp[] >>
  conj_tac >- suspend "result_bounds" >>
  conj_tac >- (rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `op_prov G3 off_op = NONE /\ op_taint tn3 off_op = {}` by
    (`post_value_type cenv off = expr_type off` by
       (irule loweringPostsTheory.post_value_type_word >>
        simp[compileEnvTheory.is_word_type_def]) >>
     metis_tac[compileEnvTheory.is_word_type_def,
       bodyPtrDefsTheory.ptr_val_ok_def]) >>
  simp[] >>
  conj_tac >- gvs[] >>
  conj_tac >- (fs[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `sa.cs_next_var <= s3.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  conj_tac >- (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
               qexists_tac `sa` >> simp[]) >>
  simp[] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >-
    (asm "offset_post" (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  qx_gen_tac `H` >> disch_tac >>
  `expr_post H ctx func cenv cx off mid s2 s3 u ee (IntV i) off_op t /\
   ghost_inv_at (DF H) lo d cenv cx ee G3 tn3 t` by metis_tac[] >>
  conj_tac >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
  conj_tac >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
  `expr_post H ctx func cenv cx src es sa s2 s0 mid (BytesV bs) (Var sv) u /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by metis_tac[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind (eval_expr cx src) _ _ = (INL _,mid)` mp_tac >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     disch_then (mp_tac o MATCH_MP (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace` suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] vyperStorageFootprintTheory.valid_horizon_frame) >>
     qexistsl_tac [`bind (eval_expr cx src) (read_result cx)`,`INL (BytesV bs)`,`mid`] >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  `wb_frame cenv es ee sa s0 t` by
    (irule (INST_TYPE [alpha |-> ``:256``] extract32_join_wb_frame) >>
     qpat_assum `expr_post H _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_post H _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  conj_tac >- simp[] >>
  conj_tac >-
    (strip_tac >> irule (SIMP_RULE (srw_ss()) [loweringPostsTheory.expr_has_effect_thm]
       (INST_TYPE [alpha |-> ``:256``] extract32_join_pure_frame)) >>
     qpat_assum `expr_post H _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_post H _ _ _ _ off _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `wb_frame cenv es mid sa s0 u` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  irule (INST_TYPE [alpha |-> ``:256``] extract32_join_ghost_kept_at) >>
  qpat_assum `stmt_state_rel H _ _ _ _ es s0` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv mid s2 G2 tn2 u G3 tn3` (irule_at Any) >> simp[]
QED

Resume extract32_vv_full[result_bounds]:
  qpat_x_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _` mp_tac >>
  simp[exprSimHypsDefsTheory.expr_body_pre_def,
       vyperTypeSystemTheory.well_typed_expr_def, NoAsms] >>
  strip_tac >>
  qpat_x_assum `well_formed_type _ (BaseT bt)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `bt` >>
  simp[vyperTypeSystemTheory.well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  rpt CASE_TAC >> gvs[] >> decide_tac
QED

Finalise extract32_vv_full

Theorem extract32_expr_full_ok:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok Extract32 (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 Extract32 typ es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  drule extract32_full_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_full_ok cx [src;off]` by
    (first_x_assum irule >>
     simp[vyperStateTheory.type_check_def,
          vyperContextTheory.type_builtin_args_length_ok_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) es'` by
    (irule extract32_vv_full >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env
     (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])
     (es' with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
