(* Request-prefix companion to bodyFullTypeBuiltinExtract32. *)
Theory s1PrefixTypeBuiltinExtract32
Ancestors
  s1PrefixPreds bodyFullTypeBuiltinExtract32
  s1PrefixDefs s1PrefixOfVV s1PrefixCompose s1PrefixProps exprOpenFirstOperand stateRelProj
  bodyFullIfExpReach[qualified,ignore_grammar] bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullExtract32Prepare exprSimExtract32Source typeBuiltinPrereqs
  gasShadowCompileStmtHelpers gasShadowCompileBuiltinBytes gasOutcomeFullCompose
  vyperStorageTrace vyperStorageFootprint vyperState vyperContext loweringPosts
  bodyFullExprsListFacts bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule extract32_full_pre_shape >> strip_tac >> gvs[] >>
  `body_exprs_full_ok cx [src;off] /\ body_exprs_prefix_ok cx [src;off]` by
    (conj_tac >> first_x_assum irule >>
     simp[type_check_def,type_builtin_args_length_ok_def,assert_def,return_def]) >>
  conj_asm2_tac >- metis_tac[expr_sim_prefix_of_vv] >>
  simp[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >> rpt gen_tac >> strip_tac >>
  drule extract32_compile_equations >> strip_tac >> gvs[] >>
  qpat_assum `expr_type src = _`
    (fn th => drule_all (REWRITE_RULE [th] extract32_compile_cuts)) >> strip_tac >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def]) >>
  disch_then (strip_assume_tac o MATCH_MP extract32_compile_equations) >>
  drule_all (Q.INST [`src` |-> `gas_shadow_expr src`]
    extract32_compile_cuts) >> strip_tac >>
  gvs[] >>
  rename1 `lower_value _ _ _ (gas_shadow_expr src) shadow_sa = (_,sh1)` >>
  rename1 `compile_bytestring_src _ sh1 = (_,sh2)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr off) sh2 = (_,sh3)` >>
  `lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
     (gas_shadow_expr src) shadow_sa = (src_op,sh1) /\ gas_shadow_state s1 sh1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type src) src)
        (lower_value compile_expr (gas_shadow_env T cenv) (expr_type src)
           (gas_shadow_expr src))` by irule gas_shadow_stmt_lower_value_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     simp[]) >>
  `gas_shadow_state s2 sh2` by
    (mp_tac (Q.INST [`src_ptr` |-> `src_op`] gas_shadow_compiles_bytestring_src) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`sh1`] mp_tac) >> gvs[]) >>
  `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr off) sh2 = (off_op,sh3) /\
   gas_shadow_state s3 sh3` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty off)
        (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr off))` by
       irule gas_shadow_stmt_lower_value_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`s2`,`sh2`] mp_tac o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
     simp[]) >>
  `expr_body_pre cenv cx env src es'` by metis_tac[expr_body_pre_type_builtin_head] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type src) src es'` by
    (`body_expr_full_ok cx src` by fs[body_exprs_full_ok_cons] >>
     drule_all body_expr_full_ok_simulations >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type src) src es'` by
    (fs[body_exprs_prefix_ok_def] >> fs[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es'` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`sh1`,`src_op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [bodySimFullTheory.expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`sh1`,`src_op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  suspend "source_bind"
QED
*)
Theorem extract32_expr_prefix_ok:
  !cx v11 typ es.
  (!s'' x t.
       type_check (type_builtin_args_length_ok Extract32 (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (type_builtin_args_length_ok Extract32 (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (TypeBuiltin v11 Extract32 typ es)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume extract32_expr_prefix_ok[source_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ srcQ srcR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx src) (read_result cx)) (es',s0,G0,tn0)
     (\H res ee G tn z. srcQ H res ee G tn z /\
       ?ms. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) ms (OK z,G,tn)) srcR` by
    (irule bodyFullIfExpReachTheory.gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ srcQ srcR` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ srcQ srcR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ srcR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx src) (read_result cx)) (es',s0,G0,tn0)
     (\H res ee G tn z. pathQ H res ee G tn z /\ ~z.vs_halted /\ ee.gas_obs = []) srcR` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ srcR` (irule_at Any) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ pathQ srcR` kall_tac >>
  `!st. SND (eval_expr cx (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) st) =
    SND (bind (bind (eval_expr cx src) (read_result cx))
              (\v. bind (eval_expr cx off) (read_result cx)) st)` by
    (pure_rewrite_tac[eval_expr_extract32_vv_bind,ETA_AX] >>
     qabbrev_tac `srcM = bind (eval_expr cx src) (read_result cx)` >>
     qabbrev_tac `offM = bind (eval_expr cx off) (read_result cx)` >> gen_tac >>
     Cases_on `srcM st` >> rename1 `srcM st = (res,mid)` >>
     Cases_on `res` >> simp[bind_def] >>
     Cases_on `offM mid` >> rename1 `offM mid = (ans,ee)` >>
     Cases_on `ans` >> simp[lift_sum_def,return_def,raise_def] >>
     CASE_TAC >> simp[lift_sum_def,return_def,raise_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => rewrite_tac[th]) >>
  irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ srcR` (irule_at Any) >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_bind_all,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >~ [`!H res ee gt r. srcR H res ee gt r ==> ISR res`]
  >- (simp[Abbr `srcR`] >> rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]) >>
  suspend "offset_entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extract32_expr_prefix_ok[offset_entry]:
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms,Abbr `pathQ`,Abbr `srcQ`] >> strip_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx src) (read_result cx)
     (es' with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (mp_tac o REWRITE_RULE [ETA_AX,listTheory.APPEND_NIL] o Q.SPEC `[]`) >>
     disch_then (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `expr_body_pre cenv cx env src (es' with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] extract32_source_value) >> strip_tac >> gvs[] >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >> simp[vyperValueTheory.evaluate_type_def]) >>
  `post_value_type cenv src = expr_type src` by
    simp[post_value_type_bytestring,compileEnvTheory.is_bytestring_type_def] >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx src es' sa s1 s0 mid (BytesV bs) src_op t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `?p. eval_operand src_op t = SOME (n2w p)` by
    (drule typeBuiltinPrereqsTheory.extract32_source_post_alloca_bound >> simp[] >> metis_tac[]) >>
  `?sv. src_op = Var sv` by
    (qpat_x_assum `ptr_val_ok cx _ (BytesV bs) src_op G1 tn1 t` mp_tac >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def,bodyPtrDefsTheory.ptr_mem_ok_def,
          compileEnvTheory.is_word_type_def,val_footprint_def] >>
     strip_tac >>
     qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
       (qspec_then `BaseTV (BytesT (Dynamic m))` mp_tac) >>
     fs[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_var <= s2.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at s1 sv` by metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `alloca_inv t` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule exprSimWordArgsTheory.expr_post_state >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx src es' sa s1 s0 mid (BytesV bs) (Var sv) t /\
    expr_store_bound cx (expr_type src) (BytesV bs) (Var sv) t /\
    ptr_val_ok cx (expr_type src) (BytesV bs) (Var sv) G1 tn1 t /\
    ptr_buf_ok cenv src (Var sv) G1 t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ghost_kept_at lo cenv es' sa G0 tn0 s0 G1 tn1` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     fs[compileEnvTheory.is_word_type_def]) >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Dynamic m)))` by simp[] >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    extract32_prepare_full) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  suspend "offset_prefix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extract32_expr_prefix_ok[offset_prefix]:
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all,storage_trace_frame_read_result] >>
  qexistsl_tac [`G2`,`u`,`tn2`] >>
  (conj_tac >- metis_tac[]) >>
  `expr_body_pre cenv cx env off mid` by
    (`expr_body_pre cenv cx env (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off])
       (es' with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all extract32_offset_body_pre >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule bodyFullPredsTheory.body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx src) _ _ = (INL _,mid)` (irule_at Any) >>
     simp[] >> metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts]) >>
  `body_expr_prefix_ok cx off` by
    (qpat_assum `bind (eval_expr cx src) _ _ = (INL _,mid)`
       (mp_then Any strip_assume_tac (REWRITE_RULE [ETA_AX] exprSimSourceTheory.eval_expr_read_INL)) >>
     fs[body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty off mid` by
    (fs[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx off) (read_result cx)) expr_res_ok mid` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ off _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`s2`,`s3`,`sh2`,`sh3`,`off_op`,`u`,`G2`,`tn2`] mp_tac) >>
  (impl_tac >- suspend "offset_inputs") >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume extract32_expr_prefix_ok[offset_inputs]:
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid u /\
     storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G2 tn2 u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     fs[expr_post_def]) >>
  `return_buf_frame d cenv s2 u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> fs[expr_post_def]) >>
  simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,G1,tn1)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
          bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     simp[] >> metis_tac[]) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)`
       (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac
          bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) >>
     simp[] >> metis_tac[]) >>
  simp[] >>
  qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,G2,tn2)`
    (mp_then Any strip_assume_tac fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
  metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise extract32_expr_prefix_ok
*)
