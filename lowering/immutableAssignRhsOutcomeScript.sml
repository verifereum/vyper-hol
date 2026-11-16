(* The RHS prefix preserves the physical value layout used by the write. *)
Theory immutableAssignRhsOutcome
Ancestors
  immutableAssignSource bodyMemAggregateUnwrap exprSimAggregateChildren
  immutableDeployPhysicalSource exprSimMemUnwrap exprSimMemDefs
  exprSimSource exprSimUnwrap valueCopyBytes valueEncoding valueEncodingProofs
  exprSimUnwrapProps exprSimMemorySource exprSimHyps exprSimHypsDefs
  memoryLocalRhsProps stmtSimForced exprLoweringProps exprOperandVar
  loweringPosts exprLowering stmtLowering compileEnv context
  fragGasMode fragGasPath fragGasPathMem gasOutcome gasSummary vyperInterpreter
  vyperState vyperTypeInvariants vyperTypeEnvPreservation
  typedMemoryCopy finite_map alist list arithmetic
Libs monadsyntax

Theorem immutable_rhs_noop_bounds[local]:
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s /\
  ((?t. vv = StackValue t op) \/
   (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\
          p.ptr_operand = op)) ==>
  expr_store_bound cx (expr_type e) v op s /\
  (~is_word_type (expr_type e) ==>
   !w tv. eval_operand op s = SOME w /\
     evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==>
     type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next)
Proof
  simp[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
  metis_tac[]
QED

Theorem immutable_rhs_unwrap_mem_path[local]:
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,su) /\
  local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func ce cx e es sa sm s0 ee (Value v) vv s) /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func ce cx e es sa su s0 ee v op u) /\
    expr_store_bound cx (expr_type e) v op u /\
    (~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
     !w tv. eval_operand op u = SOME w /\
       evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==>
       type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= u.vs_alloca_next) /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `vv_post H0 ctx func ce cx e es sa sm s0 ee (Value v) vv s` by metis_tac[] >>
  qsuff_tac `?u. gas_marked_path T ctx func s 0 (OK u) /\
    expr_post H0 ctx func ce cx e es sa su s0 ee v op u /\
    expr_store_bound cx (expr_type e) v op u /\
    (~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
     !w tv. eval_operand op u = SOME w /\
       evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==>
       type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= u.vs_alloca_next) /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_requests = s.vs_requests /\ u.vs_call_ctx = s.vs_call_ctx`
  >- (strip_tac >> qexists_tac `u` >> asm_simp_tac bool_ss [] >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      mp_tac (Q.INST [`H0` |-> `H0`, `H` |-> `H`, `ctx` |-> `ctx`,
        `func` |-> `func`, `cenv` |-> `ce`, `cx` |-> `cx`, `e` |-> `e`,
        `es` |-> `es`, `sa` |-> `sa`, `sb` |-> `su`, `s0` |-> `s0`,
        `es'` |-> `ee`, `v` |-> `v`, `op` |-> `op`, `s` |-> `s`, `u` |-> `u`]
        (SPEC_ALL (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
          exprSimUnwrapTheory.expr_post_fields_transport))) >>
      impl_tac >- fs[loweringPostsTheory.vv_post_def] >> simp[]) >>
  `!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64` by metis_tac[expr_body_pre_copy_ok] >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
    lowered_value_type ce e = post_value_type ce e` by
    (strip_tac >>
     `type_widens_to env.type_defs (post_value_type ce e) (expr_type e)` by
       metis_tac[post_value_type_widens, expr_body_pre_def] >>
     drule immutable_rhs_post_physical_classify >>
     metis_tac[type_widens_from_bytestring]) >>
  Cases_on `post_value_type ce e = expr_type e`
  >- (Cases_on `is_word_type (expr_type e)`
      >- (`?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
            metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
          drule_at (Pat `unwrap_value _ _ _ = _`)
            (INST_TYPE [alpha |-> ``:256``] unwrap_value_path_mem) >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          impl_tac >- simp[] >> strip_tac >>
          qexists_tac `u` >> simp[gas_marked_path_def]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`)
        (INST_TYPE [alpha |-> ``:256``] aggregate_unwrap_value_path_mem_capacity) >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      impl_tac >- simp[] >> strip_tac >> qexists_tac `u` >>
      simp[gas_marked_path_def] >> metis_tac[]) >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue t p` >>
  `p.ptr_location = LocMemory` by
    metis_tac[aggregate_unequal_post_result_location] >>
  `~is_word_type (post_value_type ce e)` by
    (`type_widens_to env.type_defs (post_value_type ce e) (expr_type e)` by
       metis_tac[post_value_type_widens, expr_body_pre_def] >>
     metis_tac[return_source_word_widens_eq]) >>
  `~is_word_type t` by
    (gvs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  qexists_tac `s` >> simp[gas_marked_path_def, cj 1 gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  metis_tac[immutable_rhs_noop_bounds, arithmeticTheory.ADD_COMM]
QED

Resume immutable_rhs_unwrap_mem_path[stack]:
  gvs[unwrap_value_def, comp_return_def] >>
  qexists_tac `s` >> simp[gas_marked_path_def, cj 1 gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
  metis_tac[immutable_rhs_noop_bounds, arithmeticTheory.ADD_COMM]
QED

Finalise immutable_rhs_unwrap_mem_path[local]

Theorem immutable_assign_rhs_outcome:
  expr_body_pre ce cx env e es /\ supported_expr tops e /\
  ce.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  FLOOKUP env.bare_globals (src,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME dtv /\
  expr_vv_sim_mem ctx func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,su) /\
  compile_assign_value ce (Lit (n2w off)) LocCode op (is_word_type ity)
    (vv_location vv) ity (lowered_value_type ce e)
    (type_memory_bytes ce ity) su = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm su func /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!ee v u.
    ee.gas_obs = [] /\
    (?gs pv. eval_expr cx e (es with gas_obs := gs) = (INL pv,ee) /\
             read_result cx pv ee = (INL v,ee)) /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func ce cx e es sa su s0 ee v op u) /\
    expr_store_bound cx (expr_type e) v op u /\
    (~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) ==>
     !w tv. eval_operand op u = SOME w /\
       evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==>
       type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= u.vs_alloca_next) /\
    value_runtime_typed env (lowered_value_type ce e) v /\
    expr_sim_inv ce cx env ee /\
    compile_assign_value ce (Lit (n2w off)) LocCode op (is_word_type ity)
      (vv_location vv) ity (lowered_value_type ce e)
      (type_memory_bytes ce ity) su = ((),sb) /\
    fn_has_code su sb func /\ ~u.vs_halted /\
    u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next ==>
    ?t. gas_marked_path T ctx func u 0 (OK t) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
      Q H (INL ()) (ee with immutables :=
        (cx.txn.target,set_source_immutables src
          (get_source_immutables src
            (case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m)
            |+ (id,(dtv,v)))
          (case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m)) ::
        ADELKEY cx.txn.target ee.immutables) t) /\
  (!H ex ee r. expr_exit (INR ex : eval_result + exception) r /\
             halt_exit H cx ee (INR ex : eval_result + exception) r ==>
             R H (INR ex) ee r) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx e)
      (\pv. do value <- read_result cx pv;
               place <- eval_target_place cx (TopLevelNameTarget (src,id));
               write_place cx place value od)) (es,s0) Q R
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by metis_tac[compile_expr_extends] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  match_mp_tac (Q.INST [`P` |-> `\H pv ee s.
    vv_post H ctx func ce cx e es sa sm s0 ee pv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee pv vv s /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next`]
    (SPEC_ALL forced_vv_then_outcome)) >>
  BETA_TAC >> rpt conj_tac
  >- (qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[])
  >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >>
      gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_write_place])
  >- (rpt gen_tac >> BETA_TAC >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
        (qx_choose_then `H0` assume_tac) >>
      qpat_x_assum `?gs. eval_expr cx e (es with gas_obs := gs) = (INL pv,ee)`
        (qx_choose_then `gs` assume_tac) >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H0` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      rename1 `vv_post H0 ctx func ce cx e es sa sm s0 ee pv vv t` >>
      `?v. read_result cx pv ee = (INL v,ee)` by
        (Cases_on `read_result cx pv ee` >>
         `r = ee` by metis_tac[read_result_state] >> gvs[] >>
         Cases_on `q` >> gvs[] >> metis_tac[vv_post_failed_read]) >>
      `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
        (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
        vv_post H ctx func ce cx e es sa sm s0 ee (Value v) vv t` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
           vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >>
         impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
         metis_tac[vv_post_read_result]) >>
      `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv t` by
        (fs[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]) >>
      mp_tac (Q.INST [`H0` |-> `H0`, `s` |-> `t`]
        (SPEC_ALL immutable_rhs_unwrap_mem_path)) >>
      impl_tac >- simp[] >> strip_tac >> suspend "suffix")
  >- (rpt strip_tac >> first_x_assum irule >> simp[])
QED

Resume immutable_assign_rhs_outcome[suffix]:
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `value_runtime_typed env (lowered_value_type ce e) v` by
    (qspecl_then [`ce`, `e`, `env`, `tops`, `cx`,
       `es with gas_obs := gs`, `v`, `ee`] mp_tac memory_rhs_read_lowered_typed >>
     simp[bind_def]) >>
  `expr_sim_inv ce cx env ee` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval_result] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `!ee v u. _` (qspecl_then [`ee`, `v`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  rename1 `gas_marked_path T ctx func u 0 (OK t_final)` >>
  `env_consistent env cx ee` by
    (`env_consistent env cx (es with gas_obs := gs)` by
       fs[expr_body_pre_def, expr_sim_inv_def] >>
     metis_tac[eval_expr_preserves_ec]) >>
  drule_all (immutable_assignment_source_tail |> SPEC_ALL |>
    Q.INST [`imms` |->
      `case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m`] |>
    SIMP_RULE bool_ss []) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Q _ (INL ()) fin _` >>
  `fin.storage_trace = ee.storage_trace` by simp[Abbr `fin`] >>
  qpat_assum `fin.storage_trace = ee.storage_trace`
    (fn eq => qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
      Q H (INL ()) fin t_final` (assume_tac o REWRITE_RULE [GSYM eq])) >>
  `fin with gas_obs := [] = fin` by
    simp[Abbr `fin`, evaluation_state_component_equality] >>
  qexistsl_tac [`INL ()`, `fin`, `OK t_final`] >>
  conj_tac >- simp[Abbr `fin`] >> simp[] >>
  irule (gas_marked_path_then |> SPEC_ALL |>
    Q.INST [`n` |-> `0`, `m` |-> `0`] |> REWRITE_RULE [ADD_0]) >>
  qexists_tac `u` >> simp[]
QED

Finalise immutable_assign_rhs_outcome
