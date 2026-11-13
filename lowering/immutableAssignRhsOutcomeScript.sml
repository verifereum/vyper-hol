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
  vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv s /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    expr_post ctx func ce cx e es sa su s0 ee v op u /\
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
          drule_at (Pat `unwrap_value _ _ _ = _`) unwrap_value_path_mem >>
          disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          impl_tac >- simp[] >> strip_tac >>
          qexists_tac `u` >> simp[gas_marked_path_def]) >>
      drule_at (Pat `unwrap_value _ _ _ = _`) aggregate_unwrap_value_path_mem_capacity >>
      disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
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
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!ee v u.
    ee.gas_obs = [] /\
    (?gs pv. eval_expr cx e (es with gas_obs := gs) = (INL pv,ee) /\
             read_result cx pv ee = (INL v,ee)) /\
    expr_post ctx func ce cx e es sa su s0 ee v op u /\
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
      Q (INL ()) (ee with immutables :=
        (cx.txn.target,set_source_immutables src
          (get_source_immutables src
            (case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m)
            |+ (id,(dtv,v)))
          (case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m)) ::
        ADELKEY cx.txn.target ee.immutables) t) /\
  (!ex ee r. expr_exit (INR ex : eval_result + exception) r ==>
             R (INR ex) ee r) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
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
  irule forced_vv_then_outcome >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `\pv ee s.
    vv_post ctx func ce cx e es sa sm s0 ee pv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee pv vv s /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next` >>
  reverse conj_tac
  >- (qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[]) >>
  rpt gen_tac >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  rename1 `vv_post ctx func ce cx e es sa sm s0 ee pv vv t` >>
  `?v. read_result cx pv ee = (INL v,ee)` by
    (Cases_on `read_result cx pv ee` >>
     `r = ee` by metis_tac[read_result_state] >> gvs[] >>
     Cases_on `q` >> gvs[] >> metis_tac[vv_post_failed_read]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `vv_post ctx func ce cx e es sa sm s0 ee (Value v) vv t` by
    metis_tac[vv_post_read_result] >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) vv t` by
    (fs[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]) >>
  drule_at (Pat `unwrap_value _ _ _ = _`) immutable_rhs_unwrap_mem_path >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ (Value v) _ _`)) >>
  disch_then (qspec_then `env` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> suspend "suffix"
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
  `env_consistent env cx ee` by
    (`env_consistent env cx (es with gas_obs := gs)` by
       fs[expr_body_pre_def, expr_sim_inv_def] >>
     metis_tac[eval_expr_preserves_ec]) >>
  drule_all (immutable_assignment_source_tail |> SPEC_ALL |>
    Q.INST [`imms` |->
      `case ALOOKUP ee.immutables cx.txn.target of NONE => [] | SOME m => m`] |>
    SIMP_RULE bool_ss []) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `Q (INL ()) fin t'` >>
  `fin with gas_obs := [] = fin` by
    simp[Abbr `fin`, evaluation_state_component_equality] >>
  qexistsl_tac [`INL ()`, `fin`, `OK t'`] >>
  conj_tac >- simp[Abbr `fin`] >> simp[] >>
  irule (gas_marked_path_then |> SPEC_ALL |>
    Q.INST [`n` |-> `0`, `m` |-> `0`] |> REWRITE_RULE [ADD_0]) >>
  qexists_tac `u` >> simp[]
QED

Finalise immutable_assign_rhs_outcome
