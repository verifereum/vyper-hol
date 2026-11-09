(* Seam 2 joint induction, a family leaf of the pure step: builtins other than array/tuple literals, and type builtins. *)
Theory bodyIntCallFamPureBuiltin
Ancestors
  bodyIntCallJointContract bodyIntCallJointPureCont exprSimProps
  exprSimSubscriptArrayCompose gasSummary fragGasMode exprSimHypsDefs
  stmtSimProps loweringPosts exprLoweringProps bodyIntCallJointPureSlot
  exprSimMain exprSimSource exprSimDefs stmtSimForLoop supportedExprTraverse
  bodyExprPreFacts exprSimBopRestWordBasics supportedExprs vyperAST
  exprOperandVar exprSimMapDefs vyperTypeSystem

Theorem pure_marked_vv_post_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  ~expr_has_effect e /\ sa.cs_next_var <= sb.cs_next_var /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s
    (ee with gas_obs := []) tv vv u /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx e)
    (es,s) marks res ee (OK u) /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s (ee with gas_obs := []) sb u
Proof
  strip_tac >>
  fs[gas_marked_exec_def, gas_marked_path_def] >>
  qpat_x_assum `!tail. _` (qspec_then `[]` assume_tac) >> fs[] >>
  `intcall_joint_res fp ce env
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) sa s` by
    (fs[intcall_joint_res_def, stmt_state_rel_def] >> metis_tac[]) >>
  `intcall_expr_cont fp ce env
     (es with gas_obs := gas_explicit marks s.vs_gas_readings)
     sa s (ee with gas_obs := []) sb u` by
    (irule pure_vv_post_cont >>
     simp[vv_post_initial_gas] >>
     conj_tac >- metis_tac[] >>
     qexistsl [`e`, `res`, `tv`, `vv`] >> simp[]) >>
  fs[intcall_expr_cont_def, locals_kept_def] >> metis_tac[]
QED

Theorem intcall_builtin_value_producer:
  ((?a b args. e = Builtin a b args /\ !t n. b <> MakeArray t n) \/
   (?a tb ty args. e = TypeBuiltin a tb ty args)) ==>
  intcall_expr_producer fp e
Proof
  disch_tac >> simp[intcall_expr_producer_def] >> rpt gen_tac >> strip_tac >>
  `supported_pure_expr fp.jc_tops e` by
    gvs[supported_expr_def, supported_effect_expr_def] >>
  `~expr_has_effect e` by metis_tac[supported_pure_expr_effect_free] >>
  `expr_sim_pre ce fp.jc_cx env e es` by
    (simp[expr_sim_pre_body] >> metis_tac[supported_pure_int_calls]) >>
  drule compile_expr_vv_sim >>
  disch_then (qspecl_then [`fp.jc_ctx`, `fp.jc_func`, `ty`] mp_tac) >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `vv`, `s`] mp_tac) >>
  impl_tac >- fs[intcall_joint_res_def] >>
  disch_then (fn th => irule gas_outcome_exec_conseq >> irule_at Any th) >>
  reverse conj_tac >- (rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[compile_expr_grows] >>
  `intcall_expr_cont fp ce env es sa s (mid with gas_obs := []) sb t` by
    (drule_all pure_marked_vv_post_cont >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    (drule (cj 1 compiler_compile_var) >>
     `local_ptrs_reserved ce sa` by fs[intcall_joint_res_def] >> simp[]) >>
  BETA_TAC >> qexists `tv` >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  asm_rewrite_tac[] >>
  rpt strip_tac >>
  `?v. read_result fp.jc_cx tv (mid with gas_obs := []) =
       (INL v,mid with gas_obs := [])` by
    (drule rest_word_vv_read_suffix >>
     disch_then (qx_choose_then `v` (qspec_then `[]` mp_tac)) >> simp[]) >>
  fs[intcall_expr_cont_def] >>
  gvs[post_value_type_def, expr_type_def, supported_pure_expr_def] >>
  fs[expr_body_pre_def] >>
  all_tac
  >~ [`well_typed_expr env (Builtin a b args)`] >-
    (drule_all joint_builtin_result_slot >> simp[]) >>
  drule_all joint_type_builtin_result_slot >> simp[]
QED

Theorem intcall_builtin_map_producer:
  ((?a b args. e = Builtin a b args /\ !t n. b <> MakeArray t n) \/
   (?a tb ty args. e = TypeBuiltin a tb ty args)) ==>
  intcall_map_producer fp e
Proof
  strip_tac >>
  gvs[intcall_map_producer_def, expr_map_pre_def, well_typed_expr_def]
QED

Theorem intcall_pure_builtin_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?a b args. e = Builtin a b args /\ !t n. b <> MakeArray t n) \/
   (?a tb ty args. e = TypeBuiltin a tb ty args)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  metis_tac[intcall_builtin_value_producer, intcall_builtin_map_producer]
QED
