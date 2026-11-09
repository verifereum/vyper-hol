(* Seam 2 joint induction, a family leaf of the pure step: names, top-level names, flag members and literals. *)
Theory bodyIntCallFamPureAtom
Ancestors
  bodyIntCallJointContract bodyIntCallJointPureCont bodyIntCallJointPureSlot
  exprSimWordArgs exprSimHypsDefs loweringPosts stmtSimProps compileEnv
  exprSimDefs exprSimAggregateSource exprLoweringProps exprOperandVar
  gasOutcome gasSummary fragGasMode exprSimNameValue exprSimTopLevel
  exprSimFlagWord exprSimLeaves exprSimHyps exprLowering supportedExprTraverse
  supportedExprs exprSimSource exprSimSubscriptMap vyperTypeSystem
  vyperStoragePlaceProvenance exprSimMapDefs vyperState context

Theorem joint_res_gas_obs[simp]:
  intcall_joint_res fp ce env (es with gas_obs := gs) sa s <=>
  intcall_joint_res fp ce env es sa s
Proof
  simp[intcall_joint_res_def, local_region_def]
QED


Theorem pure_vv_observed_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  ~expr_has_effect e /\
  eval_expr fp.jc_cx e (es with gas_obs := gs) = (res,ee) /\
  sa.cs_next_var <= sb.cs_next_var /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sb s ee tv vv u /\
  gas_path fp.jc_ctx fp.jc_func s n (OK u) /\
  u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  intcall_expr_cont fp ce env es sa s ee sb u
Proof
  strip_tac >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx e
     (es with gas_obs := gs) sa sb s ee tv vv u` by
    (fs[vv_post_def, locals_kept_def] >> metis_tac[]) >>
  `intcall_joint_res fp ce env (es with gas_obs := gs) sa s` by simp[] >>
  drule_all pure_vv_post_cont >>
  simp[intcall_expr_cont_def, locals_kept_def] >> metis_tac[]
QED

Theorem intcall_pure_nonconditional_producer:
  (!ce. expr_vv_ok ce e) /\ int_calls_expr e = [] /\
  (!tops. supportedExprs$supported_expr tops e ==>
          supportedExprs$supported_pure_expr tops e) /\
  (!ann elem bd args. e <> Builtin ann (MakeArray elem bd) args) /\
  (!ann c a b. e <> IfExp ann c a b) /\
  (!ann id fields. e <> StructLit ann id fields) /\
  (!ann obj fld. e <> Attribute ann obj fld) /\
  (!ann obj idx. e <> Subscript ann obj idx) ==>
  intcall_expr_producer fp e
Proof
  strip_tac >> rw[intcall_expr_producer_def] >>
  `expr_sim_pre ce fp.jc_cx env e es` by
    fs[expr_sim_pre_def, expr_body_pre_def] >>
  `expr_vv_sim fp.jc_ctx fp.jc_func ce fp.jc_cx ty e es` by
    metis_tac[expr_vv_ok_def] >>
  `local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_joint_res_def] >>
  `supportedExprs$supported_pure_expr fp.jc_tops e` by metis_tac[] >>
  `~expr_has_effect e` by metis_tac[supported_pure_expr_effect_free] >>
  `sa.cs_next_var <= sb.cs_next_var` by metis_tac[compile_expr_grows] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[compiler_compile_var] >>
  fs[expr_vv_sim_def] >>
  first_x_assum (qspecl_then [`sa`, `sb`, `vv`, `s`] mp_tac) >>
  simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  strip_tac >> qexists `marks`
  >~ [`vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`] >- (
  gvs[] >>
  `gas_path fp.jc_ctx fp.jc_func s (LENGTH marks) (OK t)` by
    fs[gas_marked_exec_def, gas_marked_path_def] >>
  `eval_expr fp.jc_cx e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
     (INL tv, es_end with gas_obs := [])` by
    (fs[gas_marked_exec_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `intcall_expr_cont fp ce env es sa s
     (es_end with gas_obs := []) sb t` by
    (drule_all pure_vv_observed_cont >> simp[]) >>
  drule vv_post_materialises >> strip_tac >>
  disj1_tac >> qexistsl [`INL tv`, `es_end`, `OK t`] >> simp[] >>
  gvs[vv_post_def, post_value_type_no_calls] >>
  rpt strip_tac >>
  irule (SRULE [arithmeticTheory.ADD_SYM] joint_nonconditional_result_slot) >>
  simp[] >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  simp[post_value_type_no_calls] >>
  fs[intcall_expr_cont_def, expr_body_pre_def] >>
  metis_tac[joint_res_gas_obs]) >>
  metis_tac[]
QED

Theorem intcall_pure_atom_expr:
  intcall_expr_producer fp (Name ann x) /\
  intcall_expr_producer fp (TopLevelName ann id) /\
  intcall_expr_producer fp (FlagMember ann id mid) /\
  intcall_expr_producer fp (Literal ann lit)
Proof
  rpt conj_tac >> irule intcall_pure_nonconditional_producer >>
  simp[vyperTypeCallGraphTheory.int_calls_expr_def, supported_pure_expr_def,
       supported_expr_def, supported_effect_expr_def, compile_name_vv_sim, compile_toplevel_name_sim, compile_flag_member_sim] >>
  metis_tac[compile_literal_case_sim, expr_ok_def]
QED

Theorem intcall_toplevel_map_producer:
  intcall_map_producer fp (TopLevelName ann (src,id))
Proof
  rw[intcall_map_producer_def] >>
  `env_consistent env fp.jc_cx es /\
   ?kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt)` by
    gvs[expr_map_pre_def, expr_sim_inv_def, well_typed_expr_def, AllCaseEqs()] >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout fp.jc_cx tr src id_str = SOME slot` >>
  drule_all lookup_global_mapping >> strip_tac >>
  `storage_mapping_region fp.jc_cx tr (n2w slot) (HashMapT kt vt)` by
    (irule lookup_global_mapping_region >> qexistsl [`src`, `es`, `es`, `id`] >> simp[]) >>
  `storage_vars_rel ce fp.jc_cx /\ transient_vars_rel ce fp.jc_cx` by
    gvs[intcall_joint_res_def, stmt_state_rel_def, state_rel_def] >>
  drule_at (Pat `find_var_decl_by_name _ _ = _`) toplevel_storage_ce_vars_decl >>
  simp[var_decl_transient_def] >> disch_then drule_all >> strip_tac >>
  `compile_expr ce ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
        (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, vyperASTTheory.expr_type_def]) >>
  gvs[] >> rewrite_tac[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL (HashMapRef tr (n2w slot) kt vt)`, `es`, `OK s`] >>
  conj_tac >- (irule toplevel_mapping_marked_exec >> simp[]) >>
  disj1_tac >> simp_tac std_ss [] >> qexists `s` >> simp_tac std_ss [] >>
  qexistsl [`tr`, `n2w slot`, `kt`, `vt`] >>
  simp[slot_loc_def, mk_ptr_def, venomStateTheory.eval_operand_def] >>
  simp[intcall_expr_cont_def, locals_kept_def]
QED

Theorem intcall_pure_atom_map:
  intcall_map_producer fp (Name ann x) /\
  intcall_map_producer fp (TopLevelName ann id) /\
  intcall_map_producer fp (FlagMember ann id mid) /\
  intcall_map_producer fp (Literal ann lit)
Proof
  rpt conj_tac
  >- simp[intcall_map_producer_def, expr_map_pre_def, well_typed_expr_def]
  >- (Cases_on `id` >> simp[intcall_toplevel_map_producer])
  >> simp[intcall_map_producer_def, expr_map_pre_def, well_typed_expr_def]
QED

Theorem intcall_pure_atom_step:
  (!e'. expr_size e' < expr_size e ==>
        intcall_expr_producer fp e' /\ intcall_forced_producer fp e' /\
        intcall_map_producer fp e') /\
  ((?ty x. e = Name ty x) \/ (?ty n. e = TopLevelName ty n) \/
   (?ty n m. e = FlagMember ty n m) \/ (?ty l. e = Literal ty l)) ==>
  intcall_expr_producer fp e /\ intcall_map_producer fp e
Proof
  strip_tac >> gvs[] >>
  metis_tac[intcall_pure_atom_expr, intcall_pure_atom_map]
QED
