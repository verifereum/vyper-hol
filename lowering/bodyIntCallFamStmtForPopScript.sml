(* Resource transport when an iteration scope is popped. *)
Theory bodyIntCallFamStmtForPop
Ancestors
  bodyIntCallJointContract bodySim compileEnv stmtSimProps exprLoweringProps
  loweringPosts intCallFrame bodyMemoryDefs venomState venomExecSemantics finite_map

(* The source typing invariant is supplied by the source scope boundary. *)
Theorem intcall_joint_res_pop_top_ext:
  intcall_joint_res fp ce' env' es sa s /\
  cenv_top_ext ce ce' es.scopes /\ es.scopes = sc :: rest /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  expr_sim_inv ce fp.jc_cx env (es with scopes := rest) /\
  ce_locals_declared ce env /\ locals_alloc_ok ce env /\
  local_ptrs_reserved ce sa ==>
  intcall_joint_res fp ce env (es with scopes := rest) sa s
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx
    (es with scopes := rest) s` by
    (irule stmt_state_rel_pop_top_ext >>
     fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `!n. lookup_scopes n rest <> NONE ==>
       FLOOKUP ce'.ce_vars n = FLOOKUP ce.ce_vars n` by
    (fs[cenv_top_ext_def] >> metis_tac[]) >>
  `ce'.ce_return_pc = ce.ce_return_pc /\
   ce'.ce_return_buf = ce.ce_return_buf /\
   ce'.ce_module_vars = ce.ce_module_vars /\
   ce'.ce_module = ce.ce_module /\ ce'.ce_is_ctor = ce.ce_is_ctor` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >> simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!n p k. local_region ce' _ _ _ _ _ ==> _` irule >>
      qexists_tac `n` >>
      irule local_region_pop_scope >> goal_assum (drule_at Any) >>
      fs[local_region_def] >> metis_tac[])
  >- (fs[ret_pc_ok_def])
  >- (Cases_on `fp.jc_rb` >> fs[return_buf_frame_def] >>
      rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >>
      fs[return_buf_frame_def])
  >- (fs[same_frame_def, cenv_top_ext_def, compile_env_component_equality] >>
      metis_tac[]) >>
  metis_tac[]
QED
