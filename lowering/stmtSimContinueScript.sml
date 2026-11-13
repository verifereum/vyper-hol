(* Counted actual-source simulation for a loop continue. *)
Theory stmtSimContinue
Ancestors
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasContext fragGasMode
  gasCount fragGasPath stmtLowering compileEnv emitHelper emitHelperProps loweringSlice
  exprLoweringProps vyperInterpreter vyperState venomInst venomState
  venomExecSemantics venomExecProofs fragExec list finite_map
Libs
  monadsyntax


Theorem continue_jump_post:
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\ ~s.vs_halted ==>
  stmt_post H ctx func cx (InLoop ex inc) cenv cenv sa sb es s
    (INR ContinueException) (es with gas_obs := []) (jump_to inc s)
Proof
  strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s.vs_gas_readings`, `s.vs_inst_idx`, `[]`] mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  pure_rewrite_tac[stmt_post_def] >> qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, stmt_state_rel_jump_to, alloca_frame_same,
       jump_to_def, lookup_var_def] >>
  `!b. get_storage cx (es with gas_obs := []) b = get_storage cx es b` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  fs[vyperStorageFootprintTheory.storage_well_formed_on_def]
QED

Theorem compile_continue_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Continue)
      (eval_stmt cx Continue) es
Proof
  rw[stmt_frag_def, stmt_framed_frag_def, stmt_env_def,
     declare_stmt_local_def, comp_bind_def, comp_return_def] >>
  qpat_x_assum `_ sa = (cenv', sb)` mp_tac >>
  simp[comp_ignore_bind_def, comp_bind_def, compile_stmt_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_inst _ _ _ sa = (_, sj)` >>
  drule emit_inst_extends >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  pure_rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR ContinueException`, `es`, `OK (jump_to inc s0)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, Once evaluate_def,
           raise_def] >> irule emit_jump_zero_path >> simp[] >>
      qexistsl_tac [`sa`, `sj`] >> simp[]) >>
  simp[fragExecTheory.exit_result_def] >>
  rpt strip_tac >> irule continue_jump_post >> gs[]
QED

