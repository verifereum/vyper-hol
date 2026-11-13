(* Counted forcing of an allocated nonword memory buffer. *)
Theory exprSimBufferForce
Ancestors
  exprSimMemorySource exprSimUnwrapProps exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasPath fragGasMode exprLowering exprLoweringProps compileEnv
  vyperAST vyperInterpreter vyperState venomState list finite_map
Libs
  monadsyntax

(* Memory-buffer forcing uses only the oracle-clean memory boundary. *)
Theorem expr_sim_of_vv_sim_buffer:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa. ?t p sb. compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
      p.ptr_location = LocMemory /\ ~is_word_type t) /\
    (!tv es'. eval_expr cx e es = (INL tv,es') ==> ?v. tv = Value v) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `!tv es'. eval_expr _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!sa. ?t p sb. _` (qspec_then `sa` strip_assume_tac) >>
  drule_all lower_value_nonword_memory >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `LocatedValue t p`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (drule_all buffer_memory_marked_read >> strip_tac >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK t'`] >>
          simp[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED

