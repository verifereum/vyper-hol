(* Counted forcing of a value already located in memory. *)
Theory exprSimMemoryForce
Ancestors
  exprSimMemorySource exprSimMemoryPath exprSimMemoryRead
  exprSimUnwrapProps exprSimProps exprSimDefs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasPath fragGasMode emitHelperProps loweringPosts
  exprLowering exprLoweringProps compileEnv loweringSlice
  list rich_list finite_map pred_set fragExec varsExt freshWrites
  vyperAST vyperInterpreter vyperState vyperTypeSystem valueEncoding
  valueEncodingProofs venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem expr_sim_of_vv_sim_memory:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa vv sm. compile_expr cenv ty e sa = (vv, sm) ==>
                sm = sa /\
                ?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `!sa vv sm. compile_expr _ _ _ _ = _ ==> _` drule >>
  strip_tac >> gvs[] >>
  drule_all unwrap_memory_extends >> strip_tac >>
  `fn_has_code sa sa func` by
    (irule (cj 1 fn_has_code_split) >> simp[cs_extends_refl] >>
     qexists_tac `sb` >> simp[]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sa`, `LocatedValue t p`, `s0`] mp_tac) >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (`~t'.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
          drule_all unwrap_memory_marked_read >> simp[] >> strip_tac >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u`] >>
          simp[] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
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

