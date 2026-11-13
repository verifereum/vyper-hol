(* Memory case of the body induction (bodyMemory's body_mem_mutual): raw_log. *)
Theory bodyMemRawLog
Ancestors
  exprSimMemoryStack bodySimCallRawLog bodySimRawLogBodySource exprSimMemDefs
  exprLowering vyperInterpreter vyperValue vyperAST vyperState
  bodyMemoryPreds bodyMemRawLogExecution bodyMemRawLogTopics bodyMemRawLogStages bodyMemRawLogCompose bodyMemRawLogFragments

Theorem body_raw_log_mem_case:
  !cx v20 es v21.
    body_exprs_mem_ok cx es ==> body_expr_mem_ok cx (Call v20 RawLog es v21)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_mem ctx func cenv cx ty (Call v20 RawLog es v21) es'` by
    (simp[expr_sim_mem_def] >> rpt strip_tac >>
     drule_all raw_log_body_lower_value >> strip_tac >> gvs[] >>
     simp[expr_type_def, expr_store_bound_none] >>
     drule raw_log_body_pre_shape >> strip_tac >>
     gvs[expr_type_def, expr_store_bound_none]
     >- (irule raw_log_fixed32_frag_mem >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     irule raw_log_dynamic_frag_mem >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule body_expr_vv_sim_mem_stack >>
  conj_tac >- (drule raw_log_body_compile_stack >> metis_tac[]) >>
  reverse conj_tac
  >- (drule raw_log_body_pre_shape >> strip_tac >>
      gvs[expr_type_def, lowered_value_type_def, evaluate_type_def,
          valueEncodingTheory.type_memory_size_def]) >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def,
       lift_option_type_def, type_check_def, check_not_static_def,
       assert_def, raise_def, push_log_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
