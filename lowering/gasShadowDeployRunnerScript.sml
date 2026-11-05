(* Proof-only raw deploy runner boundary. *)
Theory gasShadowDeployRunner
Ancestors
  gasShadowDeploy gasShadowUnitExtract gasShadowUnitGuards
  gasShadowUnit gasShadowState gasShadowModuleDefs gasShadow
  vyperCompiler moduleLowering compileEnv venomCompilerTypes list

Theorem gas_shadow_deploy_final_state:
  !has bytes imm args size ints ce stmts pay nr key trans s.
  gas_shadow_state
    (SND (compile_generate_deploy has bytes imm args size ints ce stmts pay nr key trans s))
    (SND (compile_generate_deploy has bytes imm args size
      (MAP gas_shadow_internal_package ints) ce (MAP gas_shadow_stmt stmts) pay nr key trans s))
Proof
  rpt gen_tac >> irule (cj 2 (REWRITE_RULE [gas_shadow_compiles_def] gas_shadow_compile_generate_deploy)) >>
  simp[gas_shadow_state_refl]
QED

Theorem gas_shadow_run_deploy_lowering:
  !has rp bytes imm args size ints ce stmts pay nr key trans entry.
  OPTREL gas_shadow_unit
    (run_deploy_lowering has rp bytes imm args size ints ce stmts pay nr key trans entry)
    (run_deploy_lowering has rp bytes imm args size
      (MAP gas_shadow_internal_package ints) ce (MAP gas_shadow_stmt stmts) pay nr key trans entry)
Proof
  rpt gen_tac >> simp[run_deploy_lowering_def] >>
  Cases_on `lowering_policy_ok rp` >> simp[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `gas_shadow_state st1 st1'` by
    (qpat_x_assum `_ = ((),st1)` (fn th => once_rewrite_tac[GSYM (SRULE [] (Q.AP_TERM `SND` th))]) >>
     qpat_x_assum `_ = ((),st1')` (fn th => once_rewrite_tac[GSYM (SRULE [] (Q.AP_TERM `SND` th))]) >>
     irule gas_shadow_deploy_final_state) >>
  `OPTREL (\(c,d) (c',d'). gas_shadow_context c c' /\ d = d')
    (extract_context_with_internals entry ints st1)
    (extract_context_with_internals entry (MAP gas_shadow_internal_package ints) st1')`
    by metis_tac[gas_shadow_extract_context_with_internals] >>
  Cases_on `extract_context_with_internals entry ints st1` >>
  Cases_on `extract_context_with_internals entry (MAP gas_shadow_internal_package ints) st1'` >>
  gvs[] >> PairCases_on `x` >> PairCases_on `x'` >> gvs[] >>
  drule gas_shadow_install_immutable_reservation >>
  disch_then (qspec_then `imm` assume_tac) >>
  drule gas_shadow_lowering_context_ok >> strip_tac >>
  drule gasShadowUnitObservationsTheory.gas_shadow_unit_alloca_budget >>
  strip_tac >>
  `!c d. gas_shadow_context c d ==>
         FILTER (\i. i.inst_opcode = DLOAD) (FLAT (MAP fn_insts c.ctx_functions)) =
         FILTER (\i. i.inst_opcode = DLOAD) (FLAT (MAP fn_insts d.ctx_functions))`
    by (rpt strip_tac >> irule gas_shadow_functions_filter_opc >> simp[] >>
        fs[gas_shadow_context_def]) >>
  pop_assum (fn th => drule th) >> strip_tac >>
  gvs[] >> Cases_on `lowering_context_ok (install_immutable_reservation imm x'0)` >>
  simp[gas_shadow_unit_def] >> IF_CASES_TAC >> simp[gas_shadow_unit_def]
QED
