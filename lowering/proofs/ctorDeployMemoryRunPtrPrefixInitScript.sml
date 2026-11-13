(* Initialization boundaries independent of constructor decoding. *)
Theory ctorDeployMemoryRunPtrPrefixInit
Ancestors
  ctorDeployDefs ctorDeployLoweringDefs ctorDeployShape
  o1PassContract e2eEntry ptrDiscipline ptrSafeRun vyperCompiler
  venomState venomInst venomExecSemantics contextCodegenRel unitTransformDefs
  deployUnitProducers o1PipelineCorrect

Theorem deploy_ctor_lookup_unique:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func fn.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj,
     st_exit, st_epilogue, st_final, func) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  fn = func
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `deploy_ctor_code _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [deploy_ctor_code_def]) >>
  drule lower_vyper_deploy_unit_context_ok >>
  simp[lowering_context_ok_def, ctx_fn_names_def] >> strip_tac >>
  drule lookup_function_result_name >> strip_tac >>
  `MEM fn dunit.cu_context.ctx_functions` by
    metis_tac[lookup_function_MEM] >>
  metis_tac[distinct_function_names_unique]
QED

Theorem deploy_prefix_initial_allocations:
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = imm_len tops
Proof
  simp[gas_variant_def, deploy_entry_state_def, entry_venom_state_def,
       init_venom_state_def] >> strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `\s. (s.vs_allocas, s.vs_alloca_next)`) >> simp[]
QED

Theorem deploy_prefix_normalized_allocations:
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  let s = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>
  in s.vs_allocas = FEMPTY /\ s.vs_alloca_next = imm_len tops /\
     allocas_from (imm_len tops) s
Proof
  strip_tac >> drule deploy_prefix_initial_allocations >>
  simp[allocas_from_def]
QED

Theorem deploy_prefix_no_dalloca:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\ deploy_source_ok tops am tx ==>
  ~ctx_has_dalloca dunit.cu_context
Proof
  strip_tac >> drule_all deploy_unit_shape_ok >> strip_tac >>
  simp[o1_source_unit_ok_no_dalloca]
QED

val _ = export_theory();
