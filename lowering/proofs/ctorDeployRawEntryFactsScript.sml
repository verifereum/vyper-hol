(* Structural, headroom and layout boundaries for raw deployment entries. *)
Theory ctorDeployRawEntryFacts
Ancestors
  ctorDeployDefs ctorDeployShape ctorDeployImmBudget ctorDeployMemoryFrontier
  ctorDeployInitcode ctorDeployInitcodeAsm ctorDeployDefsReach deployUnitProducers
  acceptedContextPhi ptrOkCheck o1PipelineCompose o1PipelineCorrect
  codegenEncodingWf immutableCodeLayout asmWf ctorDeployLoweringReturn asmOptimizer
  e2eDeployDefs e2eEntry lowerDloadDefs unitShapeDefs vyperCompiler list arithmetic

Theorem deploy_raw_entry_context_facts:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx ==>
  lowering_context_ok dunit.cu_context /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) dunit.cu_context.ctx_functions /\
  EVERY (\f.
    fn_ptr_ok (\nm. set (ctx_ptr_param_list dunit.cu_context nm)) f /\
    fn_ptr_ok (\nm. set (ctx_ptr_param_list dunit.cu_context nm)) (reachable_fn f))
    dunit.cu_context.ctx_functions /\
  reserved_intervals_wf dunit.cu_context.ctx_global_reserved /\
  EVERY (\f. f.fn_eom = NONE) dunit.cu_context.ctx_functions /\
  ~ctx_has_dalloca dunit.cu_context /\
  fmp_free_ctx dunit.cu_context /\
  fixed_region_reserved (imm_len tops) dunit.cu_context
Proof
  strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  `lowering_context_ok dunit.cu_context` by
    (irule lower_vyper_deploy_unit_context_ok >>
     fs[deploy_phases_def] >> metis_tac[]) >>
  `fmp_free_ctx dunit.cu_context` by metis_tac[source_fmp_free] >>
  `ptr_ok_check dunit.cu_context` by fs[lowering_context_ok_def] >>
  drule ptr_ok_check_sound >> strip_tac >>
  fs[lowering_context_ok_def, EVERY_MEM]
QED

Theorem deploy_raw_entry_mem_inv:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  vs.vs_alloca_next = imm_len tops ==>
  mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  strip_tac >>
  drule_all deploy_raw_entry_context_facts >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `dunit.cu_context.ctx_entry = SOME "__deploy" /\
   ?fn. lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn` by
    (irule lower_vyper_deploy_unit_entry >> fs[deploy_phases_def] >> metis_tac[]) >>
  irule lowered_unit_dload_headroom_ok_from >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem deploy_raw_entry_no_phi:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  lookup_function nm dunit.cu_context.ctx_functions = SOME fn /\
  lookup_block label fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  drule_all deploy_raw_entry_context_facts >> strip_tac >>
  irule lowering_context_ok_block_phi >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
  >> (metis_tac[])
QED

Theorem deploy_raw_entry_code_layout:
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  deploy_source_ok tops am tx ==>
  code_layout_valid
    ((opt_deploy_entry_state_own prog prog' cplan tops es) with
      <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
Proof
  strip_tac >> drule_all deploy_relocated_data_layout >> strip_tac >>
  `?args_bytes.
     (FST (HD es.contexts)).msgParams.code = assemble prog' ++ args_bytes /\
     constructor_args_encode tops tx args_bytes` by
    fs[deploy_state_rel_def] >>
  drule_all constructor_args_size_bounded >> strip_tac >>
  simp[code_layout_valid_def, opt_deploy_entry_state_own_def, opt_entry_state_own_def,
       entry_venom_state_frame_fields, finite_mapTheory.FLOOKUP_o_f,
       rich_listTheory.DROP_LENGTH_APPEND, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
  qpat_assum `LENGTH args_bytes < 2 ** 128`
    (assume_tac o REWRITE_RULE [EVAL ``2 ** 128 : num``]) >>
  decide_tac
QED
