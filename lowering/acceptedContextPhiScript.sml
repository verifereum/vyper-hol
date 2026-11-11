(* The acceptance check, independent of any particular compiler start. *)
Theory acceptedContextPhi
Ancestors vyperCompiler compileVyper venomInst venomExecProofs fragExec ptrDiscipline list

Theorem lowering_context_ok_block_phi:
  lowering_context_ok ctx /\ ~ctx_has_dalloca ctx /\
  lookup_function nm ctx.ctx_functions = SOME fn /\
  lookup_block label fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> irule no_phis_phi_prefix_length_zero >>
  drule lookup_function_MEM >> strip_tac >>
  fs[lowering_context_ok_def, ptr_ok_check_def, ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >>
  metis_tac[lookup_block_fn_insts]
QED

Theorem lower_vyper_runtime_unit_block_phi:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  ~ctx_has_dalloca unit.cu_context /\
  lookup_function nm unit.cu_context.ctx_functions = SOME fn /\
  lookup_block label fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> irule lowering_context_ok_block_phi >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  pairarg_tac >> simp[AllCaseEqs()] >>
  metis_tac[run_lowering_context_ok]
QED
