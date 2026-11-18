Theory deploySymSrcConstructorArgs
Ancestors
  runtimeSymSrcModuleArgPreservation runtimeSymSrcPrimitives runtimeSymSrcContext
  runtimeSymSrcAbiDecode runtimeSymSrcAbiCalls runtimeSymSrcAbiArgGuard moduleLowering
  runtimeSymSrcInterfaces runtimeSymSrcEmission compileEnv finite_map
  loweringShapeDefs list stackPlanTypes

Theorem deploy_sym_register_constructor_args:
  !args ce off size s ce' s'. runtime_sym_env tops ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_constructor_args ce args off size s = (ce',s') ==>
    runtime_sym_env tops ce' /\ EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >> simp[compile_register_constructor_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_constructor_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >> simp[]
  >- metis_tac[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) runtime_sym_alloc_buffer >>
  disch_then drule >> strip_tac >>
  `runtime_sym_env tops (ce with ce_vars updated_by
      (\m. m |+ (h0,PtrVar buf.buf_operand x')))` by
    (irule runtime_sym_env_update >> simp[runtime_sym_loc_def]) >>
  drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) runtime_sym_decode_args_at >>
  disch_then (qspec_then `tops` mp_tac) >> simp[is_label_operand_def] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED
