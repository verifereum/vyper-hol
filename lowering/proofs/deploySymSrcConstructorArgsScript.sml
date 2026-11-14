Theory deploySymSrcConstructorArgs
Ancestors
  runtimeSymSrcModuleArgPreservation runtimeSymSrcPrimitives runtimeSymSrcContext
  runtimeSymSrcAbiDecode runtimeSymSrcAbiCalls runtimeSymSrcAbiArgGuard moduleLowering
  runtimeSymSrcInterfaces runtimeSymSrcEmission compileEnv finite_map
  loweringShapeDefs list stackPlanTypes

Theorem deploy_sym_decode_args:
  !args off s u s'.
  runtime_sym_env ce /\ opc <> CODESIZE /\ opc <> CODECOPY /\
  ~is_label_operand hi /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_decode_args ce args off opc hi adj s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct
  >- (simp[compile_decode_args_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> Cases_on `h1` >>
  simp[Once compile_decode_args_def, comp_bind_def, comp_ignore_bind_def]
  >- (rpt (pairarg_tac >> simp[]) >> strip_tac >>
      qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[is_label_operand_def] >> strip_tac >>
      qpat_assum `emit_op opc _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[] >> strip_tac >>
      drule_all runtime_sym_abi_clamp_basetype >> strip_tac >>
      `EVERY runtime_sym_inst (state_insts cs'⁴')` by
        (Cases_on `FLOOKUP ce.ce_vars h0` >> gvs[comp_return_def] >>
         Cases_on `var_location_decode_operand x` >> gvs[comp_return_def] >>
         `~is_label_operand x'` by metis_tac[runtime_sym_decode_operand] >>
         qpat_assum `emit_void _ _ _ = _`
           (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
      metis_tac[]) >>
  Cases_on `h2` >> simp[] >>
  (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
   >- (strip_tac >> metis_tac[])) >>
  (Cases_on `var_location_decode_operand x` >> simp[]
   >- (strip_tac >> metis_tac[])) >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `~is_label_operand x'` by metis_tac[runtime_sym_decode_operand] >>
  rpt (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
       simp[is_label_operand_def] >> strip_tac) >>
  all_tac >~ [`compile_abi_arg_ptr_guard _ _ _ _ = _`] >-
   (drule_at (Pat `compile_abi_arg_ptr_guard _ _ _ _ = _`)
      runtime_sym_abi_arg_ptr_guard >>
    simp[is_label_operand_def] >> strip_tac >>
    qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
      (mp_then Any mp_tac runtime_sym_abi_decode_to_buf) >>
    simp[is_label_operand_def, COND_RAND] >> strip_tac >>
    first_x_assum drule_all >> simp[]) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_abi_decode_to_buf) >>
  simp[is_label_operand_def, COND_RAND] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem deploy_sym_register_constructor_args:
  !args ce off size s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_constructor_args ce args off size s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')
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
  `runtime_sym_env (ce with ce_vars updated_by
      (\m. m |+ (h0,PtrVar buf.buf_operand x')))` by
    (irule runtime_sym_env_update >> simp[runtime_sym_loc_def]) >>
  drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) deploy_sym_decode_args >>
  simp[is_label_operand_def] >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED
