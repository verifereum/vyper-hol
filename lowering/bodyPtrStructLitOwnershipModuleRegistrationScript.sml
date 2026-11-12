Theory bodyPtrStructLitOwnershipModuleRegistration
Ancestors
  bodyPtrStructLitOwnershipAbiDecode bodyPtrStructLitOwnershipAbiStatic
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  moduleLowering compileEnv bodyPtrStructLitOwnershipPrimitives
  loweringShapeProps loweringShapeDefs bodyPtrStructLitOwnershipShape

Theorem alloc_run_compile_decode_args:
  !args ce offset opc hi base.
    alloc_run fresh_outputs (compile_decode_args ce args offset opc hi base)
      (\u s. fresh_outputs s)
Proof
  Induct
  >- simp[compile_decode_args_def, comp_return_def,
          alloc_run_def, alloc_frame_refl] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_decode_args_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  TRY (rename1 `SOME loc` >>
       Cases_on `var_location_decode_operand loc` >> simp[]) >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
            SRULE [SF ETA_ss] alloc_run_compile_abi_decode_to_buf,
            SRULE [SF ETA_ss] alloc_run_compile_abi_clamp_basetype] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
  fs[SF ETA_ss] >>
  Cases_on `h4` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_abi_clamp_basetype]
QED

Theorem alloc_run_compile_register_positional_args:
  !args ce offset.
    alloc_run fresh_outputs (compile_register_positional_args ce args offset)
      (\ce' s. fresh_outputs s)
Proof
  Induct
  >- simp[compile_register_positional_args_def, comp_return_def,
          alloc_run_def, alloc_frame_refl] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[] >>
  Cases_on `var_location_memory_size x` >> simp[] >>
  simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
            SRULE [SF ETA_ss] alloc_run_compile_decode_args] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
  fs[SF ETA_ss]
QED

Theorem compile_register_positional_args_alloca_locals:
  !args ce offset st ce' st'.
    compile_register_positional_args ce args offset st = (ce',st') ==>
    ce'.ce_alloca_locals = ce.ce_alloca_locals
Proof
  Induct
  >- simp[compile_register_positional_args_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
  >- metis_tac[] >>
  Cases_on `var_location_memory_size x` >> simp[]
  >- metis_tac[] >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem alloc_run_compile_register_positional_args_mode[local]:
  alloc_run fresh_outputs (compile_register_positional_args ce args offset)
    (\ce' s. fresh_outputs s /\ ce'.ce_alloca_locals = ce.ce_alloca_locals)
Proof
  mp_tac (Q.SPECL [`args`, `ce`, `offset`]
    alloc_run_compile_register_positional_args) >>
  simp[alloc_run_def] >>
  metis_tac[compile_register_positional_args_alloca_locals]
QED

Theorem alloc_run_compile_register_positional_args_shape:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_register_positional_args ce args offset)
    (\ce' s. shape_state s /\ cenv_shape_ok s ce' /\
      ce'.ce_return_pc = ce.ce_return_pc /\
      ce'.ce_alloca_locals = ce.ce_alloca_locals)
Proof
  irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any compile_register_positional_args_shape >>
  irule_at Any alloc_run_compile_register_positional_args_mode >>
  simp[shape_state_def] >> metis_tac[shape_base_fresh_outputs]
QED
