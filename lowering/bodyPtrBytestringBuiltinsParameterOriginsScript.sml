(* Parameter entry prefixes preserve chronological allocation origins. *)
Theory bodyPtrBytestringBuiltinsParameterOrigins
Ancestors
  bodyPtrBytestringBuiltinsAllocationDeltas
  bodyPtrBytestringBuiltinsAllocationOrigins
  bodyPtrBytestringBuiltinsParameterAges moduleLowering intCallCallee
  loweringShapeDefs emitHelper compileEnv list venomInst

Theorem materialize_internal_params_allocation_delta:
  !caps ce sa ce' sb.
  materialize_internal_params ce caps sa = (ce',sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  Induct_on `caps`
  >- (simp[materialize_internal_params_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- metis_tac[] >>
      Cases_on `x` >> simp[]
      >- (simp[comp_bind_def, comp_ignore_bind_def] >>
          rpt (pairarg_tac >> gvs[]) >> strip_tac >>
          drule emit_op_allocation_delta >> strip_tac >>
          drule emit_void_allocation_delta >> strip_tac >>
          first_x_assum drule >> strip_tac >>
          conj_tac >- simp[] >>
          qexists_tac `delta ++ delta' ++ delta''` >>
          simp[APPEND_ASSOC] >>
          irule alloca_output_interval_append >>
          qexists_tac `cs''.cs_next_var` >> simp[] >>
          irule alloca_output_interval_append >>
          qexists_tac `cs'.cs_next_var` >> simp[]) >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem internal_param_decls_allocation_free_delta:
  !ps idx sa caps next sb.
  compile_internal_param_decls ps idx sa = ((caps,next),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          (!i. MEM i delta ==> i.inst_opcode <> ALLOCA)
Proof
  Induct_on `ps`
  >- (simp[compile_internal_param_decls_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `[]` >> simp[]) >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_internal_param_decls_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  PairCases_on `rest_result` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  qexists_tac `[mk_inst sa.cs_next_id PARAM [Lit (n2w idx)]
                 [STRING #"%" (toString sa.cs_next_var)]] ++ delta` >>
  simp[state_insts_def, all_blocks_def, FLAT_APPEND, APPEND_ASSOC,
       MEM_APPEND, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem materialize_internal_params_origins_env_age:
  env_operand_age ce sa /\
  EVERY (\(name,is_stack,op). safe_operand sa op) caps /\
  materialize_internal_params ce caps sa = (ce',sb) ==>
  env_operand_age ce' sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?delta. state_insts sb = state_insts sa ++ delta /\
          alloca_output_interval sa.cs_next_var sb.cs_next_var delta
Proof
  rpt strip_tac
  >- metis_tac[materialize_internal_params_env_age]
  >- metis_tac[materialize_internal_params_allocation_delta] >>
  drule materialize_internal_params_allocation_delta >> simp[]
QED
