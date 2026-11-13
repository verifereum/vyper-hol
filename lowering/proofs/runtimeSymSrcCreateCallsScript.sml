Theory runtimeSymSrcCreateCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcCallStaging runtimeSymSrcSystemCreate runtimeSymSrcAbiEncode
  runtimeSymSrcContext
  exprLowering compileEnv emitHelper list stackPlanTypes

Theorem runtime_sym_create_salt:
  (!e s op s'. salt = SOME e /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce (expr_type e) e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_salt cfn ce salt s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  (!op. out = SOME op ==> ~is_label_operand op)
Proof
  Cases_on `salt`
  >- (simp[compile_create_salt_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[compile_create_salt_def, comp_bind_def] >> disch_tac >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_create_ctor_tuple:
  (!s vals s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_multi_vvs cfn ce args s = (vals,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ EVERY runtime_sym_value vals) ==>
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_ctor_tuple cfn ce args s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  disch_tac >> simp[compile_create_ctor_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  gvs[comp_return_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule_at (Pat `compile_extcall_store_values _ _ _ _ _ = _`)
    runtime_sym_extcall_store_values >> simp[] >>
  disch_then irule >>
  `!es st. LENGTH (FST (compile_multi_vvs cfn ce es st)) = LENGTH es` by
    (Induct >> simp[compile_multi_vvs_def, comp_return_def, comp_bind_def] >>
     rpt gen_tac >> rpt (pairarg_tac >> simp[]) >>
     simp[comp_return_def] >> metis_tac[pairTheory.FST]) >>
  `LENGTH vals = LENGTH (MAP expr_type args)` by metis_tac[pairTheory.FST, LENGTH_MAP] >>
  simp[every_zip_fst]
QED
