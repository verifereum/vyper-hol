Theory runtimeSymSrcModuleArgPreservation
Ancestors
  runtimeSymSrcAbiDecode runtimeSymSrcAbiCalls runtimeSymSrcEmission
  moduleLowering context compileEnv emitHelper loweringShapeDefs venomInst
  runtimeSymSrcInterfaces finite_map list stackPlanTypes

Theorem runtime_sym_decode_operand:
  runtime_sym_env ce /\ FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_decode_operand loc = SOME dst ==> ~is_label_operand dst
Proof
  strip_tac >> `runtime_sym_loc loc` by metis_tac[runtime_sym_env_def] >>
  Cases_on `loc` >> gvs[var_location_decode_operand_def, runtime_sym_loc_def,
                        is_label_operand_def]
QED

Theorem runtime_sym_fixed_region_with_id:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_fixed_region_with_id n s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  ~is_label_operand (SND v).buf_operand
Proof
  simp[compile_fixed_region_with_id_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def, is_label_operand_def]
QED

Theorem runtime_sym_decode_args:
  !args off s u s'.
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct
  >- (simp[compile_decode_args_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> Cases_on `h1` >>
  simp[Once compile_decode_args_def, comp_bind_def, comp_ignore_bind_def]
  >- (rpt (pairarg_tac >> simp[]) >> strip_tac >>
      qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
      simp[is_label_operand_def] >> strip_tac >>
      qpat_assum `emit_op CALLDATALOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
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
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_abi_decode_to_buf) >>
  simp[is_label_operand_def] >> strip_tac >> metis_tac[]
QED
