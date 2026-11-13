Theory runtimeSymSrcCallStaging
Ancestors
  runtimeSymSrcContextComplete runtimeSymSrcContext runtimeSymSrcContextTypedBase
  runtimeSymSrcContextCopy
  runtimeSymSrcEmission runtimeSymSrcEmissionProbe runtimeSymSrcInterfaces exprLowering builtinSimple
  compileEnv emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_stage_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_stage_void[local]:
  emit_void opc ops s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[runtime_sym_emit_void]
QED

Theorem runtime_sym_extcodesize_check:
  ~is_label_operand addr /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_extcodesize_check addr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_extcodesize_check_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_stage_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_stage_void >> simp[]
QED

Theorem runtime_sym_return_value_decode:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_return_value_decode mn mx s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_return_value_decode_def, compile_select_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_stage_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_stage_void >> simp[] >> strip_tac >>
  ntac 4 (rev_dxrule runtime_sym_stage_op >> simp[is_label_operand_def] >> strip_tac) >> simp[]
QED

Theorem runtime_sym_store_multi_results:
  !ops buf off s u s'.
  EVERY (\op. ~is_label_operand op) ops /\ ~is_label_operand buf /\
  EVERY runtime_sym_inst (state_insts s) /\
  store_multi_results buf ops off s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >> simp[store_multi_results_def, comp_return_def, comp_bind_def,
                 comp_ignore_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_stage_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_stage_void >> simp[] >> strip_tac >>
  first_x_assum irule >> simp[] >>
  qexistsl [`buf`, `off + 32`, `cs''`] >> simp[]
QED

Theorem runtime_sym_extcall_store_values:
  !xs ce buf off s u s'.
  EVERY (\x. runtime_sym_value (FST x)) xs /\ runtime_sym_env ce /\
  ~is_label_operand buf /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_extcall_store_values ce xs buf off s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >- simp[compile_extcall_store_values_def, comp_return_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_stage_op >> simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_unwrap_value >> strip_tac >>
  Cases_on `is_word_type r` >> gvs[]
  >- (rev_dxrule runtime_sym_stage_void >> simp[] >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type r` >> gvs[]
  >- (drule_all runtime_sym_store_bytestring >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  rev_dxrule runtime_sym_stage_void >> simp[is_label_operand_def] >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem runtime_sym_store_abi_tuple:
  !xs ce buf off s u s'.
  EVERY (\x. ~is_label_operand (FST x)) xs /\
  ~is_label_operand buf /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_store_abi_tuple ce buf off xs s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def] >>
  Cases_on `h` >> rpt gen_tac >>
  simp[compile_store_abi_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_stage_op >> simp[is_label_operand_def] >> strip_tac >>
  Cases_on `is_word_type r` >> gvs[]
  >- (rev_dxrule runtime_sym_stage_void >> simp[] >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all runtime_sym_copy_memory >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem runtime_sym_stage_intcall_args:
  !ce vals flags tys s ops s'.
  runtime_sym_env ce /\ EVERY runtime_sym_value vals /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_stage_intcall_args ce vals flags tys s = (ops,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  EVERY (\op. ~is_label_operand op) ops
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >> rpt conj_tac
  >- simp[compile_stage_intcall_args_def, comp_return_def]
  >- (rpt gen_tac >> disch_tac >> rpt gen_tac >> simp[Once compile_stage_intcall_args_def,
                         comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      drule_all runtime_sym_unwrap_value >> strip_tac >>
      gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]) 
  >- (rpt gen_tac >> disch_tac >> rpt gen_tac >> simp[Once compile_stage_intcall_args_def,
                         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >>
      drule_all runtime_sym_unwrap_value >> strip_tac >>
      drule_all runtime_sym_alloc_buffer >> strip_tac >>
      Cases_on `is_word_type ty` >> gvs[]
      >- (rev_dxrule runtime_sym_stage_void >> simp[] >> strip_tac >>
          gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]) >>
      Cases_on `case ty of BaseT (BytesT (Dynamic _)) => T | BaseT (StringT _) => T | _ => F` >> gvs[]
      >- (gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
          pairarg_tac >> gvs[] >>
          drule_all runtime_sym_store_bytestring >> strip_tac >>
          gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]) >>
      drule_all runtimeSymSrcContextTypedTheory.runtime_sym_store_memory >> strip_tac >>
      gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]) >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  simp[Once compile_stage_intcall_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all runtime_sym_unwrap_value >> strip_tac >>
  gvs[] >> first_x_assum drule_all >> strip_tac >> simp[]
QED

Theorem runtime_sym_default_return_path_cond:
  (!dst src hi s u s'.
     ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand hi /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info s = (u,s') ==>
     EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_env ce /\ ~is_label_operand buf /\ ~is_label_operand result /\
  ~is_label_operand def /\ ~is_label_operand addr /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_default_return_path ce rt dt buf result def addr skip mn mx info s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  disch_tac >>
  simp[compile_default_return_path_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_stage_op >> simp[] >> strip_tac) >>
  ntac 3 (rev_dxrule runtime_sym_fresh_label >> strip_tac >> gvs[]) >>
  qpat_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >> simp[] >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> strip_tac >>
  drule_all runtimeSymSrcContextTypedTheory.runtime_sym_store_memory >> strip_tac >>
  Cases_on `skip` >> gvs[comp_return_def]
  >- (drule_all runtime_sym_jump >> strip_tac >>
      drule_all runtime_sym_copy_new_block >> strip_tac >>
      drule_all runtime_sym_return_value_decode >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      drule_all runtime_sym_jump >> strip_tac >>
      drule_all runtime_sym_copy_new_block >> simp[]) >>
  drule_all runtime_sym_extcodesize_check >> strip_tac >>
  drule_all runtime_sym_jump >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> strip_tac >>
  drule_all runtime_sym_return_value_decode >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all runtime_sym_jump >> strip_tac >>
  drule_all runtime_sym_copy_new_block >> simp[]
QED
