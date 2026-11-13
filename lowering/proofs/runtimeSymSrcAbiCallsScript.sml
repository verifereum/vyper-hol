Theory runtimeSymSrcAbiCalls
Ancestors
  runtimeSymSrcContext runtimeSymSrcEmission runtimeSymSrcInterfaces
  abiEncoder builtinAbi compileEnv emitHelper loweringShapeDefs venomInst list
  stackPlanTypes

Theorem runtime_sym_abi_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_abi_void[local]:
  emit_void opc ops s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[runtime_sym_emit_void]
QED

Theorem runtime_sym_abi_int_clamp:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_int_clamp v bits signed s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `signed` >>
  simp[compile_abi_int_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[]
QED

Theorem runtime_sym_abi_bytes_clamp:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_bytes_clamp v n s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[]
QED

Theorem runtime_sym_abi_clamp_basetype:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_clamp_basetype v c s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `c` >> simp[compile_abi_clamp_basetype_def, comp_return_def]
  >- (rpt strip_tac >> gvs[])
  >- metis_tac[runtime_sym_abi_int_clamp]
  >- metis_tac[runtime_sym_abi_bytes_clamp] >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[]
QED

Theorem runtime_sym_abi_zero_pad:
  ~is_label_operand p /\ ~is_label_operand n /\ ~is_label_operand c /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_zero_pad p n c s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_abi_zero_pad_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_abi_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[]
QED

Theorem runtime_sym_get_element_ptr:
  ~is_label_operand p /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_get_element_ptr p n s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_get_element_ptr_def] >> strip_tac >>
  rev_dxrule runtime_sym_abi_op >> simp[is_label_operand_def]
QED

Theorem runtime_sym_get_dynarray_elem_ptr:
  ~is_label_operand p /\ ~is_label_operand i /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_get_dynarray_elem_ptr p i n s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_get_dynarray_elem_ptr_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_op >> simp[]
QED

Theorem runtime_sym_abi_encode_static:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_static dst src s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_abi_encode_static_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_abi_void >> simp[is_label_operand_def]
QED

Theorem runtime_sym_abi_encode_static_info:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_static_info dst src info s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def]
  >- metis_tac[runtime_sym_abi_encode_static]
  >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[is_label_operand_def] >>
  rev_dxrule runtime_sym_abi_void >> simp[is_label_operand_def]
QED

Theorem runtime_sym_abi_decode_static:
  (!v s u s'. ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
     clamp v s = (u,s') ==> EVERY runtime_sym_inst (state_insts s')) ==>
  ~is_label_operand src /\ ~is_label_operand dst /\
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_decode_static src dst opc clamp s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  simp[compile_abi_decode_static_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rev_dxrule runtime_sym_abi_void >> simp[]
QED

Theorem runtime_sym_abi_dec_addr:
  ~is_label_operand bop /\ ~is_label_operand pos /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_dec_addr bop pos s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp[comp_return_def] >- (rpt strip_tac >> gvs[]) >>
  strip_tac >> rev_dxrule runtime_sym_abi_op >> simp[]
QED

Theorem runtime_sym_abi_decode_range_check:
  ~is_label_operand start /\ ~is_label_operand endop /\ ~is_label_operand hi /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_decode_range_check start endop hi s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[] >> strip_tac >>
  ntac 4 (rev_dxrule runtime_sym_abi_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[]
QED

Theorem runtime_sym_getelemptr_abi:
  ~is_label_operand src /\ ~is_label_operand bop /\ ~is_label_operand hi /\
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_getelemptr_abi src dyn off opc bop hi s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `dyn`
  >- (Cases_on `hi = Lit 0w` >>
      simp[compile_getelemptr_abi_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def] >>
      ntac 4 (pairarg_tac >> simp[])
      >- (strip_tac >> gvs[] >>
          rev_dxrule runtime_sym_abi_op >> simp[is_label_operand_def] >> strip_tac >>
          drule_all runtime_sym_abi_dec_addr >> strip_tac >>
          rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac >>
          rev_dxrule runtime_sym_abi_op >> simp[]) >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      rev_dxrule runtime_sym_abi_op >> simp[is_label_operand_def] >> strip_tac >>
      drule_all runtime_sym_abi_dec_addr >> strip_tac >>
      ntac 4 (rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac) >>
      rev_dxrule runtime_sym_abi_void >> simp[]) >>
  simp[compile_getelemptr_abi_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rev_dxrule runtime_sym_abi_op >> simp[is_label_operand_def]
QED

Theorem runtime_sym_abi_decode_dyn_elem_ptr:
  ~is_label_operand bop /\ ~is_label_operand elem /\
  ~is_label_operand src /\ ~is_label_operand hi /\
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_abi_dec_addr >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac) >>
  ntac 2 (rev_dxrule runtime_sym_abi_op >> simp[] >> strip_tac) >>
  rev_dxrule runtime_sym_abi_void >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_abi_op >> simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_abi_decode_range_check >> simp[]
QED
