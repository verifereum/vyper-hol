Theory runtimeSymSrcExternalPrimitive
Ancestors
  runtimeSymSrcBlockEmission
  runtimeSymSrcCallStaging runtimeSymSrcContextComplete runtimeSymSrcContextCopy
  runtimeSymSrcContext runtimeSymSrcContextTyped abiEncodeValuesCode abiEncoderChildCode
  runtimeSymSrcEmission runtimeSymSrcInterfaces exprLowering compileEnv emitHelper
  loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_zip_fst:
  !xs ys P. EVERY P xs ==> EVERY (\x. P (FST x)) (ZIP (xs,ys))
Proof
  Induct >> Cases_on `ys` >> simp[ZIP_def]
QED

Theorem runtime_sym_external_return_cond[local]:
  (!dst src hi info s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand hi /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ce buf def addr rt dt skip mn ra rm hasdef dec s v s'.
    runtime_sym_env tops ce /\ ~is_label_operand buf /\ ~is_label_operand def /\
    ~is_label_operand addr /\ EVERY runtime_sym_inst (state_insts s) /\
    (if rt = NoneT then comp_return (Lit 0w)
     else if hasdef then
       do result <- compile_alloc_buffer rm;
          compile_default_return_path ce rt dt buf result.buf_operand def addr skip mn ra dec od
     else
       do result <- compile_alloc_buffer rm;
          hi <- compile_return_value_decode mn ra;
          u <- compile_abi_decode_to_buf result.buf_operand (Lit 0w) MLOAD buf hi dec;
          comp_return result.buf_operand od) s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  disch_tac >> rpt gen_tac >>
  Cases_on `rt = NoneT` >- (simp[comp_return_def, is_label_operand_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `hasdef` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >>
      drule_all runtime_sym_alloc_buffer >> strip_tac >>
      qpat_assum `compile_default_return_path _ _ _ _ _ _ _ _ _ _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_default_return_path_cond) >>
      disch_then (qspec_then `tops` mp_tac) >> impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum drule_all >> simp[]) >> simp[]) >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule_all runtime_sym_return_value_decode >> strip_tac >>
  gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_abi_encode_child_prefix[local]:
  ~is_label_operand dst /\ ~is_label_operand cursor /\
  EVERY runtime_sym_inst (state_insts s) /\
  abi_encode_child_prefix dst off cursor s = ((head,tail_off,child),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  ~is_label_operand head /\ ~is_label_operand tail_off /\ ~is_label_operand child
Proof
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  ntac 3 (rev_dxrule runtime_sym_emit_op_result >>
    simp[is_label_operand_def] >> strip_tac) >> simp[]
QED

Theorem runtime_sym_abi_encode_child_suffix[local]:
  ~is_label_operand head /\ ~is_label_operand cursor /\
  ~is_label_operand tail_off /\ ~is_label_operand len /\
  EVERY runtime_sym_inst (state_insts s) /\
  abi_encode_child_suffix head cursor tail_off len s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 3 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rev_dxrule runtime_sym_emit_void_result >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_emit_op_result >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_emit_void_result >> simp[]
QED

Theorem runtime_sym_abi_encode_value_rows[local]:
  (!dst src info s v s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf dst src info s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  !rows ce dst cursor off s s'.
    runtime_sym_env tops ce /\ EVERY (\row. runtime_sym_value (FST row)) rows /\
    ~is_label_operand dst /\ ~is_label_operand cursor /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_value_rows ce dst cursor off rows s = ((),s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  disch_then (mk_asm "encode") >>
  Induct >- simp[compile_abi_encode_value_rows_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[] >> strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields h1`
  >- (drule_all abi_encode_value_rows_dynamic_trace >> strip_tac >>
      drule_all runtime_sym_abi_encode_child_prefix >> strip_tac >>
      drule_all runtime_sym_unwrap_value >> strip_tac >>
      asm "encode" drule_all >> strip_tac >>
      drule_all runtime_sym_abi_encode_child_suffix >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> drule_all abi_encode_value_rows_static_trace >> strip_tac >>
  rev_dxrule runtime_sym_emit_op_result >> simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_unwrap_value >> strip_tac >>
  drule_all runtime_sym_store_memory >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem runtime_sym_abi_encode_values_to_buf:
  (!dst src info s v s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf dst src info s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) ==>
  !ce dst rows s v s'.
    runtime_sym_env tops ce /\ EVERY (\row. runtime_sym_value (FST row)) rows /\
    ~is_label_operand dst /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_values_to_buf ce dst rows s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  drule abi_encode_values_to_buf_trace >> strip_tac >>
  rev_dxrule runtime_sym_emit_op_result >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_emit_void_result >> simp[is_label_operand_def] >> strip_tac >>
  dxrule runtime_sym_abi_encode_value_rows >>
  disch_then drule_all >> strip_tac >>
  rev_dxrule runtime_sym_emit_op_result >> simp[]
QED

Theorem runtime_sym_external_call_kwargs_cond:
  (!dst src info s v s'.
    ~is_label_operand dst /\ ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_encode_to_buf dst src info s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!dst src hi info s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand hi /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ce addr vals tys aa mid ra mn rm static value gas skip hasdef def rt dt dec s v s'.
    runtime_sym_env tops ce /\ EVERY runtime_sym_value vals /\
    ~is_label_operand addr /\ ~is_label_operand value /\
    ~is_label_operand gas /\ ~is_label_operand def /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_call_kwargs ce addr vals tys aa mid ra mn rm static
      value gas skip hasdef def rt dt dec s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "encode_abi") (mk_asm "decode")) >>
  rpt gen_tac >>
  simp[compile_external_call_kwargs_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 14 (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs'³') /\ ~is_label_operand call_len`
    by suspend "encode" >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts cs'⁵')` by
    (Cases_on `rt = NoneT /\ ~skip` >> gvs[comp_return_def] >>
     drule_all runtime_sym_extcodesize_check >> simp[]) >>
  `EVERY runtime_sym_inst (state_insts cs'⁶') /\ ~is_label_operand success` by
    (qpat_x_assum `(if static then _ else _) _ = _` mp_tac >>
     Cases_on `static` >> simp[] >> strip_tac >>
     qpat_assum `emit_op _ _ _ = (success,_)`
       (mp_then Any mp_tac runtime_sym_emit_op) >>
     simp[is_label_operand_def]) >>
  rev_dxrule runtime_sym_fresh_label >> strip_tac >>
  rev_dxrule runtime_sym_fresh_label >> strip_tac >>
  qpat_assum `emit_inst JNZ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_jnz) >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> fs[] >>
  qpat_assum `emit_op RETURNDATASIZE _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_x_assum `_ (emit_void RETURNDATACOPY _ _) = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `emit_void RETURNDATACOPY _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_inst REVERT _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  impl_tac >- metis_tac[runtime_sym_nonlabel_reserved] >>
  strip_tac >> imp_res_tac runtime_sym_new_block_result >> fs[] >>
  suspend "return"
QED

Resume runtime_sym_external_call_kwargs_cond[encode]:
  Cases_on `vals = []` >- gvs[comp_return_def, is_label_operand_def] >>
  qpat_x_assum `(if vals = [] then _ else _) _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >>
  `EVERY (\x. runtime_sym_value (FST x)) (ZIP (vals,tys))`
    by (irule runtime_sym_zip_fst >> simp[]) >>
  qpat_assum `emit_op ADD [buf_op_alloc.buf_operand; Lit 32w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  asm "encode_abi" (mp_tac o MATCH_MP runtime_sym_abi_encode_values_to_buf) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `emit_op ADD [args_len; Lit 4w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def]
QED
Resume runtime_sym_external_call_kwargs_cond[return]:
  qpat_assum `(if rt = NoneT then _ else _) _ = _`
    (mp_then Any mp_tac runtime_sym_external_return_cond) >>
  disch_then (qspec_then `tops` mp_tac) >> impl_tac >- (asm "decode" mp_tac >> simp[]) >> simp[]
QED
Finalise runtime_sym_external_call_kwargs_cond
