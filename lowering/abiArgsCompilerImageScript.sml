Theory abiArgsCompilerImage
Ancestors
  exprLowering context compileEnv emitHelper

Theorem abi_image_convert_label:
  compile_type_convert op conv sa = (Label l,sb) ==>
  op = Label l /\ sb.cs_blocks = sa.cs_blocks
Proof
  Cases_on `conv` >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       load_bytestring_as_word_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt (IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
            fresh_id_def, fresh_var_def, emit_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_alloc_not_label:
  compile_alloc_buffer n sa = (buf,sb) ==> buf.buf_operand <> Label l
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_ensure_label:
  compile_ensure_in_memory op loc bytes wc ctor imm sa = (Label l,sb) ==>
  op = Label l /\ sb = sa
Proof
  Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[abi_image_alloc_not_label]
QED

Theorem abi_image_load_not_label:
  compile_ptr_load ctor imm loc op sa = (v,sb) ==> v <> Label l
Proof
  Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, emit_op_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_image_unwrap_label:
  unwrap_value ce vv sa = (Label l,sb) ==>
  vv_operand vv = Label l /\ sb = sa
Proof
  Cases_on `vv` >> simp[unwrap_value_def, comp_return_def, vv_operand_def] >>
  Cases_on `is_word_type t` >> simp[]
  >- metis_tac[abi_image_load_not_label] >>
  Cases_on `p.ptr_location` >> simp[comp_return_def] >>
  metis_tac[abi_image_ensure_label]
QED
