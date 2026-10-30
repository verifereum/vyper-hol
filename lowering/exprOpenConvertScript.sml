(*
 * compile_expr keeps its block open: convert
 *
 * TOP-LEVEL:
 *   compile_type_convert_open — the supported conversions
 *)

Theory exprOpenConvert
Ancestors
  list rich_list exprOpenBuiltins exprOpenPrimitives exprLowering compileEnv context emitHelper venomInst

Theorem compile_convert_int_open:
  !v in_s in_b out_s out_b sa r sb.
    ~block_is_terminated sa /\
    compile_type_convert v (ConvIntToInt in_s in_b out_s out_b) sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `in_s` >> Cases_on `out_s` >>
  Cases_on `out_b < in_b` >>
  simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  strip_tac >> Cases_on `sa.cs_current_insts` >>
  gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
      mk_inst_def, is_terminator_def]
QED

Theorem compile_convert_fixed_to_bytestring_open:
  !v m sa r sb.
    compile_type_convert v (ConvFixedToBytestring m) sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_type_convert_open:
  !v cv sa r sb.
    ~block_is_terminated sa /\ compile_type_convert v cv sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `cv`
  >~ [`ConvIntToInt`] >- metis_tac[compile_convert_int_open]
  >~ [`ConvFixedToBytestring`] >- metis_tac[compile_convert_fixed_to_bytestring_open] >>
  simp[compile_type_convert_def, load_bytestring_as_word_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> Cases_on `sa.cs_current_insts` >>
  gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
      mk_inst_def, is_terminator_def]
QED
