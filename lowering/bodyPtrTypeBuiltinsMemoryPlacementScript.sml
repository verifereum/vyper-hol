Theory bodyPtrTypeBuiltinsMemoryPlacement
Ancestors exprSimConvertBytes bodyPtrTypeBuiltinsWidenCopyShape storageCopyGasPath
  emitHelperProps emitHelper exprLoweringProps exprLowering compileEnv fragExec context

Theorem bytestring_cast_id_growth:
  compile_type_convert x (ConvBytestringCast n i) sa = (out,sb) ==>
  sa.cs_next_id <= sb.cs_next_id
Proof
  Cases_on `n < i` >>
  simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_void_def, emit_op_def, emit_inst_def, comp_bind_def,
    comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem straight_line_suffix_placement:
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb fn ==>
  sa.cs_current_bb = sb.cs_current_bb /\
  LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP (LENGTH sa.cs_current_insts) bb.bb_instructions)
Proof
  strip_tac >> conj_tac >- fs[same_blocks_def] >>
  conj_tac
  >- (fs[emitted_insts_def] >> imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> decide_tac) >>
  metis_tac[storage_copy_code_prefix]
QED

Theorem bytestring_widen_straight_line:
  compile_bytestring_widen_copy capacity src n sa = (out,sb) /\ fn_has_code sa sb fn ==>
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  strip_tac >> drule_all widen_copy_code_split >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  Cases_on `n = 0`
  >- gvs[compile_copy_memory_def, comp_return_def, same_blocks_def] >>
  `emit_void MCOPY [buf.buf_operand;src;Lit (n2w n)] sm = ((),sb)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  drule emit_void_extends >> strip_tac >>
  fs[same_blocks_def] >> gvs[] >>
  simp[GSYM listTheory.APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]
QED
