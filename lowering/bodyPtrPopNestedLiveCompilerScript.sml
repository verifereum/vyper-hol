Theory bodyPtrPopNestedLiveCompiler
Ancestors
  exprSimPopNestedLocalRun exprLowering exprLoweringProps context emitHelperProps emitHelper
  fragExec compileEnv list rich_list

Theorem pop_memory_compile_stages:
  compile_dynarray_pop hdr 32 scale ctor imm LocMemory sa = (dst,sz) ==>
  ?sm sb sc sd se sf sg sh len nz valid new_len data offset.
    emit_op MLOAD [hdr] sa = (len,sm) /\
    emit_op ISZERO [len] sm = (nz,sb) /\
    emit_op ISZERO [nz] sb = (valid,sc) /\
    emit_void ASSERT [valid] sc = ((),sd) /\
    emit_op SUB [len;Lit 1w] sd = (new_len,se) /\
    emit_void MSTORE [hdr;new_len] se = ((),sf) /\
    emit_op ADD [hdr;Lit 32w] sf = (data,sg) /\
    emit_op MUL [new_len;Lit (n2w scale)] sg = (offset,sh) /\
    emit_op ADD [data;offset] sh = (dst,sz)
Proof
  simp[compile_dynarray_pop_def, compile_ptr_load_def, compile_ptr_store_def,
       comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem pop_memory_stage_code:
  emit_op MLOAD [hdr] sa = (len,sm) /\
  emit_op ISZERO [len] sm = (nz,sb) /\
  emit_op ISZERO [nz] sb = (valid,sc) /\
  emit_void ASSERT [valid] sc = ((),sd) /\
  emit_op SUB [len;Lit 1w] sd = (new_len,se) /\
  emit_void MSTORE [hdr;new_len] se = ((),sf) /\
  emit_op ADD [hdr;Lit 32w] sf = (data,sg) /\
  emit_op MUL [new_len;Lit (n2w scale)] sg = (offset,sh) /\
  emit_op ADD [data;offset] sh = (dst,sz) /\ fn_has_code sa sz fn ==>
  fn_has_code sa sm fn /\ fn_has_code sm se fn /\
  fn_has_code se sf fn /\ fn_has_code sf sg fn /\
  fn_has_code sg sh fn /\ fn_has_code sh sz fn /\
  sa.cs_next_var <= sf.cs_next_var /\
  (!v. new_len = Var v ==> not_fresh_at sf v)
Proof
  strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `sa.cs_next_var <= sf.cs_next_var /\
   (!v. new_len = Var v ==> not_fresh_at sf v)` by
    (imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >> gvs[not_fresh_at_def]) >>
  fs[same_blocks_def, fn_has_code_def, emitted_blocks_def] >>
  simp[] >> metis_tac[IS_PREFIX_APPEND, IS_PREFIX_TRANS]
QED
