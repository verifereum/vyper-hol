(* Compiler boundary for aggregate storage Append. *)
Theory bodyMemAppendAggregateCode
Ancestors
  bodyMemAppendAggregatePath stmtSimAppendStorageCompose exprLowering
  exprLoweringProps emitHelper emitHelperProps compileEnv list words pair stmtLowering stmtSimDefs loweringPosts stmtLoweringMono fragExec venomInst

Theorem append_storage_aggregate_suffix_mono:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  cs_extends sa sf /\ sa.cs_next_var <= sf.cs_next_var
Proof
  strip_tac >>
  `ci_mono sa sf` by metis_tac[ci_mono_compile_dynarray_append, SND] >>
  fs[ci_mono_def]
QED

Theorem append_storage_aggregate_code_frame:
  lower_value compile_expr cenv elem e sa = (op,sb) /\
  compile_alloc_buffer sz sb = (buf,sc) /\
  compile_store_memory cenv op buf.buf_operand elem vt sc = ((),sd) /\
  compile_dynarray_append cenv (Lit slot) buf.buf_operand 1 n elem elem cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sd = ((),sf) /\
  fn_has_code sa sf func ==>
  cs_extends sa sb /\ cs_extends sb sc /\ cs_extends sc sd /\ cs_extends sd sf /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\
  fn_has_code sc sd func /\ fn_has_code sd sf func /\
  sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= sf.cs_next_var
Proof
  strip_tac >>
  `cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `ci_mono sb sc` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono sc sd` by metis_tac[ci_mono_compile_store_memory, SND] >>
  drule append_storage_aggregate_suffix_mono >> strip_tac >>
  gvs[ci_mono_def] >>
  `cs_extends sb sf /\ cs_extends sc sf` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem append_storage_aggregate_suffix_open:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  ~block_is_terminated sf
Proof
  strip_tac >> drule (iffLR append_storage_copy_suffix_parts) >>
  disch_then (qx_choosel_then
    [`len'`, `valid`, `data`, `offset`, `dst`, `fresh`, `u`,
     `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`] strip_assume_tac) >>
  Cases_on `tr` >>
  gvs[emit_void_def, emit_def, fresh_id_def, comp_bind_def, comp_return_def] >>
  Cases_on `s8.cs_current_insts` >>
  simp[block_is_terminated_def, mk_inst_def, is_terminator_def,
       LAST_CONS_cond, rich_listTheory.LAST_APPEND_NOT_NIL]
QED
