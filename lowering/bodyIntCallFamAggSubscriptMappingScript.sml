(* Mapping scratch execution retaining the joint continuation. *)
Theory bodyIntCallFamAggSubscriptMapping
Ancestors
  bodyIntCallFamAggSubscriptScratchTail bodyIntCallFamAggSubscriptScratchStages
  bodyIntCallJointContract exprSimMapKey exprSimAlloc exprLoweringProps
  fragExec loweringHalt emitHelperProps context compileEnv venomInst

Theorem intcall_mapping_scratch_cont:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  compile_mapping_subscript base_op key sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      intcall_expr_cont fp ce env es sa s es sb u /\
      (!x. op = Var x ==> not_fresh_at sb x)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_mapping_subscript_parts >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sp /\
   ci_mono sp sq /\ ci_mono sq sb` by
    (metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, ci_mono_emit_op, pairTheory.SND]) >>
  fs[ci_mono_def] >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
   fn_has_code sn sp fp.jc_func /\ fn_has_code sp sq fp.jc_func /\
   fn_has_code sq sb fp.jc_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `32 <= (64:num) /\ 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all intcall_alloc_word_cont >> strip_tac >>
  rename1 `intcall_expr_cont fp ce env es sa s es sn header` >>
  drule_all mapping_alloca_code >> strip_tac >>
  irule intcall_scratch_tail_cont >> simp[] >>
  rename1 `emit_op ADD _ sn = (dst,sp)` >>
  qexistsl_tac [`addr`, `buf.buf_operand`, `dst`,
    `mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]`, `key`, `header`, `sn`, `sp`, `sq`, `w1`] >>
  simp[mk_inst_def] >> goal_assum (drule_at Any) >> simp[]
QED
