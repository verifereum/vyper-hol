(* Joint resources at the supplied mapping scratch endpoint. *)
Theory bodyIntCallFamAggSubscriptMappingRun
Ancestors
  bodyIntCallFamAggSubscriptWordRun bodyIntCallFamAggSubscriptTailRun
  bodyIntCallFamAggSubscriptRunCuts bodyIntCallFamAggSubscriptCuts bodyIntCallJointContract
  exprSimMapKey exprSimAlloc exprLoweringProps loweringHalt emitHelperProps
  stmtReasonMemory fragExec context compileEnv venomState venomInst

Theorem intcall_mapping_scratch_run_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  compile_mapping_subscript base_op key sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. key = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME w0 /\ eval_operand key s = SOME w1 /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  intcall_expr_cont fp ce env es sa s es sb
    (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_mapping_subscript_parts >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sp /\
   ci_mono sp sq /\ ci_mono sq sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, ci_mono_emit_op, pairTheory.SND] >>
  fs[ci_mono_def] >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sn fp.jc_func /\
   fn_has_code sn sp fp.jc_func /\ fn_has_code sp sq fp.jc_func /\
   fn_has_code sq sb fp.jc_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all mapping_scratch_run_cuts >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sn) s = OK first` >>
  `32 <= (64:num) /\ 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all intcall_alloc_word_run_cont >> strip_tac >>
  drule_all run_inst_seq_data_section >> strip_tac >>
  `eval_operand key (first with vs_inst_idx := LENGTH sn.cs_current_insts) = SOME w1` by
    (Cases_on `key` >> fs[eval_operand_def, lookup_var_def, intcall_expr_cont_def] >>
     metis_tac[]) >>
  drule_all mapping_alloca_code >> strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var /\
   (!v. key = Var v ==> not_fresh_at sn v) /\
   (!v. buf.buf_operand = Var v ==> not_fresh_at sn v) /\
   eval_operand buf.buf_operand (first with vs_inst_idx := LENGTH sn.cs_current_insts) = SOME addr /\
   FLOOKUP (first with vs_inst_idx := LENGTH sn.cs_current_insts).vs_allocas
     sa.cs_next_id = SOME (w2n addr,64)` by
    (fs[not_fresh_at_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fp.jc_func) /\
   (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
      [STRING #"%" (toString sa.cs_next_var)]).inst_opcode = ALLOCA` by
    simp[mk_inst_def] >>
  qabbrev_tac `ai = mk_inst sa.cs_next_id ALLOCA [Lit 64w]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `sa.cs_next_id <= ai.inst_id /\
   FLOOKUP (first with vs_inst_idx := LENGTH sn.cs_current_insts).vs_allocas
     ai.inst_id = SOME (w2n addr,64)` by simp[Abbr `ai`, mk_inst_def] >>
  drule_all intcall_scratch_tail_run_cont >> simp[]
QED
