(* Compiler shape and supplied-run decomposition for mapping scratch. *)
Theory bodyIntCallFamAggSubscriptCuts
Ancestors
  bodyIntCallFamAggSubscriptRunCuts exprSimMapKey exprSimAlloc
  exprLoweringProps emitHelperProps loweringHalt context compileEnv venomState venomInst

Theorem mapping_scratch_cut_shape:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; base_op] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sn = (dst,sp) /\
  emit_void MSTORE [dst; key] sp = ((),sq) /\
  emit_op SHA3 [buf.buf_operand; Lit 64w] sq = (op,sb) ==>
  sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  sp.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sp /\
  sb.cs_current_insts = sp.cs_current_insts ++ emitted_insts sp sb /\
  sq.cs_current_insts = sp.cs_current_insts ++ emitted_insts sp sq /\
  sb.cs_current_insts = sq.cs_current_insts ++ emitted_insts sq sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sp sb) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sq sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  imp_res_tac emitted_insts_emit_void >>
  imp_res_tac emitted_insts_emit_op >>
  simp[emitted_insts_def, listTheory.APPEND_ASSOC,
       listTheory.DROP_APPEND2, mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_PREFIX, listTheory.DROP_APPEND2, is_terminator_def]
QED

Theorem mapping_scratch_run_cuts:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; base_op] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sn = (dst,sp) /\
  emit_void MSTORE [dst; key] sp = ((),sq) /\
  emit_op SHA3 [buf.buf_operand; Lit 64w] sq = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sn) /\
  ?first added stored.
    run_inst_seq (emitted_insts sa sn) s = OK first /\
    run_inst_seq (emitted_insts sn sp)
      (first with vs_inst_idx := LENGTH sn.cs_current_insts) = OK added /\
    run_inst_seq (emitted_insts sp sq)
      (added with vs_inst_idx := LENGTH sp.cs_current_insts) = OK stored /\
    run_inst_seq (emitted_insts sq sb)
      (stored with vs_inst_idx := LENGTH sq.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH sq.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mapping_scratch_cut_shape >> strip_tac >>
  simp[] >>
  drule_all subscript_run_split >>
  disch_then (qx_choose_then `first` strip_assume_tac) >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` kall_tac >>
  drule_all subscript_run_split >>
  disch_then (qx_choose_then `added` strip_assume_tac) >>
  qpat_x_assum `run_inst_seq (emitted_insts sn sb) _ = _` kall_tac >>
  drule_all subscript_run_split >>
  disch_then (qx_choose_then `stored` strip_assume_tac) >>
  qexistsl [`first`, `added`, `stored`] >> gvs[]
QED
