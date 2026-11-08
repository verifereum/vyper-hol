(* Final store of a clean DLOAD word; full old root capacities survive. *)
Theory exprPtrCodeCopyStore
Ancestors
  exprPtrUnwrapStoreSegment exprSimCopy context compileEnv emitHelper emitHelperProps
  exprLoweringProps fragGasSeqPtr ptrDiscipline venomState finite_map
  exprPtrUnwrapCopyEdges exprPtrUnwrapFrames ghostPcTransportPtr instIdxIndep
  venomExecSemantics venomInst

Theorem code_copy_runtime_store:
  emit_void MSTORE [Var root;v] sa = ((),sb) /\
  copy_old_operand sa (Var root) /\ copy_old_operand sa v /\
  eval_operand (Var root) s = SOME addr /\ eval_operand v s = SOME value /\
  op_taint tn v = {} /\ ptr_covers G tn root s 32 /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem = tn.t_mem DIFF {j | w2n addr <= j /\ j < w2n addr + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all copy_runtime_store >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all copy_store_segment >>
  disch_then (qspecl_then [`sa.cs_next_id`, `fn`, `PG`, `D`] strip_assume_tac) >>
  gvs[] >> qexistsl [`Gf`, `tnf`, `mstore (w2n addr) value s`] >> simp[] >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var root;v] []) s =
    OK (mstore (w2n addr) value s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def] >>
  gvs[inst_seq_ptr_def] >> gen_tac >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
       mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule ptr_inst_ok_mstore_tainted >> simp[]
QED
