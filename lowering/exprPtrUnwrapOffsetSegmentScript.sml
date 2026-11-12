(* Root-plus-bounded-offset ADD: establish coverage before hiding ghosts. *)
Theory exprPtrUnwrapOffsetSegment
Ancestors
  exprPtrUnwrapFrames exprPtrUnwrapScalarEdges exprPtrUnwrapCopyEdges typedCopyLoopHeaderPtr
  typedCopyPtr decoderGhostFramePtr bodyPtrDefs fragGasSeqPtr fragExec
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map exprLoweringProps

Theorem copy_offset_segment:
  lookup_var root s = SOME a /\ eval_operand offset s = SOME (n2w off) /\
  ptr_covers G tn root s capacity /\ op_taint tn offset = {} /\
  off < capacity /\ off + n <= capacity /\
  w2n a + off < dimword(:256) /\ root <> out /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [Var root;offset] [out]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [Var root;offset] [out]] s Gf tnf /\
    t = update_var out (a + n2w off) s /\ ptr_covers Gf tnf out t n /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p c. p <> out /\ ptr_covers G tn p s c ==> ptr_covers Gf tnf p t c)
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  qexistsl [`step_prov PG G (mk_inst id ADD [Var root;offset] [out])
    (update_var out (a+n2w off) s)`,
    `step_taint (mk_inst id ADD [Var root;offset] [out]) s
      (update_var out (a+n2w off) s) tn`, `update_var out (a+n2w off) s`] >>
  `step_inst_base (mk_inst id ADD [Var root;offset] [out]) s =
    OK (update_var out (a+n2w off) s)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, ptr_inst_ok_copy_arith,
       copy_len_binop_ghost_frame, copy_mk_immutable_taint] >>
  conj_tac
  >- (irule typed_copy_loop_dynamic_offset_covers >> metis_tac[]) >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
