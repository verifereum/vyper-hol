(* Scalar straight-line summary hiding the concrete intermediate ghosts. *)
Theory exprPtrUnwrapScalarSegments
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapCopyEdges exprPtrUnwrapFrames decoderGhostFramePtr
  typedCopyPtr fragGasSeqPtr fragExec ptrDiscipline ptrSafeRun
  venomExecSemantics venomInst venomState finite_map exprLoweringProps

Theorem copy_assign_segment:
  eval_operand arg s = SOME x /\ op_taint tn arg = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ASSIGN [arg] [tmp]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ASSIGN [arg] [tmp]] s Gf tnf /\
    t = update_var tmp x s /\ op_taint tnf (Var tmp) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> tmp ==> FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> tmp /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  qexistsl [`step_prov PG G (mk_inst id ASSIGN [arg] [tmp]) (update_var tmp x s)`,
    `step_taint (mk_inst id ASSIGN [arg] [tmp]) s (update_var tmp x s) tn`,
    `update_var tmp x s`] >>
  `step_inst_base (mk_inst id ASSIGN [arg] [tmp]) s = OK (update_var tmp x s)` by
    simp[step_inst_base_def, mk_inst_def] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, ptr_inst_ok_copy_assign, copy_assign_ghost_frame] >>
  conj_tac >- metis_tac[copy_assign_ghost_frame] >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
