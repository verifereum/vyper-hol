(* Scalar straight-line summaries hide the concrete intermediate ghosts. *)
Theory exprPtrUnwrapScalarSegments
Ancestors
  exprPtrUnwrapScalarEdges exprPtrUnwrapFrames decoderGhostFramePtr
  typedCopyPtr fragGasSeqPtr fragExec ptrDiscipline
  ptrSafeRun venomExecSemantics venomInst venomState finite_map exprLoweringProps

Theorem copy_arith_segment:
  (opc = ADD \/ opc = MUL) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id opc [left;right] [tmp]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn [mk_inst id opc [left;right] [tmp]]
      s Gf tnf /\
    t = update_var tmp (if opc = ADD then x+y else x*y) s /\
    op_taint tnf (Var tmp) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> tmp /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `update_var tmp result s` >>
  qexistsl_tac [`step_prov PG G (mk_inst id opc [left;right] [tmp])
    (update_var tmp result s)`,
    `step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp result s) tn`, `update_var tmp result s`] >>
  `step_inst_base (mk_inst id opc [left;right] [tmp]) s =
    OK (update_var tmp result s)` by
    (gvs[Abbr `result`] >>
     simp[step_inst_base_def, mk_inst_def, exec_pure2_def]) >>
  gvs[] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, ptr_inst_ok_copy_arith,
       copy_len_binop_ghost_frame, copy_mul_ghost_frame] >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem copy_assign_segment:
  eval_operand arg s = SOME x /\ op_taint tn arg = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ASSIGN [arg] [tmp]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn [mk_inst id ASSIGN [arg] [tmp]]
      s Gf tnf /\
    t = update_var tmp x s /\ op_taint tnf (Var tmp) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> tmp /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  qexistsl_tac [`step_prov PG G (mk_inst id ASSIGN [arg] [tmp])
    (update_var tmp x s)`,
    `step_taint (mk_inst id ASSIGN [arg] [tmp]) s
      (update_var tmp x s) tn`, `update_var tmp x s`] >>
  `step_inst_base (mk_inst id ASSIGN [arg] [tmp]) s =
    OK (update_var tmp x s)` by
    simp[step_inst_base_def, mk_inst_def] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, ptr_inst_ok_copy_assign,
       copy_assign_ghost_frame] >>
  conj_tac >- metis_tac[copy_assign_ghost_frame] >>
  rpt strip_tac >> irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
