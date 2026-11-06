(* A slot load transports, rather than discards, dead-byte taint. *)
Theory exprPtrUnwrapLoadSegment
Ancestors
  exprPtrUnwrapCopyEdges exprPtrUnwrapFrames decoderGhostFramePtr
  slotCopyExecution fragGasSeqPtr fragExec
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState finite_map
  exprLoweringProps

Theorem copy_slot_load_segment:
  (load = SLOAD \/ load = TLOAD) /\ eval_operand arg s = SOME key /\
  op_taint tn arg = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id load [arg] [out]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn [mk_inst id load [arg] [out]]
      s Gf tnf /\
    t = update_var out (slot_copy_word load s key) s /\
    op_taint tnf (Var out) =
      key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) key /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> out ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. p <> out /\ ptr_covers G tn p s n ==> ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  qexistsl [`step_prov PG G (mk_inst id load [arg] [out])
    (update_var out (slot_copy_word load s key) s)`,
    `step_taint (mk_inst id load [arg] [out]) s
      (update_var out (slot_copy_word load s key) s) tn`,
    `update_var out (slot_copy_word load s key) s`] >>
  `step_inst_base (mk_inst id load [arg] [out]) s =
    OK (update_var out (slot_copy_word load s key) s)` by
    (gvs[] >> simp[step_inst_base_def, mk_inst_def, exec_read1_def,
                   slot_copy_word_def]) >>
  simp[run_inst_seq_def, inst_seq_ptr_def, ptr_inst_ok_slot_load,
       slot_load_output_taint, slot_load_ghost_frame] >>
  rpt strip_tac >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
  irule ptr_covers_step_frame >>
  simp[mk_inst_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
