(* Cursor initialization is independent of allocation: the caller supplies a
   covered cell, so this boundary also applies to reused scratch cells. *)
Theory logCursorInitPtr
Ancestors
  logInstSeqPtr logTopicScalarPtr typedCopyPtr emitHelperProps
  ptrDiscipline venomExecSemantics venomState venomInst words pred_set

Theorem emit_literal_cursor_init_seq_ptr:
  emit_void MSTORE [Var dst;Lit w] sa = ((),sb) /\
  ptr_covers G tn dst s 32 /\ lookup_var dst s = SOME a /\
  ~ctx_has_dalloca ctx ==>
  ?tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tnf /\
    sf = mstore (w2n a) w s /\
    mem_agree_outside {i | w2n a <= i /\ i < w2n a + 32}
      sf.vs_memory s.vs_memory /\
    tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tnf.t_mem) /\
    (!i. ~(w2n a <= i /\ i < w2n a + 32) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `op_taint tn (Lit w) = {} /\ eval_operand (Lit w) s = SOME w` by
    simp[op_taint_def, eval_operand_def] >>
  drule_all emit_mstore_clean_seq_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`]
    (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac))) >>
  `EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (drule emitted_insts_emit_void >> simp[mk_inst_def]) >>
  `tnf.t_imm = tn.t_imm` by
    (drule_all inst_seq_ptr_immutable_taint_frame >> simp[]) >>
  qexistsl_tac [`tnf`, `sf`] >>
  simp[mstore_memory_frame, IN_DIFF, IN_GSPEC_IFF]
QED
