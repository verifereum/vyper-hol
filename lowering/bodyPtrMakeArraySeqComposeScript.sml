(* Checked append keeps the suffix at its actual advanced cursor. *)
Theory bodyPtrMakeArraySeqCompose
Ancestors
  fragGasSeqPtr fragExec ghostPcTransportPtr instIdxIndep
  exprLoweringProps venomExecSemantics venomInst venomState list arithmetic

Theorem inst_seq_ptr_append_shifted:
  !xs s u G tn G1 tn1 ys G2 tn2.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK u /\
    inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 /\
    inst_seq_ptr D lo ctx fn PG G1 tn1 ys
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G2 tn2 ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  Induct >> simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by
    fs[EVERY_MEM] >>
  `run_inst_seq xs (v with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`G1`, `tn1`] >>
  gvs[arithmeticTheory.ADD_CLAUSES]
QED
