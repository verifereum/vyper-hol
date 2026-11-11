(* Checked append keeps the suffix at its actual advanced cursor. *)
Theory bodyPtrMakeArraySeqCompose
Ancestors
  fragGasSeqPtr fragExec ghostPcTransportPtr instIdxIndep exprSimCopy
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

Theorem copy_runtime_checked_append_uniform:
  copy_runtime_frame sa s sb u /\ copy_runtime_frame sb u sc v /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  (!j. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := j) G1 tn1) /\
  (!j. inst_seq_ptr D lo ctx fn PG G1 tn1 (emitted_insts sb sc)
    (u with vs_inst_idx := j) G2 tn2) ==>
  copy_runtime_frame sa s sc v /\
  (!j. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sc)
    (s with vs_inst_idx := j) G2 tn2)
Proof
  strip_tac >>
  `copy_runtime_frame sa s sc v` by metis_tac[copy_runtime_frame_trans] >>
  simp[] >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> fs[copy_runtime_frame_def]) >>
  simp[] >> gen_tac >> irule inst_seq_ptr_append_shifted >>
  conj_tac >- simp[] >>
  qexistsl_tac [`G1`, `tn1`, `u with vs_inst_idx := j`] >> simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  fs[copy_runtime_frame_def, exec_result_map_def]
QED
