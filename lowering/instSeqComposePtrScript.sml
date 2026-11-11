(* Uniform suffix checks accommodate the cursor advanced by the prefix. *)
Theory instSeqComposePtr
Ancestors exprLoweringProps fragGasSeqPtr ghostPcTransportPtr instIdxIndep fragExec
  venomExecSemantics venomState venomInst list

Theorem inst_seq_ptr_append:
  !xs s t G tn G1 tn1 G2 tn2 ys.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 /\
    (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 ys
           (t with vs_inst_idx := k) G2 tn2) ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  Induct_on `xs`
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  first_x_assum irule >>
  qexistsl_tac [`G1`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tn1`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem inst_seq_ptr_uniform_append:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = OK t /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn xs
         (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 ys
         (t with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys)
        (s with vs_inst_idx := k) G2 tn2
Proof
  rpt strip_tac >> irule inst_seq_ptr_append >>
  conj_tac >- simp[] >> qexistsl_tac [`G1`, `t with vs_inst_idx := k`, `tn1`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem inst_seq_ptr_abort_append:
  !xs s a t G tn G1 tn1 ys.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = Abort a t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G1 tn1
Proof
  Induct_on `xs` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  first_x_assum irule >> conj_tac
  >- (qexistsl_tac [`a`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
      simp[run_inst_seq_inst_idx, exec_result_map_def]) >> simp[]
QED

Theorem inst_seq_ptr_uniform_abort_append:
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  run_inst_seq xs s = Abort a t /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn xs
         (s with vs_inst_idx := k) G1 tn1) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys)
        (s with vs_inst_idx := k) G1 tn1
Proof
  rpt strip_tac >> irule inst_seq_ptr_abort_append >> conj_tac
  >- (qexistsl_tac [`a`, `t with vs_inst_idx := k`] >>
      simp[run_inst_seq_inst_idx, exec_result_map_def]) >> simp[]
QED
