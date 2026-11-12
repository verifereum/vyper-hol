(* Uniform suffix checks accommodate the cursor advanced by the prefix. *)
Theory instSeqComposePtr
Ancestors exprLoweringProps fragGasSeqPtr ghostPcTransportPtr instIdxIndep fragExec
  venomExecSemantics venomState venomInst list arithmetic

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

(* Pointer checks also compose at the counted endpoint itself:
   revert-forwarding exemptions in ptr_inst_ok are cursor-sensitive. *)
Theorem inst_seq_ptr_append_ok:
  !xs s t G tn G1 tn1 ys G2 tn2.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s G1 tn1 /\
    inst_seq_ptr D lo ctx fn PG G1 tn1 ys
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) G2 tn2 ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s G2 tn2
Proof
  Induct_on `xs`
  >- simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  first_x_assum irule >>
  qexistsl [`G1`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tn1`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >>
  fs[ADD_CLAUSES]
QED

(* Successful whole runs expose phase endpoints without operational unfolding. *)
Theorem run_inst_seq_append_ok_split:
  run_inst_seq (xs ++ ys) s = OK t ==>
  ?u. run_inst_seq xs s = OK u /\ run_inst_seq ys u = OK t
Proof
  Cases_on `run_inst_seq xs s`
  >- (drule run_inst_seq_append >> disch_then (qspec_then `ys` assume_tac) >>
      strip_tac >> qexists_tac `v` >> fs[]) >>
  simp[run_inst_seq_append_err]
QED
