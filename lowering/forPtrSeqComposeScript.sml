(* Successful finite pointer sequences, uniform in the instruction cursor. *)
Theory forPtrSeqCompose
Ancestors exprLoweringProps fragExec fragGasSeqPtr ghostPcTransportPtr instIdxIndep venomInst
  venomExecSemantics venomState ptrSafeRun ptrDiscipline list

Theorem for_inst_seq_ptr_cons:
  (!k. inst_seq_ptr D lo ctx fn PG G tn [i]
         (s with vs_inst_idx := k) G1 tn1) /\
  (!k. ?u. step_inst_base i (s with vs_inst_idx := k) = OK u /\
           !j. (u with vs_inst_idx := j) = (v with vs_inst_idx := j)) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 code
         (v with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (i::code)
        (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `!k. ?u. _` (qspec_then `k` strip_assume_tac) >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _`
    (qspec_then `k` mp_tac) >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  qpat_x_assum `!j. _ = _` (qspec_then `SUC k` assume_tac) >>
  simp[inst_seq_ptr_def] >> metis_tac[]
QED

Theorem for_inst_seq_ptr_cons_exact:
  (!k. inst_seq_ptr D lo ctx fn PG G tn [i]
         (s with vs_inst_idx := k) G1 tn1) /\
  (!k. step_inst_base i (s with vs_inst_idx := k) =
         OK (v with vs_inst_idx := k)) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 code
         (v with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (i::code)
        (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >> irule for_inst_seq_ptr_cons >>
  qexistsl [`G1`, `tn1`, `v`] >> simp[]
QED

Theorem for_inst_seq_ptr_cons_nonterminator:
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK v /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn [i]
         (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 code
         (v with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (i::code)
        (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >> irule for_inst_seq_ptr_cons_exact >>
  qexistsl [`G1`, `tn1`, `v`] >>
  simp[step_inst_inst_idx_indep, exec_result_map_def]
QED

Theorem for_inst_seq_ptr_append:
  !pre s t G tn G1 tn1 post G2 tn2.
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  run_inst_seq pre s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn pre s G1 tn1 /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 post
    (t with vs_inst_idx := k) G2 tn2) ==>
  inst_seq_ptr D lo ctx fn PG G tn (pre ++ post) s G2 tn2
Proof
  Induct_on `pre`
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  rpt gen_tac >> simp[run_inst_seq_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  gvs[inst_seq_ptr_def] >> first_x_assum irule >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem for_inst_seq_ptr_append_uniform:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  run_inst_seq pre s = OK t /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn pre
    (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 post
    (t with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (pre ++ post)
    (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >> gen_tac >> irule for_inst_seq_ptr_append >>
  conj_tac >- simp[] >>
  qexistsl [`G1`, `t with vs_inst_idx := k`, `tn1`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED
