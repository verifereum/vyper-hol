(* Successful finite pointer sequences, uniform in the instruction cursor. *)
Theory forPtrSeqCompose
Ancestors fragGasSeqPtr ghostPcTransportPtr instIdxIndep venomInst
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
