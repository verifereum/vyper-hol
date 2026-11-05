(* Pointer checks compose at the counted endpoint, not the raw run endpoint:
   revert-forwarding exemptions in ptr_inst_ok are cursor-sensitive. *)
Theory instSeqComposePtr
Ancestors
  fragGasSeqPtr ghostPcTransportPtr fragExec exprLoweringProps instIdxIndep
  venomExecSemantics venomInst venomState list arithmetic

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
