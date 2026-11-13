Theory bodyPtrTypeBuiltinsSeq
Ancestors
  fragGasSeqPtr fragExec exprLoweringProps instIdxIndep venomExecSemantics venomState
  venomInst list

(* run_inst_seq does not advance the cursor, whereas the check certificate
   does. A cursor-uniform suffix is the interface for composing both. *)
Theorem inst_seq_ptr_append_run:
  !xs s t G tn H th ys K tk D lo ctx fn PG.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s H th /\
    (!k. inst_seq_ptr D lo ctx fn PG H th ys
      (t with vs_inst_idx := k) K tk) ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s K tk
Proof
  Induct >- (simp[run_inst_seq_def, inst_seq_ptr_def] >>
    rpt strip_tac >> first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, Once inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  simp[Once inst_seq_ptr_def] >>
  first_x_assum irule >>
  qexistsl_tac [`H`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `th`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def]
QED
