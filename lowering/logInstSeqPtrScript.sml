(* Successful straight-line pointer sequences, with explicit cursors. *)
Theory logInstSeqPtr
Ancestors
  fragGasSeqPtr fragExec instIdxIndep ghostPcTransportPtr exprLoweringProps
  ptrSafeRun venomExecSemantics venomInst venomState list arithmetic

Theorem inst_seq_ptr_singleton:
  ptr_inst_ok D lo 0 ctx fn G tn i s /\ step_inst_base i s = OK t ==>
  inst_seq_ptr D lo ctx fn PG G tn [i] s
    (step_prov PG G i t) (step_taint i s t tn)
Proof
  simp[inst_seq_ptr_def]
QED

Theorem inst_seq_ptr_append:
  !xs s t G tn H tm ys K tk.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s H tm /\
    inst_seq_ptr D lo ctx fn PG H tm ys
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) K tk ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s K tk
Proof
  Induct >> simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by fs[EVERY_MEM] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`H`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tm`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >>
  metis_tac[ADD_CLAUSES]
QED

(* A two-step consumer keeps the caller's cursor, including nonzero cursors. *)
Theorem inst_seq_ptr_pair:
  ptr_inst_ok D lo 0 ctx fn G tn i s /\ step_inst_base i s = OK t /\
  ptr_inst_ok D lo 0 ctx fn (step_prov PG G i t) (step_taint i s t tn)
    j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst_base j (t with vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  inst_seq_ptr D lo ctx fn PG G tn [i;j] s
    (step_prov PG (step_prov PG G i t) j u)
    (step_taint j (t with vs_inst_idx := SUC s.vs_inst_idx) u
      (step_taint i s t tn))
Proof
  simp[inst_seq_ptr_def]
QED
