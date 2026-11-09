(* Invariants of the ghost pair along a checked executed prefix. *)
Theory bodyPtrEnvBuiltinsSequenceFrame
Ancestors fragGasSeqPtr ptrDiscipline venomExecSemantics venomState list

Theorem inst_seq_ptr_invariant:
  !code s G tn G' tn' R.
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' /\ R G tn /\
    (!i u v H q. MEM i code /\ R H q /\ step_inst_base i u = OK v ==>
      R (step_prov PG H i v) (step_taint i u v q)) ==>
    R G' tn'
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum irule >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`step_prov PG G h v`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`, `step_taint h s v tn`] >>
  simp[] >> metis_tac[]
QED
