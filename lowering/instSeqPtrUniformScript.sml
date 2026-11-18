(* The final pointer ghost is uniform across the masks checking a run. *)
Theory instSeqPtrUniform
Ancestors fragGasSeqPtr

Theorem inst_seq_ptr_uniformize:
  (!D. ?H th.
    (!q. inst_seq_ptr D lo ctx fn PG G tn code (entry (q:num)) H th) /\ P H th) ==>
  ?H th.
    (!D q. inst_seq_ptr D lo ctx fn PG G tn code (entry q) H th) /\ P H th
Proof
  strip_tac >>
  first_assum (qspec_then `ARB` (qx_choose_then `H` (qx_choose_then `th` strip_assume_tac))) >>
  qexistsl_tac [`H`,`th`] >> simp[] >> rpt gen_tac >>
  first_x_assum (qspec_then `D` (qx_choose_then `H1` (qx_choose_then `th1` strip_assume_tac))) >>
  `H1 = H /\ th1 = th` by
    (irule inst_seq_ptr_ghost_unique >> metis_tac[]) >>
  gvs[]
QED
