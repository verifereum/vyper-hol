Theory bodyPtrPopSequenceStep
Ancestors fragGasSeqPtr

(* Goal-directed cons boundary: witnesses remain in the suffix, so concrete
   instruction checks can be reduced independently of the rest of the run. *)
Theorem pop_inst_seq_ptr_cons_exists:
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  (?u. step_inst_base i s = OK u /\
    ?G' tn'. inst_seq_ptr D lo ctx fn PG (step_prov PG G i u)
      (step_taint i s u tn) is
      (u with vs_inst_idx := SUC s.vs_inst_idx) G' tn' /\ P G' tn') ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn (i::is) s G' tn' /\ P G' tn'
Proof
  strip_tac >> qexistsl_tac [`G'`, `tn'`] >> simp[Once inst_seq_ptr_def]
QED
