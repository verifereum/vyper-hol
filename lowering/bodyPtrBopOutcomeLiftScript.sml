Theory bodyPtrBopOutcomeLift
Ancestors
  fragGasPathPtr gasOutcome gasSummary fragGasMode

(* Preserve the inherited semantic witness, not merely its exit cursor. *)
Theorem bop_outcome_ptr_lift:
  gas_outcome F tops (ctx,fn) source (es,s0) Q R /\
  (!n res ee r.
    gas_path ctx fn s0 n r /\
    ((?t. r = OK t /\ Q res ee t) \/ (exit_result r /\ R res ee r)) ==>
    ?G tn. gas_path_ptr D 0 ctx fn PG G0 tn0 s0 n G tn r /\
      ((?t. r = OK t /\ Qp res ee G tn t) \/
       (exit_result r /\ Rp res ee (G,tn) r))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s0,G0,tn0) Qp Rp
Proof
  simp [gas_outcome_def, gas_outcome_ptr_def,
    gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def,
    gas_summary_ptr_at_def] >>
  metis_tac[]
QED
