(* Outcome interfaces for operand sequencing, independent of operand types. *)
Theory operandOutcomePtr
Ancestors
  gasSummaryComposePtr fragGasPathPtr vyperState

Theorem gas_outcome_ptr_marked_conseq:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R /\
  (!marks res mid G tn t.
    gas_marked_exec F (ctx,func) source (es,s0) marks res mid (OK t) /\
    Q res (mid with gas_obs := []) G tn t ==>
    Q' res (mid with gas_obs := []) G tn t) /\
  (!res ee gt r. R res ee gt r ==> R' res ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q' R'
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_ptr_exec >> strip_tac >> metis_tac[]) 
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED
