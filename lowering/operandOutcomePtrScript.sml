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

Theorem gas_marked_exec_ptr_map_return:
  gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0)
    marks res ee G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (do v <- source; return (f v) od) (es,s0,G0,tn0)
    marks (case res of INL v => INL (f v) | INR exc => INR exc) ee G tn r
Proof
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  simp[] >> gen_tac >> simp[bind_def] >>
  Cases_on `res` >> simp[return_def]
QED

Theorem ignore_map_return:
  ignore_bind (do v <- source; return (f v) od) (return ()) =
  ignore_bind source (return ())
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >>
  qx_gen_tac `s` >> Cases_on `source s` >> Cases_on `q` >> simp[bind_def, return_def]
QED

Theorem gas_outcome_ptr_map_return:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R /\
  (!res ee G tn t. Q res ee G tn t ==>
    Q' (case res of INL v => INL (f v) | INR exc => INR exc) ee G tn t) /\
  (!res ee gt r. R res ee gt r ==>
    R' (case res of INL v => INL (f v) | INR exc => INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (do v <- source; return (f v) od) (es,s0,G0,tn0) Q' R'
Proof
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_ptr_map_return >> metis_tac[])
  >- (qexists_tac `marks` >> disj1_tac >>
      drule gas_marked_exec_ptr_map_return >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  simp[ignore_map_return] >> metis_tac[]
QED
