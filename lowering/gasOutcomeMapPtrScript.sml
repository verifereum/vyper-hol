(* Pure source result maps retain exactly the same counted pointer path. *)
Theory gasOutcomeMapPtr
Ancestors
  gasSummaryComposePtr fragGasPathPtr vyperInterpreter vyperState list
Libs
  monadsyntax

Theorem ignore_bind_map_return:
  ignore_bind (bind source (\v. return (f v))) (return ()) =
  ignore_bind source (return ())
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >> gen_tac >>
  Cases_on `source x` >> rename1 `source x = (res,ee)` >>
  Cases_on `res` >> simp[]
QED

Theorem gas_marked_exec_ptr_map_return:
  gas_marked_exec_ptr D (ctx,func) PG source (es,s0,G0,tn0) marks res ee G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG (bind source (\v. return (f v)))
    (es,s0,G0,tn0) marks (case res of INL v => INL (f v) | INR ex => INR ex)
    ee G tn r
Proof
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  gen_tac >> simp[bind_def] >> Cases_on `res` >> simp[return_def]
QED

Theorem gas_summary_ptr_at_map_return:
  gas_summary_ptr_at D (ctx,func) PG marks source (es,s0,G0,tn0) P E /\
  (!res ee G tn t. P res ee G tn t ==>
    Q (case res of INL v => INL (f v) | INR ex => INR ex) ee G tn t) /\
  (!res ee gt r. E res ee gt r ==>
    R (case res of INL v => INL (f v) | INR ex => INR ex) ee gt r) ==>
  gas_summary_ptr_at D (ctx,func) PG marks (bind source (\v. return (f v)))
    (es,s0,G0,tn0) Q R
Proof
  simp[gas_summary_ptr_at_marked] >> rpt strip_tac >>
  drule gas_marked_exec_ptr_map_return >>
  disch_then (qspec_then `f` assume_tac) >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem gas_outcome_ptr_map_return:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) P E /\
  (!res ee G tn t. P res ee G tn t ==>
    Q (case res of INL v => INL (f v) | INR ex => INR ex) ee G tn t) /\
  (!res ee gt r. E res ee gt r ==>
    R (case res of INL v => INL (f v) | INR ex => INR ex) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind source (\v. return (f v)))
    (es,s0,G0,tn0) Q R
Proof
  simp[gas_outcome_ptr_def] >> rpt strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule_all gas_summary_ptr_at_map_return >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  simp[ignore_bind_map_return] >> metis_tac[]
QED
