(* Pure source result maps retain exactly the same counted pointer path. *)
Theory gasOutcomeMapPtr
Ancestors
  gasSummaryComposePtr fragGasPathPtr gasStorage vyperStorageTrace
  vyperInterpreter vyperState list
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
  gas_summary_ptr_at D (ctx,func) PG cx st0 marks source (es,s0,G0,tn0) P E /\
  (!H res ee G tn t. P H res ee G tn t ==>
    Q H (case res of INL v => INL (f v) | INR ex => INR ex) ee G tn t) /\
  (!H res ee gt r. E H res ee gt r ==>
    R H (case res of INL v => INL (f v) | INR ex => INR ex) ee gt r) ==>
  gas_summary_ptr_at D (ctx,func) PG cx st0 marks
    (bind source (\v. return (f v))) (es,s0,G0,tn0) Q R
Proof
  rewrite_tac[gas_summary_ptr_at_marked] >> strip_tac >>
  qexistsl_tac [`case res of INL v => INL (f v) | INR ex => INR ex`,
                `es_end`, `G`, `tn`, `r`] >>
  conj_tac
  >- (gen_tac >> simp[bind_def] >> Cases_on `res` >> simp[return_def]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule gas_marked_exec_ptr_map_return >>
  disch_then (qspec_then `f` assume_tac) >> simp[] >> metis_tac[]
QED

Theorem gas_outcome_ptr_map_return:
  gas_outcome_ptr D tops (ctx,func) PG cx st0 source (es,s0,G0,tn0) P E /\
  (!H res ee G tn t. P H res ee G tn t ==>
    Q H (case res of INL v => INL (f v) | INR ex => INR ex) ee G tn t) /\
  (!H res ee gt r. E H res ee gt r ==>
    R H (case res of INL v => INL (f v) | INR ex => INR ex) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (bind source (\v. return (f v))) (es,s0,G0,tn0) Q R
Proof
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_return])
  >- (disj2_tac >> disj1_tac >>
      irule gas_summary_ptr_at_map_return >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> simp[ignore_bind_map_return] >> metis_tac[]
QED
