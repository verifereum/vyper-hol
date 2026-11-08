(* Correctness of the ordered supply-threaded memory merging pass. *)
Theory mmBlockSimProofs
Ancestors
  mmCorrectnessProofs mmTraceProofs mmDloadProofs mmLocalScanProofs
  mmTransformSupply dftCorrectnessFinal passSimulationDefs passSimulationProofs
  stateEquiv stateEquivProofs

Theorem mm_function_correct:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn supply fn /\ fn_entry_state fn s /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\ reachability_closed Inv ctx /\
  fn_entry_inv Inv ctx fn s /\
  (!inst st. Inv ctx fn inst st ==> static_mem_ok eom ctx fn inst st) /\
  transform_function_supply supply fn = (fn', supply') ==>
  (?e. run_function fuel ctx fn s = Error e) \/
  lift_result (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (run_function fuel ctx fn s) (run_function fuel ctx fn' s)
Proof
  cheat
QED

Theorem eol_function_pass_correct[local]:
  !R_ok R_term R_abort exec1 exec2.
    (!fuel. (?e. exec1 fuel = Error e) \/
            lift_result R_ok R_term R_abort
              (exec1 fuel) (exec2 fuel)) /\
    (!fuel fuel'. terminates (exec1 fuel) /\ terminates (exec1 fuel') ==>
      exec1 fuel = exec1 fuel') /\
    (!fuel fuel'. terminates (exec2 fuel) /\ terminates (exec2 fuel') ==>
      exec2 fuel = exec2 fuel') /\
    (?f0. terminates (exec1 f0)) ==>
    pass_correct R_ok R_term R_abort exec1 exec2
Proof
  rw[pass_correct_def]
  >- ((* Goal 1: ∃fuel'. terminates (exec2 fuel') *)
      qpat_x_assum `!fuel. _ \/ lift_result _ _ _ _ _`
        (qspec_then `f0` mp_tac) >>
      strip_tac >> gvs[]
      >- (Cases_on `exec1 f0` >> gvs[terminates_def]) >>
      qexists_tac `f0` >>
      Cases_on `exec1 f0` >> Cases_on `exec2 f0` >>
      gvs[lift_result_def, terminates_def])
  >- ((* Goal 2: lift_result when both terminate *)
      qpat_x_assum `!fuel. _ \/ lift_result _ _ _ _ _`
        (qspec_then `fuel` mp_tac) >>
      strip_tac >> gvs[]
      >- (Cases_on `exec1 fuel` >> gvs[terminates_def]) >>
      `terminates (exec2 fuel)` by
        (Cases_on `exec1 fuel` >> Cases_on `exec2 fuel` >>
         gvs[lift_result_def, terminates_def]) >>
      `exec2 fuel' = exec2 fuel` by metis_tac[] >>
      gvs[])
QED

Theorem mm_pass_correct:
  fn_inst_wf fn /\ wf_function fn /\ wf_ssa fn /\
  ir_supply_covers_fn supply fn /\ fn_entry_state fn s /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  eom < dimword (:256) /\ reachability_closed Inv ctx /\
  fn_entry_inv Inv ctx fn s /\
  (!inst st. Inv ctx fn inst st ==> static_mem_ok eom ctx fn inst st) /\
  transform_function_supply supply fn = (fn', supply') /\
  (?fuel. terminates (run_function fuel ctx fn s)) ==>
  pass_correct (state_equiv UNIV) (execution_equiv UNIV) revert_equiv
    (\fuel. run_function fuel ctx fn s)
    (\fuel. run_function fuel ctx fn' s)
Proof
  rpt strip_tac >>
  irule eol_function_pass_correct >>
  BETA_TAC >> rpt conj_tac >>
  metis_tac[mm_function_correct, run_function_fuel_determ]
QED
