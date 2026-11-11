(* Terminal DSE relations and result composition. Extracted from
   deadStoreElimProofs so simulation helpers can use them without a cycle. *)
Theory deadStoreElimEquiv
Ancestors
  deadStoreElimDefs passSharedProps stateEquiv stateEquivProps
  venomExecSemantics deadStoreElimFrame
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_equiv_refl:
  !space s. dse_equiv space s s
Proof
  simp[dse_equiv_def]
QED

Theorem dse_equiv_trans:
  !space s1 s2 s3.
    dse_equiv space s1 s2 /\ dse_equiv space s2 s3 ==>
    dse_equiv space s1 s3
Proof
  simp[dse_equiv_def] >> metis_tac[]
QED

Theorem dse_equiv_implies_all:
  !space s1 s2. dse_equiv space s1 s2 ==> dse_all_equiv s1 s2
Proof
  simp[dse_equiv_def, dse_all_equiv_def]
QED

Theorem dse_all_equiv_refl:
  !s. dse_all_equiv s s
Proof
  simp[dse_all_equiv_def]
QED

Theorem dse_all_equiv_trans:
  !s1 s2 s3.
    dse_all_equiv s1 s2 /\ dse_all_equiv s2 s3 ==>
    dse_all_equiv s1 s3
Proof
  simp[dse_all_equiv_def] >> metis_tac[]
QED

Theorem state_equiv_empty_implies_dse_equiv:
  !space s1 s2. state_equiv {} s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[state_equiv_def, execution_equiv_def, dse_equiv_def,
       lookup_var_def] >>
  rpt strip_tac >>
  `FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v`
    by metis_tac[pred_setTheory.NOT_IN_EMPTY] >> gvs[]
QED

Theorem execution_equiv_empty_implies_dse_equiv:
  !space s1 s2. execution_equiv {} s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[execution_equiv_def, dse_equiv_def, lookup_var_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

(* Result relations of a DSE run: the per-space or combined relation on OK
   and Abort, dse_term_equiv on Halt/IntRet. *)
Theorem lift_result_dse_term_trans:
  !space r1 r2 r3.
    lift_result (dse_equiv space) dse_term_equiv (dse_equiv space) r1 r2 /\
    lift_result (dse_equiv space) dse_term_equiv (dse_equiv space) r2 r3 ==>
    lift_result (dse_equiv space) dse_term_equiv (dse_equiv space) r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_trans]
QED

Theorem lift_result_dse_all_term_trans:
  !r1 r2 r3.
    lift_result dse_all_equiv dse_term_equiv dse_all_equiv r1 r2 /\
    lift_result dse_all_equiv dse_term_equiv dse_all_equiv r2 r3 ==>
    lift_result dse_all_equiv dse_term_equiv dse_all_equiv r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[dse_all_equiv_trans, dse_equiv_trans]
QED

Theorem lift_result_dse_term_to_all:
  !space r1 r2.
    lift_result (dse_equiv space) dse_term_equiv (dse_equiv space) r1 r2 ==>
    lift_result dse_all_equiv dse_term_equiv dse_all_equiv r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_implies_all]
QED

Theorem lift_result_dse_equiv_to_all:
  !space r1 r2.
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2 ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_implies_all]
QED

Theorem lift_result_dse_equiv_term:
  !space r1 r2.
    (!sp. lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp) r1 r2) ==>
    lift_result (dse_equiv space) dse_term_equiv (dse_equiv space) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def]
QED

Theorem lift_result_or_error_trans:
  !R (r1:exec_result) r2 r3.
    ((?e. r1 = Error e) \/ lift_result R R R r1 r2) /\
    ((?e. r2 = Error e) \/ lift_result R R R r2 r3) /\
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) ==>
    (?e. r1 = Error e) \/ lift_result R R R r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[]
QED

Theorem lift_result_or_error_equiv_to_all:
  !space (r1:exec_result) r2.
    ((?e. r1 = Error e) \/ lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2) ==>
    (?e. r1 = Error e) \/ lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2
Proof
  rpt strip_tac >> gvs[] >>
  disj2_tac >> irule lift_result_dse_equiv_to_all >> qexists `space` >> simp[]
QED

Theorem result_equiv_empty_implies_lift_result_dse_equiv:
  !space r1 r2.
    result_equiv {} r1 r2 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def, result_equiv_def] >>
  metis_tac[state_equiv_empty_implies_dse_equiv, execution_equiv_empty_implies_dse_equiv]
QED

Theorem clear_nops_function_dse_equiv:
  !space fuel ctx fn s.
    wf_function fn /\
    s.vs_inst_idx = 0 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (clear_nops_function fn) s)
Proof
  rpt strip_tac >> irule result_equiv_empty_implies_lift_result_dse_equiv >> irule clear_nops_function_correct >> simp[]
QED
