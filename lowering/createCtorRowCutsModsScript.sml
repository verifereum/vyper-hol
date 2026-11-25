(* Source and compiler facts for the observed constructor-row cuts. *)
Theory createCtorRowCutsMods
Ancestors
  exprSimWordArgs exprLoweringProps vyperStorageTrace vyperStorageFootprint
  vyperState list rich_list

Theorem ctor_rows_source_mods:
  LENGTH vs = LENGTH args /\
  (!i. i < LENGTH args ==>
    vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
      (INL (EL i vs), E (SUC i))) ==>
  !i. i <= LENGTH args ==>
    eval_exprs cx (DROP i args) (E i) = (INL (DROP i vs), E (LENGTH args))
Proof
  strip_tac >> gen_tac >> measureInduct_on `LENGTH args - i` >> strip_tac >>
  Cases_on `i = LENGTH args` >- fs[eval_exprs_nil] >>
  `i < LENGTH args /\ i < LENGTH vs` by decide_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  imp_res_tac DROP_CONS_EL >>
  simp[eval_exprs_cons_action, bind_def, return_def]
QED

Theorem ctor_rows_read_horizon_mods:
  vyperState$bind (eval_expr cx e) (read_result cx) es = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (vyperState$bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
  drule_all_then ACCEPT_TAC valid_horizon_frame
QED

Theorem ctor_rows_horizon_mods:
  eval_exprs cx xs es = (res,ee) /\ valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  metis_tac[valid_horizon_frame, cj 6 evaluate_storage_trace_frame]
QED

Theorem ctor_rows_suffix_cuts_mods:
  (!i. i < n ==> ci_mono (C i) (C (SUC i)) /\ (St (SUC i)).vs_labels = (St i).vs_labels) ==>
  !i. i <= n ==> ci_mono (C i) (C n) /\ (St n).vs_labels = (St i).vs_labels
Proof
  strip_tac >> gen_tac >> measureInduct_on `n - i` >> strip_tac >>
  Cases_on `i = n` >- simp[ci_mono_refl] >>
  `i < n` by decide_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qpat_x_assum `!j. j < n ==> _` drule >> metis_tac[ci_mono_trans]
QED
