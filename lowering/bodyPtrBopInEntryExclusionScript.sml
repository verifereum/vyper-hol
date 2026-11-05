(* Semantic outcome elimination for the entry-exclusion test. *)
Theory bodyPtrBopInEntryExclusion
Ancestors bodyPtrBopInSemanticBoundary bodyPtrBopInSourceFrame
  gasExemptCert gasSummary gasOutcome exprSimDefs

Theorem successful_source_outcome_path:
  (!gs. source (es with gas_obs := gs) =
        (INL v, ee with gas_obs := gs)) /\
  gas_outcome memory tops (ctx, func) source (es, s0) Q R /\
  (!res st r. R res st r ==> ~(?x. res = INL x)) ==>
  ?(marks : bool list) t. gas_marked_path memory ctx func s0 (LENGTH marks) (OK t) /\
            Q (INL v) (ee with gas_obs := []) t
Proof
  strip_tac >>
  gvs[gas_outcome_def, gas_summary_at_def, gas_marked_exec_def]
  >- (first_x_assum (qspec_then `[]` mp_tac) >>
      strip_tac >> gvs[] >>
      `ee with gas_obs := [] = es_end with gas_obs := []` by
        (gvs[vyperStateTheory.evaluation_state_component_equality]) >>
      metis_tac[])
  >- (qpat_x_assum `!tail. _` (qspec_then `[]` strip_assume_tac) >>
      metis_tac[])
  >> drule gas_exempt_cert_execution >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def]
QED

Theorem string_membership_source_success:
  bind (eval_expr cx probe_expr) (read_result cx) es =
    (INL (BoolV T), es)
Proof
  simp[probe_expr_def, vyperInterpreterTheory.evaluate_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.read_result_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def, vyperContextTheory.builtin_args_length_ok_def,
       vyperValueTheory.compatible_bound_def,
       vyperValueOperationTheory.evaluate_literal_def,
       vyperStateTheory.lift_sum_def, vyperASTTheory.expr_type_def,
       probe_make_array_builtin, probe_in_builtin]
QED

Theorem string_membership_semantic_path:
  expr_sim ctx func cenv cx ty probe_expr es /\
  lower_value compile_expr cenv ty probe_expr sa = (op, sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx probe_expr) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?(marks : bool list) t.
    gas_marked_path F ctx func s0 (LENGTH marks) (OK t) /\
    expr_post ctx func cenv cx probe_expr es sa sb s0
      (es with gas_obs := []) (BoolV T) op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_def] >> disch_then drule >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pos (el 2)) successful_source_outcome_path >>
  simp[string_membership_source_success, expr_exit_INL] >>
  disch_then (qspecl_then [`BoolV T`, `es`] mp_tac) >>
  impl_tac >- metis_tac[expr_exit_INL] >> simp[]
QED
