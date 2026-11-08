(* The audited External tuple fails its first expression invariant:
   its environment still lists the external probe as an internal callable. *)
Theory augAssignNestedExternalApplicability
Ancestors augAssignNestedExternalBodyInv augAssignNestedExternalSemanticAudit
  augAssignNestedExternalCallerProbe augAssignNestedExternalEntryProbe
  augAssignNestedPremiseProbe augAssignNestedNormalizedProbe
  vyperTypeInvariants exprSimHypsDefs
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_external_fn_sigs_inconsistent:
  ~fn_sigs_consistent nested_external_env.fn_sigs nested_external_cx
Proof
  rewrite_tac[fn_sigs_consistent_def] >> strip_tac >>
  first_x_assum (qspecl_then [`NONE`, `"probe"`,
    `<|param_types := []; num_defaults := 0; ret_ty := NoneT|>`] mp_tac) >>
  EVAL_TAC >> simp[vyperInterpreterTheory.lookup_function_def]
QED

Theorem nested_external_context_excluded:
  ~env_context_consistent nested_external_env nested_external_cx
Proof
  simp[env_context_consistent_def, nested_external_fn_sigs_inconsistent]
QED

Theorem nested_external_expr_inv_excluded:
  ~expr_sim_inv nested_external_slice_cenv nested_external_cx
    nested_external_env nested_premise_es
Proof
  simp[expr_sim_inv_def, env_consistent_def, nested_external_context_excluded]
QED
