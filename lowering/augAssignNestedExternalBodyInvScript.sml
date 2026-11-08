(* Body invariant for the common External tuple, not an old-context transfer. *)
Theory augAssignNestedExternalBodyInv
Ancestors augAssignNestedExternalSemanticAudit bodySim compileVyper
  augAssignNestedExternalEntryProbe augAssignNestedExternalCallerProbe
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_external_body_inv:
  body_inv nested_external_tops nested_external_unit.cu_context
    nested_external_slice_cenv nested_external_cx
Proof
  rewrite_tac[body_inv_def] >>
  conj_tac >- ACCEPT_TAC nested_external_supported >>
  conj_tac
  >- (qexistsl [`nested_premise_policy`, `nested_external_unit`] >>
      `~nested_external_cx.in_deploy` by EVAL_TAC >>
      simp[nested_external_slice_cenv_def, nested_external_compile_env] >>
      conj_tac
      >- (mp_tac nested_external_lowering_exists >>
          Cases_on `lower_vyper_runtime_unit nested_external_tops nested_premise_policy` >>
          simp[nested_external_unit_def]) >> EVAL_TAC) >>
  simp[nested_external_slice_cenv_def, nested_external_compile_env,
       cenv_module_pins_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``nested_external_tops``,
    ``function_selector``, ``calldata_method_id``]) >>
  simp[] >> rpt conj_tac >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``]) >> simp[]
QED
