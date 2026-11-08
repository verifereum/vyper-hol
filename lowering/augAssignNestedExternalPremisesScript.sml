(* Target and expression boundaries for the checked External artifact tuple. *)
Theory augAssignNestedExternalPremises
Ancestors augAssignNestedExternalArtifactAudit augAssignNestedExternalBodyInv
  augAssignNestedExternalCallerProbe augAssignNestedExternalEntryProbe
  augAssignNestedCalleeFacts augAssignNestedReachProbe augAssignNestedPremiseProbe
  targetPlaceSimCases bodySimCallIntcall bodySimExprCases exprSimLiteralWord
  vyperTypeCallStackSoundness vyperTypeCallGraphSoundness vyperContext vyperInterpreter
  exprSimHypsDefs vyperState vyperTypeInvariants
Libs finite_mapLib computeLib supportedEvalLib

val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset

Theorem nested_external_index_body_ok:
  body_expr_ok nested_external_cx
    (Call (BaseT (UintT 256)) (IntCall (NONE,"f")) [] NONE)
Proof
  irule intcall_body_expr_ok >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `get_module_code nested_external_cx NONE = SOME nested_external_tops` by EVAL_TAC >>
  `~nested_external_cx.in_deploy` by EVAL_TAC >>
  gvs[lift_option_type_def, nested_external_tops_def, nested_reach_tops_def,
      lookup_callable_function_def, lookup_function_def, return_def, AllCaseEqs()] >>
  simp[nested_replacement_body_ok,
       bodySimTheory.body_exprs_ok_def, bodySimTheory.body_results_ok_def]
QED

Theorem nested_external_target_case:
  !tops ctx func cenv.
    body_inv tops ctx cenv nested_external_cx ==>
    target_case F ctx func cenv nested_external_cx nested_reach_target
Proof
  rpt strip_tac >> irule target_case_all >>
  `body_expr_ok nested_external_cx
    (Literal (BaseT (UintT 256)) (IntL 0))` by
    (irule body_expr_ok_intro >> simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  drule_all body_expr_ok_case >> strip_tac >>
  mp_tac nested_external_index_body_ok >>
  disch_then (mp_then Any mp_tac body_expr_ok_case) >>
  simp[] >> strip_tac >>
  simp[nested_reach_target_def, targetPlaceSimTheory.target_idx_case_def] >> metis_tac[]
QED

Theorem nested_external_call_safe:
  call_evaluation_safe nested_external_cx [(NONE,"f")]
Proof
  rewrite_tac[call_evaluation_safe_def] >>
  qexistsl [`[((NONE,""),(NONE,"f")); ((NONE,"probe"),(NONE,"f"))]`,
            `(NONE,"")`, `[]`] >>
  EVAL_TAC >> simp[] >> conj_tac
  >- (qmatch_goalsub_abbrev_tac `TC R` >>
      `transitive R` by
        (simp[Abbr `R`, relationTheory.transitive_def, call_edge_rel_def] >>
         rpt strip_tac >> gvs[]) >>
      drule relationTheory.transitive_TC_identity >> disch_then SUBST1_TAC >>
      simp[Abbr `R`, relationTheory.irreflexive_def, call_edge_rel_def]) >>
  simp[lookup_function_def] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem nested_external_no_calls_safe:
  call_evaluation_safe nested_external_cx []
Proof
  irule call_evaluation_safe_mono >>
  qexists `[(NONE,"f")]` >> simp[nested_external_call_safe]
QED

Theorem nested_external_indices:
  target_indices_pre nested_external_slice_cenv nested_external_cx
    nested_external_artifact_env nested_reach_target
Proof
  rewrite_tac[nested_reach_target_def,
    targetPlaceSimTheory.target_indices_pre_def, expr_body_pre_def] >>
  `get_tenv nested_external_cx = type_env (cx_tops nested_external_cx)` by EVAL_TAC >>
  `cx_tops nested_external_cx = nested_external_tops` by EVAL_TAC >>
  simp[nested_external_supported] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``call_evaluation_safe``, ``expr_sim_inv``,
    ``nested_external_slice_cenv``, ``nested_external_artifact_env``,
    ``nested_external_cx``, ``supported_program``, ``nested_external_tops``]) >>
  simp[nested_external_call_safe, nested_external_no_calls_safe,
       nested_external_supported] >>
  gen_tac >> disch_then kall_tac >> conj_tac
  >- (rewrite_tac[nested_external_artifact_env_normal] >> EVAL_TAC >> simp[]) >>
  qexists `nested_external_tops` >> simp[nested_external_supported] >> EVAL_TAC >> simp[]
QED

Theorem nested_external_rhs_pre:
  expr_body_pre nested_external_slice_cenv nested_external_cx
    nested_external_artifact_env (Literal (BaseT (UintT 256)) (IntL 1)) nested_premise_es
Proof
  simp[expr_body_pre_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``expr_sim_inv``, ``nested_external_cx``,
    ``call_evaluation_safe``, ``nested_external_slice_cenv``,
    ``nested_external_artifact_env``, ``nested_premise_es``]) >>
  simp[nested_external_artifact_expr_inv, nested_external_no_calls_safe] >>
  rewrite_tac[nested_external_artifact_env_normal] >> EVAL_TAC >> simp[]
QED

(* RHS simulation is supplied directly by compile_literal_word_sim;
   no specialized duplicate of nested_external_rhs_case is needed. *)
