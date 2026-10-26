(* Composition regressions for outcome and state transport. *)
Theory e2eCompositionChecks
Ancestors
  e2eComposition
  e2eDefs vyperLoweringCorrect unitTransformDefs codegenCorrectness
  venomExecSemantics venomState stateEquiv vyperInterpreter vyperValue
  frameOutcome callTrace vfmDecreasesGas list

(* Exemption still supplies an actual run, without pipeline or codegen. *)
Theorem exempt_source_actual_run:
  source_exempt tops (call_external (SOME (MAP SND (call_trace es))) am tx) ==>
  ?r es'. run_call es = SOME (r, es') /\
          call_result_rel tops ret am tx es r es'
Proof
  strip_tac >> qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  drule source_exempt_call_result_rel >> simp[]
QED

Theorem source_nonterminal_results_rejected:
  ~external_call_result_rel tops ret tx src (Error m) /\
  ~external_call_result_rel tops ret tx src (OK ss) /\
  ~external_call_result_rel tops ret tx src (IntRet vals ss)
Proof
  PairCases_on `src` >> Cases_on `src0` >>
  simp[external_call_result_rel_def]
QED

Theorem source_escaped_control_rejected:
  ~external_call_result_rel tops ret tx (INR BreakException, am', rqs) res /\
  ~external_call_result_rel tops ret tx (INR ContinueException, am', rqs) res /\
  ~external_call_result_rel tops ret tx (INR (ReturnException v), am', rqs) res
Proof
  Cases_on `res` >> simp[external_call_result_rel_def]
QED

(* Pipeline aborts intentionally do NOT equate abort kind or any state field. *)
Theorem pipeline_exceptional_halt_may_revert:
  unit_result_rel (Abort ExHalt_abort raw) (Abort Revert_abort output) /\
  unit_result_rel (Abort ExHalt_abort raw) (Abort ExHalt_abort output) /\
  ~unit_result_rel (Abort Revert_abort raw) (Abort ExHalt_abort output)
Proof
  simp[unit_result_rel_def]
QED

Theorem runtime_failure_no_request_or_data_constraint:
  external_call_result_rel tops ret tx (INR (Error (RuntimeError m)), am', rqs)
    (Abort a (ss with <| vs_requests := different_requests;
                       vs_returndata := different_data;
                       vs_outcomes := remaining_outcomes |>))
Proof
  simp[external_call_result_rel_def]
QED

Theorem ordinary_assert_revert_and_unreachable:
  (external_call_result_rel tops ret tx (INR (AssertException s), am', rqs)
     (Abort ExHalt_abort ss) <=> s = "UNREACHABLE") /\
  external_call_result_rel tops ret tx (INR (AssertException s), am', rqs)
     (Abort Revert_abort ss)
Proof
  simp[external_call_result_rel_def]
QED

(* Successful composition matches requests, but not leftover outcomes. *)
Theorem successful_composition_requests:
  external_call_result_rel tops ret tx (INL v, am', rqs) (Halt raw) /\
  unit_result_rel (Halt raw) (Halt output) /\
  venom_frame_rel es r es' (Halt output) ==>
  rqs = MAP FST (call_trace es)
Proof
  simp[external_call_result_rel_def, unit_result_rel_def,
       observable_equiv_def, venom_frame_rel_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem successful_leftover_outcomes_unobserved:
  (external_call_result_rel tops ret tx (INL v, am', rqs)
     (Halt (ss with vs_outcomes := os)) <=>
   external_call_result_rel tops ret tx (INL v, am', rqs) (Halt ss)) /\
  (venom_frame_rel es r es' (Halt (ss with vs_outcomes := os)) <=>
   venom_frame_rel es r es' (Halt ss))
Proof
  simp[external_call_result_rel_def, venom_frame_rel_def]
QED
