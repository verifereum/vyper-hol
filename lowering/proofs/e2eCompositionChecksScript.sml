(* TASK054 focused composition regressions and saved-kernel receipt.
 * This is not a stage producer, project audit umbrella, or fixture rollup.
 * Every theorem below checks an actual outcome/transport boundary.
 *)
Theory e2eCompositionChecks
Ancestors
  e2eComposition e2eCorrectness configuredE2ECorrectness
  e2eDefs vyperLoweringCorrect unitTransformDefs codegenCorrectness
  venomExecSemantics venomState stateEquiv vyperInterpreter vyperValue
  frameOutcome callTrace vfmDecreasesGas list

(* Exemption still supplies an actual run, without pipeline or codegen. *)
Theorem exempt_source_actual_run:
  source_exempt tops (call_external (SOME (MAP SND (call_trace es))) [] am tx) ==>
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

(* Frozen public §8.1 schema: no compiler policy, entry assumptions, memory
 * assumptions, environment requirements, or extra source boundary premise.
 * This comparison checks the SAVED theorem, including quantifier order. *)
val expected_composition = ``
  !tops ret am tx ctx ctx' vs es.
    vs.vs_outcomes = MAP SND (call_trace es) /\
    (?fuel. external_call_result_rel tops ret tx
              (call_external (SOME vs.vs_outcomes) [] am tx)
              (run_context fuel ctx vs)) /\
    (~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) ==>
       ctx_transform_correct ctx ctx' vs /\
       !fuel. ?r es'.
         run_call es = SOME (r, es') /\
         (frame_resource_starved es r es' \/ precompile_call_starved es \/
          venom_frame_rel es r es' (run_context fuel ctx' vs)))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/ precompile_call_starved es \/
             call_result_rel tops ret am tx es r es')``;
val saved_composition = DB.fetch "e2eCorrectness" "e2e_vyper_to_evm";
val () = if Term.aconv expected_composition (Thm.concl saved_composition)
         then print "TASK054 EXACT §8.1 schema: PASS; explicit stages 1/2/3\n"
         else raise Fail "TASK054 public composition schema changed";

fun check_saved (thy, name) =
  let
    val th = DB.fetch thy name
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    val _ = if null (Thm.hyp th) andalso null axioms andalso
               List.all (fn s => s = "DISK_THM") oracles then ()
            else raise Fail ("TASK054 unclosed/admitted object: " ^ thy ^ "." ^ name)
  in
    print ("TASK054 OBJECT " ^ thy ^ "." ^ name ^
           " Hyp=0 axioms=[] admissions=[] (DISK_THM bookkeeping only)\n")
  end;
val () = check_saved ("e2eCorrectness", "e2e_vyper_to_evm");
val () = check_saved ("vfmDecreasesGas", "run_call_eq_tr");
val () = List.app (fn (name, _) => check_saved ("e2eComposition", name))
                 (DB.theorems "e2eComposition");
val () = List.app (fn (name, _) => check_saved ("e2eCompositionChecks", name))
                 (DB.theorems "e2eCompositionChecks");

(* TASK056: the replacement top is explicitly stage-admitted, NOT a clean
 * certificate. The seven exact logical leaves are checked by cheat_audit deps.
 * Deployment is a separate off-call-path planned admission. *)
fun check_classified_stage (thy, name) =
  let
    val th = DB.fetch thy name
    val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    val _ = if null (Thm.hyp th) andalso null axioms then ()
            else raise Fail ("TASK056 broken classified stage: " ^ thy ^ "." ^ name)
  in
    print ("TASK056 CLASSIFIED STAGE " ^ thy ^ "." ^ name ^
           " Hyp=0 axioms=[] oracles=[" ^ String.concatWith "," oracles ^
           "] NOT a clean certificate\n")
  end;
val () = List.app check_classified_stage
  [("e2eCorrectness", "vyper_call_correct"),
   ("e2eCorrectness", "e2e_deploy_correctness")];
