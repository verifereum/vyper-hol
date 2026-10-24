(* PLAN §8.1 composition helpers. No stage theorem is used here.
 * TOP-LEVEL: raw-result termination/transport, source exemption,
 *   successful and failed frame composition, unconditional run_call totality.
 * Requests are compared on return and halt; abort transport retains revert kind.
 *)
Theory e2eComposition
Ancestors
  e2eDefs vyperLoweringCorrect unitTransformDefs codegenCorrectness
  passSimulationDefs stateEquiv venomExecSemantics venomState
  vyperInterpreter vyperValue vfmDecreasesGas vfmExecution frameOutcome callTrace
  list pair

(* ===== Actual EVM run, including exempt source failures ===== *)

Theorem run_call_total:
  !es. ?r es'. run_call es = SOME (r, es')
Proof
  gen_tac >> simp[run_call_eq_tr] >>
  Cases_on `run_call_tr (LENGTH es.contexts) (step es)` >> simp[]
QED

Theorem source_exempt_call_result_rel:
  source_exempt tops (call_external (SOME (MAP SND (call_trace es))) am tx) ==>
  call_result_rel tops ret am tx es r es'
Proof
  simp[source_exempt_def, call_result_rel_def, LET_THM] >>
  Cases_on `call_external (SOME (MAP SND (call_trace es))) am tx` >>
  rename1 `call_external _ am tx = (res, tail)` >>
  Cases_on `tail` >> Cases_on `res` >> simp[] >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[]
QED

(* ===== Raw termination and pipeline transport ===== *)

Theorem external_call_result_rel_terminal:
  external_call_result_rel tops ret tx src res ==>
  (?ss. res = Halt ss) \/ (?a ss. res = Abort a ss)
Proof
  PairCases_on `src` >> Cases_on `src0` >> Cases_on `res` >>
  simp[external_call_result_rel_def, AllCaseEqs()]
QED

Theorem external_call_result_rel_terminates:
  external_call_result_rel tops ret tx src res ==> terminates res
Proof
  strip_tac >> drule external_call_result_rel_terminal >>
  rw[terminates_def] >> simp[]
QED

Theorem external_call_result_rel_unit_transport:
  external_call_result_rel tops ret tx src res /\ unit_result_rel res res' ==>
  external_call_result_rel tops ret tx src res'
Proof
  PairCases_on `src` >> Cases_on `res` >> Cases_on `res'` >>
  gvs[unit_result_rel_def, external_call_result_rel_def, AllCaseEqs(),
      observable_equiv_def] >>
  rpt strip_tac >> gvs[] >> rpt CASE_TAC >> gvs[] >>
  rename1 `abort_before <> Revert_abort` >> Cases_on `abort_before` >> gvs[]
QED

(* ===== Frame composition, separated by semantic outcome ===== *)

Theorem venom_frame_rel_abort_failure:
  venom_frame_rel es r es' (Abort a ss) ==>
  ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
Proof
  Cases_on `a` >> simp[venom_frame_rel_def] >>
  rpt strip_tac >> goal_assum $ drule_at Any
QED

Theorem venom_frame_rel_assertion:
  (a = Revert_abort \/ s = "UNREACHABLE") /\
  venom_frame_rel es r es' (Abort a ss) ==>
  ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                (exc = Reverted \/ s = "UNREACHABLE")
Proof
  Cases_on `a` >> simp[venom_frame_rel_def] >>
  rpt strip_tac >> goal_assum $ drule_at Any >> simp[]
QED

Theorem external_call_result_rel_frame_success:
  call_external (SOME (MAP SND (call_trace es))) am tx = (INL v, am', rqs) /\
  external_call_result_rel tops ret tx (INL v, am', rqs) (Halt ss) /\
  venom_frame_rel es r es' (Halt ss) ==>
  call_result_rel tops ret am tx es r es'
Proof
  simp[external_call_result_rel_def, venom_frame_rel_def,
       call_result_rel_def, LET_THM] >>
  rpt strip_tac >> qexistsl_tac [`ss.vs_returndata`, `ss.vs_logs`] >> gvs[]
QED

Theorem external_call_result_rel_frame_assertion:
  call_external (SOME (MAP SND (call_trace es))) am tx =
    (INR (AssertException s), am', rqs) /\
  external_call_result_rel tops ret tx
    (INR (AssertException s), am', rqs) (Abort a ss) /\
  venom_frame_rel es r es' (Abort a ss) ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >> gvs[call_result_rel_def, LET_THM] >>
  irule venom_frame_rel_assertion >> qexistsl_tac [`a`, `ss`] >>
  simp[] >> Cases_on `a` >> gvs[external_call_result_rel_def]
QED

Theorem external_call_result_rel_frame_halt:
  call_external (SOME (MAP SND (call_trace es))) am tx =
    (INR HaltException, am', rqs) /\
  external_call_result_rel tops ret tx
    (INR HaltException, am', rqs) (Halt ss) /\
  venom_frame_rel es r es' (Halt ss) ==>
  call_result_rel tops ret am tx es r es'
Proof
  simp[external_call_result_rel_def, venom_frame_rel_def,
       call_result_rel_def, LET_THM] >>
  rpt strip_tac >> qexists_tac `ss.vs_logs` >> gvs[]
QED

Theorem external_call_result_rel_frame_runtime:
  call_external (SOME (MAP SND (call_trace es))) am tx =
    (INR (Error (RuntimeError m)), am', rqs) /\
  venom_frame_rel es r es' (Abort a ss) ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >> drule venom_frame_rel_abort_failure >>
  simp[call_result_rel_def, LET_THM]
QED

Theorem external_call_result_rel_frame_error:
  call_external (SOME (MAP SND (call_trace es))) am tx =
    (INR (Error e), am', rqs) /\
  external_call_result_rel tops ret tx (INR (Error e), am', rqs) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >> Cases_on `e` >> Cases_on `res` >>
  gvs[external_call_result_rel_def, call_result_rel_def, LET_THM,
      AllCaseEqs()] >>
  FIRST [gvs[venom_frame_rel_def] >> NO_TAC,
         drule venom_frame_rel_abort_failure >> simp[]]
QED

(* Covers all source constructors; escaped control exceptions have no row.
 * A Halt paired with Error can only be the deliberately exempt decoder case.
 *)
Theorem external_call_result_rel_frame:
  external_call_result_rel tops ret tx
    (call_external (SOME (MAP SND (call_trace es))) am tx) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >>
  Cases_on `call_external (SOME (MAP SND (call_trace es))) am tx` >>
  rename1 `call_external _ am tx = (src, tail)` >> Cases_on `tail` >>
  rename1 `call_external _ am tx = (src, am', rqs)` >>
  Cases_on `src`
  >- (Cases_on `res` >>
      FIRST [drule_all external_call_result_rel_frame_success >> simp[],
             gvs[external_call_result_rel_def]]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  FIRST [drule_all external_call_result_rel_frame_error >> simp[],
         Cases_on `res` >>
         FIRST [drule_all external_call_result_rel_frame_assertion >> simp[],
                drule_all external_call_result_rel_frame_halt >> simp[],
                gvs[external_call_result_rel_def]]]
QED
