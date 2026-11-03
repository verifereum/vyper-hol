(* PLAN §8.1 composition helpers. No stage theorem is used here.
 * TOP-LEVEL: raw-result termination/transport, source exemption,
 *   successful and failed frame composition, unconditional run_call totality.
 * Requests are compared only on success; abort kinds/data are not equated.
 *)
Theory e2eComposition
Ancestors
  e2eDefs vyperLoweringCorrect unitTransformDefs o1PassContract compileEnv
  accountsRelProps codegenCorrectness
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
  source_exempt tops (call_external (SOME (MAP SND (call_trace es))) [] am tx) ==>
  call_result_rel tops ret am tx es r es'
Proof
  simp[source_exempt_def, call_result_rel_def, LET_THM] >>
  Cases_on `call_external (SOME (MAP SND (call_trace es))) [] am tx` >>
  rename1 `call_external _ _ am tx = (res, tail)` >>
  Cases_on `tail` >> Cases_on `res` >> simp[] >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[]
QED

(* ===== Raw termination and pipeline transport ===== *)

Theorem initial_evaluation_context_txn[local,simp]:
  (initial_evaluation_context srcs layouts tx src_id_opt).txn = tx
Proof
  simp[initial_evaluation_context_def]
QED

Theorem storage_agree_except_storage_dead[local]:
  storage_agree_except {(k,b) | storage_dead cx tr st (w2n k) b} st st' <=>
  storage_agree (storage_dead cx tr st) st st'
Proof
  simp[storage_agree_except_def, word_agree_except_def, key_taint_def,
       storage_agree_def, vfmStateTheory.lookup_storage_def] >>
  metis_tac[]
QED

Theorem storage_agree_except_empty[local]:
  storage_agree_except {} st st' <=> st' = st
Proof
  simp[storage_agree_except_def, word_agree_except_def, key_taint_def,
       FUN_EQ_THM] >>
  metis_tac[word_to_bytes_EL_eq]
QED

Theorem external_call_dead_wf:
  dead_wf (external_call_dead tx src)
Proof
  PairCases_on `src` >>
  rw[dead_wf_def, external_call_dead_def] >>
  Cases_on `a = tx.target` >> gvs[storage_agree_except_storage_dead] >>
  drule storage_agree_storage_dead >> simp[]
QED

Theorem storage_agree_dead_trans[local]:
  storage_agree (storage_dead cx tr st0) st0 st1 /\
  storage_agree (storage_dead cx tr st1) st1 st2 ==>
  storage_agree (storage_dead cx tr st0) st0 st2
Proof
  strip_tac >>
  `storage_dead cx tr st1 = storage_dead cx tr st0` by
    (irule storage_agree_storage_dead >> simp[]) >>
  gvs[storage_agree_def]
QED

(* What accounts_agree_except and transient_agree_except say for the
   source's dead bytes: equal off the running contract, which agrees up to
   storage_dead. *)
Theorem accounts_agree_except_external_call_dead[local]:
  accounts_agree_except (external_call_dead tx (res, am', rqs)) a1 a2 <=>
  (!a. (a1 a with storage := (a2 a).storage) = a2 a) /\
  (!a. a <> tx.target ==> (a1 a).storage = (a2 a).storage) /\
  storage_agree
    (storage_dead (initial_evaluation_context am'.sources am'.layouts tx NONE)
       F (a1 tx.target).storage)
    (a1 tx.target).storage (a2 tx.target).storage
Proof
  simp[accounts_agree_except_def, external_call_dead_def] >> eq_tac
  >- (strip_tac >> rpt conj_tac
      >- (gen_tac >> first_x_assum (qspec_then `a` (ACCEPT_TAC o CONJUNCT1)))
      >- (rpt strip_tac >> first_x_assum (qspec_then `a` mp_tac) >>
          gvs[storage_agree_except_empty]) >>
      first_x_assum (qspec_then `tx.target` mp_tac) >>
      simp[storage_agree_except_storage_dead]) >>
  rpt strip_tac
  >- (first_x_assum (qspec_then `a` ACCEPT_TAC)) >>
  Cases_on `a = tx.target` >>
  gvs[storage_agree_except_storage_dead, storage_agree_except_empty]
QED

Theorem transient_agree_except_external_call_dead[local]:
  transient_agree_except (external_call_dead tx (res, am', rqs)) t1 t2 <=>
  (!a. a <> tx.target ==> t1 a = t2 a) /\
  storage_agree
    (storage_dead (initial_evaluation_context am'.sources am'.layouts tx NONE)
       T (t1 tx.target))
    (t1 tx.target) (t2 tx.target)
Proof
  simp[transient_agree_except_def, external_call_dead_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (rpt strip_tac >> first_x_assum (qspec_then `a` mp_tac) >>
          gvs[storage_agree_except_empty]) >>
      first_x_assum (qspec_then `tx.target` mp_tac) >>
      simp[storage_agree_except_storage_dead]) >>
  rpt strip_tac >> Cases_on `a = tx.target` >>
  gvs[storage_agree_except_storage_dead, storage_agree_except_empty]
QED

Theorem accounts_agree_storage_dead_trans[local]:
  accounts_agree cx a0 a1 /\
  (!a. (a1 a with storage := (a2 a).storage) = a2 a) /\
  (!a. a <> cx.txn.target ==> (a1 a).storage = (a2 a).storage) /\
  storage_agree (storage_dead cx F (a1 cx.txn.target).storage)
    (a1 cx.txn.target).storage (a2 cx.txn.target).storage ==>
  accounts_agree cx a0 a2
Proof
  rw[accounts_agree_def] >>
  TRY (irule storage_agree_dead_trans >>
       qexists_tac `(a1 cx.txn.target).storage` >> gvs[] >> NO_TAC) >>
  gvs[vfmStateTheory.account_state_component_equality]
QED

Theorem transient_agree_storage_dead_trans[local]:
  transient_agree cx t0 t1 /\
  (!a. a <> cx.txn.target ==> t1 a = t2 a) /\
  storage_agree (storage_dead cx T (t1 cx.txn.target))
    (t1 cx.txn.target) (t2 cx.txn.target) ==>
  transient_agree cx t0 t2
Proof
  rw[transient_agree_def] >>
  irule storage_agree_dead_trans >>
  qexists_tac `t1 cx.txn.target` >> gvs[]
QED

Theorem accounts_agree_dead_trans[local]:
  cx = initial_evaluation_context am'.sources am'.layouts tx NONE /\
  accounts_agree cx a0 a1 /\
  accounts_agree_except (external_call_dead tx (res, am', rqs)) a1 a2 ==>
  accounts_agree cx a0 a2
Proof
  rw[accounts_agree_except_external_call_dead] >>
  irule accounts_agree_storage_dead_trans >>
  qexists_tac `a1` >> gvs[]
QED

Theorem transient_agree_dead_trans[local]:
  cx = initial_evaluation_context am'.sources am'.layouts tx NONE /\
  transient_agree cx t0 t1 /\
  transient_agree_except (external_call_dead tx (res, am', rqs)) t1 t2 ==>
  transient_agree cx t0 t2
Proof
  rw[transient_agree_except_external_call_dead] >>
  irule transient_agree_storage_dead_trans >>
  qexists_tac `t1` >> gvs[]
QED

Theorem request_agree_dead_trans[local]:
  cx = initial_evaluation_context am'.sources am'.layouts tx NONE /\
  request_agree cx r0 r1 /\
  request_agree_except (external_call_dead tx (res, am', rqs)) r1 r2 ==>
  request_agree cx r0 r2
Proof
  rw[request_agree_def, request_agree_except_def]
  >- gvs[extCallOracleTheory.call_request_component_equality]
  >- metis_tac[accounts_agree_dead_trans]
  >> metis_tac[transient_agree_dead_trans]
QED

Theorem external_call_result_rel_abort_transport[local]:
  external_call_result_rel tops ret tx src (Abort a ss) /\
  (a = Revert_abort ==> a' = Revert_abort) ==>
  external_call_result_rel tops ret tx src (Abort a' ss')
Proof
  PairCases_on `src` >> Cases_on `a` >> Cases_on `a'` >>
  simp[external_call_result_rel_def] >> rpt CASE_TAC >> simp[]
QED

(* The source relation holds of every run that matches one it holds of up
   to the source's dead bytes. *)
Theorem external_call_result_rel_dead_transport:
  external_call_result_rel tops ret tx src res /\
  dead_result_rel (external_call_dead tx src) res res' ==>
  external_call_result_rel tops ret tx src res'
Proof
  PairCases_on `src` >> Cases_on `res` >> Cases_on `res'` >>
  simp[dead_result_rel_def] >> rpt strip_tac >>
  TRY (drule_all external_call_result_rel_abort_transport >> simp[] >>
       NO_TAC) >>
  Cases_on `src0` >> gvs[external_call_result_rel_def, AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `accounts_agree cx` >>
  `v'.vs_returndata = v.vs_returndata` by
    (irule LIST_EQ >> gvs[external_call_dead_def]) >>
  rpt conj_tac
  >- gvs[]
  >- (irule accounts_agree_dead_trans >> simp[Abbr`cx`] >> metis_tac[])
  >- (irule transient_agree_dead_trans >> simp[Abbr`cx`] >> metis_tac[]) >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  irule request_agree_dead_trans >> simp[Abbr`cx`] >> metis_tac[]
QED

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
  rpt CASE_TAC >> rpt strip_tac >> gvs[]
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
  call_external (SOME (MAP SND (call_trace es))) [] am tx = (INL v, am', rqs) /\
  external_call_result_rel tops ret tx (INL v, am', rqs) (Halt ss) /\
  venom_frame_rel es r es' (Halt ss) ==>
  call_result_rel tops ret am tx es r es'
Proof
  simp[external_call_result_rel_def, venom_frame_rel_def,
       call_result_rel_def, LET_THM] >>
  rpt strip_tac >> qexistsl_tac [`ss.vs_returndata`, `ss.vs_logs`] >> gvs[]
QED

Theorem external_call_result_rel_frame_assertion:
  call_external (SOME (MAP SND (call_trace es))) [] am tx =
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

Theorem external_call_result_rel_frame_runtime:
  call_external (SOME (MAP SND (call_trace es))) [] am tx =
    (INR (Error (RuntimeError m)), am', rqs) /\
  venom_frame_rel es r es' (Abort a ss) ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >> drule venom_frame_rel_abort_failure >>
  simp[call_result_rel_def, LET_THM]
QED

Theorem external_call_result_rel_frame_error:
  call_external (SOME (MAP SND (call_trace es))) [] am tx =
    (INR (Error e), am', rqs) /\
  external_call_result_rel tops ret tx (INR (Error e), am', rqs) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >> Cases_on `res` >>
  gvs[external_call_result_rel_def, call_result_rel_def, LET_THM,
      AllCaseEqs()] >>
  drule venom_frame_rel_abort_failure >> simp[]
QED

(* Covers all source constructors; escaped control exceptions have no row.
 * A Halt paired with Error can only be the deliberately exempt decoder case.
 *)
Theorem external_call_result_rel_frame:
  external_call_result_rel tops ret tx
    (call_external (SOME (MAP SND (call_trace es))) [] am tx) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel tops ret am tx es r es'
Proof
  rpt strip_tac >>
  Cases_on `call_external (SOME (MAP SND (call_trace es))) [] am tx` >>
  rename1 `call_external _ _ am tx = (src, tail)` >> Cases_on `tail` >>
  rename1 `call_external _ _ am tx = (src, am', rqs)` >>
  Cases_on `src`
  >- (Cases_on `res` >>
      FIRST [drule_all external_call_result_rel_frame_success >> simp[],
             gvs[external_call_result_rel_def]]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  FIRST [drule_all external_call_result_rel_frame_error >> simp[],
         Cases_on `res` >>
         FIRST [drule_all external_call_result_rel_frame_assertion >> simp[],
                gvs[external_call_result_rel_def]]]
QED
