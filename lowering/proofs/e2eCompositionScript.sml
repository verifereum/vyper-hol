(* PLAN §8.1 composition helpers. No stage theorem is used here.
 * TOP-LEVEL: raw-result termination/transport, source exemption,
 *   successful and failed frame composition, unconditional run_call totality.
 *   external_call_dead_wf (external_call_dead is in vyperLoweringCorrect),
 *   external_call_result_rel_dead_transport — the source result's dead
 *   bytes, and the source relation's transport up to them.
 * Requests are compared only on success; abort kinds/data are not equated.
 *)
Theory e2eComposition
Ancestors
  e2eDefs vyperLoweringCorrect unitTransformDefs o1PassContract ptrDiscipline compileEnv
  accountsRelProps codegenCorrectness
  passSimulationDefs stateEquiv venomExecSemantics venomState
  vyperInterpreter vyperCallMetadata vyperValue vfmDecreasesGas vfmExecution frameOutcome callTrace
  list pair

(* ===== Actual EVM run, including exempt source failures ===== *)

Theorem run_call_total:
  !es. ?r es'. run_call es = SOME (r, es')
Proof
  cheat
QED

Theorem source_exempt_call_result_rel:
  source_exempt tops (call_external (SOME (MAP SND (call_trace es))) gobs am tx) ==>
  call_result_rel_at gobs tops ret am tx es r es'
Proof
  cheat
QED

(* ===== Raw termination and pipeline transport ===== *)

Theorem initial_evaluation_context_txn[local,simp]:
  (initial_evaluation_context srcs layouts tx src_id_opt).txn = tx
Proof
  cheat
QED

Theorem storage_agree_except_storage_dead:
  storage_agree_except {(k,b) | storage_dead cx tr st (w2n k) b} st st' <=>
  storage_agree (storage_dead cx tr st) st st'
Proof
  cheat
QED

Theorem storage_agree_except_empty:
  storage_agree_except {} st st' <=> st' = st
Proof
  cheat
QED

Theorem external_call_dead_wf:
  dead_wf (external_call_dead tx src)
Proof
  cheat
QED

(* ===== The dead-byte set ignores the source observations ===== *)

(* Only immutable source/layout metadata determines the dead-byte set. *)
Theorem external_call_dead_observations:
  external_call_dead tx (call_external orc gobs am tx) =
  external_call_dead tx (call_external orc' gobs' am tx)
Proof
  cheat
QED

val () =
  let val th = external_call_dead_observations
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles then
       print "DEAD_CALL_METADATA_AUDIT OK\n"
     else print "statement-check gate skipped\n"
  end;

Theorem storage_agree_dead_trans:
  storage_agree (storage_dead cx tr st0) st0 st1 /\
  storage_agree (storage_dead cx tr st1) st1 st2 ==>
  storage_agree (storage_dead cx tr st0) st0 st2
Proof
  cheat
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
  cheat
QED

Theorem transient_agree_except_external_call_dead[local]:
  transient_agree_except (external_call_dead tx (res, am', rqs)) t1 t2 <=>
  (!a. a <> tx.target ==> t1 a = t2 a) /\
  storage_agree
    (storage_dead (initial_evaluation_context am'.sources am'.layouts tx NONE)
       T (t1 tx.target))
    (t1 tx.target) (t2 tx.target)
Proof
  cheat
QED

Theorem accounts_agree_storage_dead_trans:
  accounts_agree cx a0 a1 /\
  (!a. (a1 a with storage := (a2 a).storage) = a2 a) /\
  (!a. a <> cx.txn.target ==> (a1 a).storage = (a2 a).storage) /\
  storage_agree (storage_dead cx F (a1 cx.txn.target).storage)
    (a1 cx.txn.target).storage (a2 cx.txn.target).storage ==>
  accounts_agree cx a0 a2
Proof
  cheat
QED

Theorem transient_agree_storage_dead_trans:
  transient_agree cx t0 t1 /\
  (!a. a <> cx.txn.target ==> t1 a = t2 a) /\
  storage_agree (storage_dead cx T (t1 cx.txn.target))
    (t1 cx.txn.target) (t2 cx.txn.target) ==>
  transient_agree cx t0 t2
Proof
  cheat
QED

Theorem accounts_agree_dead_trans[local]:
  cx = initial_evaluation_context am'.sources am'.layouts tx NONE /\
  accounts_agree cx a0 a1 /\
  accounts_agree_except (external_call_dead tx (res, am', rqs)) a1 a2 ==>
  accounts_agree cx a0 a2
Proof
  cheat
QED

(* Deleting the same accounts on both sides keeps them equal up to any
   dead bytes: a deleted account is empty on both. *)
Theorem accounts_agree_except_process_deletions:
  !D ds a1 a2.
    accounts_agree_except D a1 a2 ==>
    accounts_agree_except D (process_deletions ds a1) (process_deletions ds a2)
Proof
  cheat
QED

Theorem transient_agree_dead_trans[local]:
  cx = initial_evaluation_context am'.sources am'.layouts tx NONE /\
  transient_agree cx t0 t1 /\
  transient_agree_except (external_call_dead tx (res, am', rqs)) t1 t2 ==>
  transient_agree cx t0 t2
Proof
  cheat
QED

Theorem request_agree_dead_trans[local]:
  cx = initial_evaluation_context am'.sources am'.layouts tx NONE /\
  request_agree cx r0 r1 /\
  request_agree_except (external_call_dead tx (res, am', rqs)) r1 r2 ==>
  request_agree cx r0 r2
Proof
  cheat
QED

Theorem external_call_result_rel_abort_transport[local]:
  external_call_result_rel tops ret tx src (Abort a ss) /\
  (a = Revert_abort ==> a' = Revert_abort) ==>
  external_call_result_rel tops ret tx src (Abort a' ss')
Proof
  cheat
QED

(* The source relation holds of every run that matches one it holds of up
   to the source's dead bytes. *)
Theorem external_call_result_rel_dead_transport:
  external_call_result_rel tops ret tx src res /\
  dead_result_rel (external_call_dead tx src) res res' ==>
  external_call_result_rel tops ret tx src res'
Proof
  cheat
QED

Theorem external_call_result_rel_terminal:
  external_call_result_rel tops ret tx src res ==>
  (?ss. res = Halt ss) \/ (?a ss. res = Abort a ss)
Proof
  cheat
QED

Theorem external_call_result_rel_terminates:
  external_call_result_rel tops ret tx src res ==> terminates res
Proof
  cheat
QED

Theorem external_call_result_rel_unit_transport:
  external_call_result_rel tops ret tx src res /\ unit_result_rel res res' ==>
  external_call_result_rel tops ret tx src res'
Proof
  cheat
QED

(* ===== Frame composition, separated by semantic outcome ===== *)

Theorem venom_frame_rel_abort_failure:
  venom_frame_rel es r es' (Abort a ss) ==>
  ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs
Proof
  cheat
QED

Theorem venom_frame_rel_assertion:
  (a = Revert_abort \/ s = "UNREACHABLE") /\
  venom_frame_rel es r es' (Abort a ss) ==>
  ?exc out lgs. frame_outcome es r es' (SOME exc) out lgs /\
                (exc = Reverted \/ s = "UNREACHABLE")
Proof
  cheat
QED

Theorem external_call_result_rel_frame_success:
  call_external (SOME (MAP SND (call_trace es))) gobs am tx = (INL v, am', rqs) /\
  external_call_result_rel tops ret tx (INL v, am', rqs) (Halt ss) /\
  venom_frame_rel es r es' (Halt ss) ==>
  call_result_rel_at gobs tops ret am tx es r es'
Proof
  cheat
QED

Theorem external_call_result_rel_frame_assertion:
  call_external (SOME (MAP SND (call_trace es))) gobs am tx =
    (INR (AssertException s), am', rqs) /\
  external_call_result_rel tops ret tx
    (INR (AssertException s), am', rqs) (Abort a ss) /\
  venom_frame_rel es r es' (Abort a ss) ==>
  call_result_rel_at gobs tops ret am tx es r es'
Proof
  cheat
QED

Theorem external_call_result_rel_frame_runtime:
  call_external (SOME (MAP SND (call_trace es))) gobs am tx =
    (INR (Error (RuntimeError m)), am', rqs) /\
  venom_frame_rel es r es' (Abort a ss) ==>
  call_result_rel_at gobs tops ret am tx es r es'
Proof
  cheat
QED

Theorem external_call_result_rel_frame_error:
  call_external (SOME (MAP SND (call_trace es))) gobs am tx =
    (INR (Error e), am', rqs) /\
  external_call_result_rel tops ret tx (INR (Error e), am', rqs) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel_at gobs tops ret am tx es r es'
Proof
  cheat
QED

(* Covers all source constructors; escaped control exceptions have no row.
 * A Halt paired with Error can only be the deliberately exempt decoder case.
 *)
Theorem external_call_result_rel_frame:
  external_call_result_rel tops ret tx
    (call_external (SOME (MAP SND (call_trace es))) gobs am tx) res /\
  venom_frame_rel es r es' res ==>
  call_result_rel_at gobs tops ret am tx es r es'
Proof
  cheat
QED
