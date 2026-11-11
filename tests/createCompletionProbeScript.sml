Theory createCompletionProbe
Ancestors
  venomExecSemantics venomState vfmExecution vfmState vfmCompute vfmDecreasesGas
Libs
  wordsLib cv_transLib

(* The CREATE helper starts initcode directly, not by executing step_create. *)
Definition create_probe_state_def:
  create_probe_state = (init_venom_state "entry") with vs_call_ctx :=
    (init_venom_state "entry").vs_call_ctx with
      <|cc_address := 1w; cc_gas := 100000|>
End

(* Expand only the entry construction, erasing unused Venom finite-map fields
   before translating the executable probe. *)
Definition create_probe_entry_def:
  create_probe_entry address value code =
    make_venom_create_state create_probe_state address 100000 value code
End
Theorem create_probe_entry_expanded:
  create_probe_entry address value code =
    let ctxt = initial_context address code F (Code address)
         (make_sub_tx 1w address value 100000 []);
        rb = make_rollback (transfer_value 1w address value empty_accounts)
               empty_transient_storage 1w address
    in <|contexts := [(ctxt,rb)];
         txParams := <|origin := 0w; gasPrice := 0; baseFeePerGas := 0;
           baseFeePerBlobGas := 0; blockNumber := 0; blockTimeStamp := 0;
           blockCoinBase := 0w; blockGasLimit := 0; prevRandao := 0w;
           prevHashes := []; blobHashes := []; chainId := 0; authRefund := 0|>;
         rollback := rb; originalAccounts := rb.accounts;
         msdomain := Collect empty_domain|>
Proof
  simp[create_probe_entry_def, make_venom_create_state_def,
       create_probe_state_def, init_venom_state_def, venom_to_tx_params_def,
       empty_tx_context_def, empty_block_context_def]
QED
val () = cv_auto_trans create_probe_entry_expanded;

Definition create_run_observation_def:
  create_run_observation rr =
    case rr of
    | NONE => NONE
    | SOME (r,fs) =>
        (case fs.contexts of
         | [(ctxt,rb)] => SOME (r,ctxt.returnData)
         | _ => NONE)
End
Definition create_probe_observe_def:
  create_probe_observe salt value code =
    let address = case salt of
      | NONE => address_for_create 1w 0
      | SOME s => address_for_create2 1w s code
    in create_run_observation (run (create_probe_entry address value code))
End
val () = cv_auto_trans create_probe_observe_def;

Theorem create_probe_stop:
  create_probe_observe NONE 0 [0w] = SOME (INR NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem create_probe_constructor_revert:
  create_probe_observe NONE 0 [96w; 42w; 96w; 0w; 83w; 96w; 1w; 96w; 0w; 253w] =
    SOME (INR (SOME Reverted), [42w])
Proof
  CONV_TAC cv_eval
QED

Theorem create_probe_constructor_invalid:
  create_probe_observe NONE 0 [254w] = SOME (INR (SOME InvalidOpcode), [])
Proof
  CONV_TAC cv_eval
QED

(* Observation-to-extraction is independent of termination. *)
Theorem create_observation_extract:
  create_run_observation rr = SOME (r,data) ==>
  ?s'. extract_venom_result s address 0 0 rr =
        SOME (if r = INR NONE then address else 0w, s') /\
       s'.vs_returndata = data
Proof
  Cases_on `rr` >> simp[create_run_observation_def] >>
  PairCases_on `x` >> simp[] >> strip_tac >>
  Cases_on `x1.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >> PairCases_on `h` >> gvs[] >>
  Cases_on `r` >> gvs[extract_venom_result_def] >>
  Cases_on `y` >> simp[]
QED

Theorem create2_probe_stop:
  create_probe_observe (SOME 7w) 0 [0w] = SOME (INR NONE, [])
Proof
  CONV_TAC cv_eval
QED

Theorem create2_probe_constructor_revert:
  create_probe_observe (SOME 7w) 0
    [96w; 42w; 96w; 0w; 83w; 96w; 1w; 96w; 0w; 253w] =
    SOME (INR (SOME Reverted), [42w])
Proof
  CONV_TAC cv_eval
QED

(* A pre-entry check is MISSING from this concrete Venom helper: this
   STOP constructor succeeds although the caller's account is unfunded.
   This is evidence for an execution-interface repair, not an assumption
   ruling out failed creation in a future correctness theorem. *)
Theorem create_probe_unfunded_caller:
  (lookup_account 1w create_probe_state.vs_accounts).balance = 0 /\
  create_probe_observe NONE 1 [0w] = SOME (INR NONE, []) /\
  create_probe_observe (SOME 7w) 1 [0w] = SOME (INR NONE, [])
Proof
  conj_tac >- EVAL_TAC >> CONV_TAC cv_eval
QED

Theorem create_probe_run_terminates:
  ?e fs. run (make_venom_create_state s address gas value code) =
         SOME (INR e,fs)
Proof
  simp[run_eq_tr] >>
  Cases_on `run_tr (step (make_venom_create_state s address gas value code))` >>
  simp[]
QED

(* Neither termination nor nonemptiness alone licenses extraction. *)
Theorem create_probe_nonsingleton_extract:
  extract_venom_result s address 0 0
    (SOME (INR NONE, es with contexts := [a;b])) = NONE
Proof
  simp[extract_venom_result_def]
QED

Theorem create_extraction_requires_singleton:
  (?out s'. extract_venom_result s address 0 0 rr = SOME (out,s')) <=>
  ?r fs ctxt rb. rr = SOME (r,fs) /\ fs.contexts = [(ctxt,rb)]
Proof
  Cases_on `rr` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `t` >> simp[] >> PairCases_on `h` >> simp[] >>
  Cases_on `x0` >> simp[] >> Cases_on `y` >> simp[]
QED

(* Remaining production prerequisites, NOT asserted here:
   - a run_tr induction preserving a nonempty well-formed context stack;
   - every terminating step on such an entry is singleton (nonempty alone
     from vfmExecutionProp.run_preserves_nonempty_contexts is insufficient);
   - correspondence of Code-return deployment/rollback with source CREATE;
   - repair/abstract the pre-entry balance, nonce, collision, static and
     initcode-size behavior before claiming full CREATE opcode correctness.
   The unfunded probe above specifically prevents hiding that gap behind
   an assumption that the compiled instruction already succeeded. *)
val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createCompletionProbe");
