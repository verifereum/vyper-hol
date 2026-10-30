(* Shared, gas-free external-call oracle. No evaluator is activated here.
 * TOP-LEVEL: call_request, call_outcome; precompile_result,
 * computed_precompile, failed_outcome, take_outcome, record_request,
 * adopt_outcome. CV translations export representations for later stages.
 *)
Theory extCallOracle
Ancestors
  arithmetic list option pair words byte
  vfmTypes vfmState vfmContext vfmExecution
  (* Verifereum's CV representation for function-valued transient storage. *)
  vfmCompute[ignore_grammar] sha2
Libs
  cv_transLib

(* ===== Requests and outcomes ===== *)

(* Deliberately no forwarded-gas field: the source has no such observation. *)
Datatype:
  call_request = <| cr_target : address;
                    cr_value : num;
                    cr_data : byte list;
                    cr_static : bool;
                    cr_accounts : evm_accounts;
                    cr_tStorage : transient_storage |>
End

Datatype:
  call_outcome = <| co_success : bool;
                    co_returnData : byte list;
                    co_accounts : evm_accounts;
                    co_tStorage : transient_storage;
                    co_logs : event list;
                    co_toDelete : address list |>
End

(* ===== Computed precompiles ===== *)

(* NONE: ordinary address; SOME NONE: invalid EC point (failure);
 * SOME (SOME bs): success, including invalid ecrecover's empty result.
 * These are precisely the bodies of Verifereum's precompiles 1/2/6/7,
 * with the gas charge removed. Input beyond the used slices is ignored.
 *)
Definition precompile_result_def:
  precompile_result (target:address) (input:byte list) =
    if target = 1w then
      let hash = word_of_bytes T (0w:bytes32) (take_pad_0 32 input);
          v = num_of_be_bytes (take_pad_0 32 (DROP 32 input));
          r = num_of_be_bytes (take_pad_0 32 (DROP 64 input));
          s = num_of_be_bytes (take_pad_0 32 (DROP 96 input))
      in SOME (SOME (case vfmExecution$ecrecover hash v r s of
                       NONE => []
                     | SOME addr => PAD_LEFT 0w 32 (word_to_bytes addr T)))
    else if target = 2w then
      SOME (SOME (word_to_bytes (SHA_256_bytes input) T))
    else if target = 6w then
      let ax = num_of_be_bytes (take_pad_0 32 input);
          ay = num_of_be_bytes (take_pad_0 32 (DROP 32 input));
          bx = num_of_be_bytes (take_pad_0 32 (DROP 64 input));
          by = num_of_be_bytes (take_pad_0 32 (DROP 96 input))
      in SOME (OPTION_MAP (\(x,y).
           PAD_LEFT 0w 32 (num_to_be_bytes x) ++
           PAD_LEFT 0w 32 (num_to_be_bytes y))
         (vfmExecution$ecadd (ax,ay) (bx,by)))
    else if target = 7w then
      let px = num_of_be_bytes (take_pad_0 32 input);
          py = num_of_be_bytes (take_pad_0 32 (DROP 32 input));
          s = num_of_be_bytes (take_pad_0 32 (DROP 64 input))
      in SOME (OPTION_MAP (\(x,y).
           PAD_LEFT 0w 32 (num_to_be_bytes x) ++
           PAD_LEFT 0w 32 (num_to_be_bytes y))
         (vfmExecution$ecmul (px,py) s))
    else NONE
End

val () = cv_auto_trans
  (precompile_result_def |> REWRITE_RULE
    [GSYM word_of_bytes_be_def, GSYM word_to_bytes_be_def]);

Definition computed_precompile_def:
  computed_precompile rq <=>
    rq.cr_value = 0 /\ IS_SOME (precompile_result rq.cr_target rq.cr_data)
End

val () = cv_auto_trans computed_precompile_def;

Definition failed_outcome_def:
  failed_outcome rq =
    <| co_success := F; co_returnData := []; co_accounts := rq.cr_accounts;
       co_tStorage := rq.cr_tStorage; co_logs := []; co_toDelete := [] |>
End

val () = cv_auto_trans failed_outcome_def;

Definition take_outcome_def:
  take_outcome rq os =
    if computed_precompile rq then
      (case precompile_result rq.cr_target rq.cr_data of
         SOME (SOME bs) =>
           (failed_outcome rq with <| co_success := T; co_returnData := bs |>, os)
       | _ => (failed_outcome rq, os))
    else case os of
           [] => (failed_outcome rq, [])
         | outcome :: rest => (outcome, rest)
End

val () = cv_auto_trans take_outcome_def;

Definition record_request_def:
  record_request rq rqs = if computed_precompile rq then rqs else rqs ++ [rq]
End

val () = cv_auto_trans record_request_def;

Definition adopt_outcome_def:
  adopt_outcome rq outcome (accounts, tStorage, logs, pending) =
    if outcome.co_success /\ ~rq.cr_static
    then (outcome.co_accounts, outcome.co_tStorage, logs ++ outcome.co_logs,
          outcome.co_toDelete ++ pending)
    else (accounts, tStorage, logs, pending)
End

val () = cv_auto_trans adopt_outcome_def;

(* Export the remaining outcome selector too, for source/Venom consumers. *)
val () = cv_trans (DB.fetch "extCallOracle"
  "recordtype_call_outcome_seldef_co_returnData_def");

(* ===== Permanent consumer contracts ===== *)

(* Address numerals use 160-bit words, not the default 32-bit words. *)
Theorem precompile_addresses_distinct[simp]:
  (1w:address) <> 2w /\ (1w:address) <> 6w /\ (1w:address) <> 7w /\
  (2w:address) <> 1w /\ (2w:address) <> 6w /\ (2w:address) <> 7w /\
  (6w:address) <> 1w /\ (6w:address) <> 2w /\ (6w:address) <> 7w /\
  (7w:address) <> 1w /\ (7w:address) <> 2w /\ (7w:address) <> 6w
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem precompile_result_domain:
  IS_SOME (precompile_result target input) <=>
    target = 1w \/ target = 2w \/ target = 6w \/ target = 7w
Proof
  rw[precompile_result_def] >> simp[]
QED

Theorem computed_precompile_addresses:
  computed_precompile rq <=>
    rq.cr_value = 0 /\
    (rq.cr_target = 1w \/ rq.cr_target = 2w \/
     rq.cr_target = 6w \/ rq.cr_target = 7w)
Proof
  simp[computed_precompile_def, precompile_result_domain]
QED

Theorem precompile_result_ordinary:
  target <> 1w /\ target <> 2w /\ target <> 6w /\ target <> 7w ==>
  precompile_result target input = NONE
Proof
  simp[precompile_result_def]
QED

Theorem precompile_result_sha256[simp]:
  precompile_result 2w input = SOME (SOME (word_to_bytes (SHA_256_bytes input) T))
Proof
  simp[precompile_result_def]
QED

Theorem precompile_result_ecrecover_invalid:
  vfmExecution$ecrecover
    (word_of_bytes T (0w:bytes32) (take_pad_0 32 input))
    (num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
    (num_of_be_bytes (take_pad_0 32 (DROP 64 input)))
    (num_of_be_bytes (take_pad_0 32 (DROP 96 input))) = NONE ==>
  precompile_result 1w input = SOME (SOME [])
Proof
  simp[precompile_result_def]
QED

Theorem precompile_result_ecrecover_valid:
  vfmExecution$ecrecover
    (word_of_bytes T (0w:bytes32) (take_pad_0 32 input))
    (num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
    (num_of_be_bytes (take_pad_0 32 (DROP 64 input)))
    (num_of_be_bytes (take_pad_0 32 (DROP 96 input))) = SOME addr ==>
  precompile_result 1w input = SOME (SOME (PAD_LEFT 0w 32 (word_to_bytes addr T)))
Proof
  simp[precompile_result_def]
QED

Theorem precompile_result_ecadd:
  precompile_result 6w input =
    SOME (OPTION_MAP (\(x,y).
      PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
      (vfmExecution$ecadd
        (num_of_be_bytes (take_pad_0 32 input),
         num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
        (num_of_be_bytes (take_pad_0 32 (DROP 64 input)),
         num_of_be_bytes (take_pad_0 32 (DROP 96 input)))))
Proof
  simp[precompile_result_def]
QED

Theorem precompile_result_ecmul:
  precompile_result 7w input =
    SOME (OPTION_MAP (\(x,y).
      PAD_LEFT 0w 32 (num_to_be_bytes x) ++ PAD_LEFT 0w 32 (num_to_be_bytes y))
      (vfmExecution$ecmul
        (num_of_be_bytes (take_pad_0 32 input),
         num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
        (num_of_be_bytes (take_pad_0 32 (DROP 64 input)))))
Proof
  simp[precompile_result_def]
QED

(* Regression probes evaluate through the exported CV translations. Empty
 * ecrecover input has v = 0 (invalid signature but successful call). Empty
 * EC input is the point at infinity. (0,1) is not a valid BN254 point.
 *)
Theorem precompile_result_empty_ecrecover:
  precompile_result 1w [] = SOME (SOME [])
Proof
  CONV_TAC cv_eval
QED

Theorem precompile_result_empty_sha256:
  precompile_result 2w [] = SOME (SOME (word_to_bytes
    (0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855w:bytes32) T))
Proof
  CONV_TAC (REWRITE_CONV [GSYM word_to_bytes_be_def] THENC cv_eval)
QED

Theorem precompile_result_empty_ec:
  precompile_result 6w [] = SOME (SOME (REPLICATE 64 0w)) /\
  precompile_result 7w [] = SOME (SOME (REPLICATE 64 0w))
Proof
  CONV_TAC cv_eval
QED

Theorem precompile_result_invalid_ec:
  precompile_result 6w (REPLICATE 63 0w ++ [1w]) = SOME NONE /\
  precompile_result 7w (REPLICATE 63 0w ++ [1w]) = SOME NONE
Proof
  CONV_TAC cv_eval
QED

Theorem failed_outcome_fields[simp]:
  ~(failed_outcome rq).co_success /\
  (failed_outcome rq).co_returnData = [] /\
  (failed_outcome rq).co_accounts = rq.cr_accounts /\
  (failed_outcome rq).co_tStorage = rq.cr_tStorage /\
  (failed_outcome rq).co_logs = [] /\
  (failed_outcome rq).co_toDelete = []
Proof
  simp[failed_outcome_def]
QED

Theorem take_outcome_ordinary:
  ~computed_precompile rq ==>
  take_outcome rq (outcome::rest) = (outcome, rest) /\
  record_request rq rqs = rqs ++ [rq]
Proof
  simp[take_outcome_def, record_request_def]
QED

Theorem take_outcome_exhausted:
  ~computed_precompile rq ==> take_outcome rq [] = (failed_outcome rq, [])
Proof
  simp[take_outcome_def]
QED

Theorem take_outcome_nonzero_value:
  rq.cr_value <> 0 ==>
  take_outcome rq (outcome::rest) = (outcome, rest) /\
  take_outcome rq [] = (failed_outcome rq, []) /\
  record_request rq rqs = rqs ++ [rq]
Proof
  simp[computed_precompile_def, take_outcome_def, record_request_def]
QED

Theorem take_outcome_computed_valid:
  rq.cr_value = 0 /\ precompile_result rq.cr_target rq.cr_data = SOME (SOME bs) ==>
  take_outcome rq os =
    (failed_outcome rq with <| co_success := T; co_returnData := bs |>, os) /\
  record_request rq rqs = rqs
Proof
  strip_tac >>
  simp[computed_precompile_def, take_outcome_def, record_request_def]
QED

(* In particular invalid ecrecover is a successful computed call, unlike
 * invalid EC points. Both leave the oracle and request trace untouched. *)
Theorem take_outcome_empty_ecrecover:
  rq.cr_value = 0 /\ rq.cr_target = 1w /\ rq.cr_data = [] ==>
  take_outcome rq os =
    (failed_outcome rq with <| co_success := T; co_returnData := [] |>, os) /\
  record_request rq rqs = rqs
Proof
  strip_tac >> irule take_outcome_computed_valid >>
  simp[precompile_result_empty_ecrecover]
QED

Theorem take_outcome_computed_invalid:
  rq.cr_value = 0 /\ precompile_result rq.cr_target rq.cr_data = SOME NONE ==>
  take_outcome rq os = (failed_outcome rq, os) /\ record_request rq rqs = rqs
Proof
  strip_tac >>
  simp[computed_precompile_def, take_outcome_def, record_request_def]
QED

Theorem take_outcome_invalid_ec:
  rq.cr_value = 0 /\ (rq.cr_target = 6w \/ rq.cr_target = 7w) /\
  rq.cr_data = REPLICATE 63 0w ++ [1w] ==>
  take_outcome rq os = (failed_outcome rq, os) /\ record_request rq rqs = rqs
Proof
  strip_tac >> irule take_outcome_computed_invalid >>
  simp[precompile_result_invalid_ec]
QED

Theorem computed_precompile_no_observation:
  computed_precompile rq ==>
  SND (take_outcome rq os) = os /\ record_request rq rqs = rqs
Proof
  rw[take_outcome_def, record_request_def] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  rename1 `SOME result` >> Cases_on `result` >> simp[]
QED

Theorem adopt_outcome_failed[simp]:
  ~outcome.co_success ==>
  adopt_outcome rq outcome (accounts, tStorage, logs, pending) =
    (accounts, tStorage, logs, pending)
Proof
  simp[adopt_outcome_def]
QED

Theorem adopt_outcome_static[simp]:
  rq.cr_static ==>
  adopt_outcome rq outcome (accounts, tStorage, logs, pending) =
    (accounts, tStorage, logs, pending)
Proof
  simp[adopt_outcome_def]
QED

Theorem adopt_outcome_success:
  outcome.co_success /\ ~rq.cr_static ==>
  adopt_outcome rq outcome (accounts, tStorage, logs, pending) =
    (outcome.co_accounts, outcome.co_tStorage, logs ++ outcome.co_logs,
     outcome.co_toDelete ++ pending)
Proof
  simp[adopt_outcome_def]
QED

(* Computed calls carry the request's snapshots and emit no logs. *)
Theorem computed_precompile_state:
  computed_precompile rq ==>
  (FST (take_outcome rq os)).co_accounts = rq.cr_accounts /\
  (FST (take_outcome rq os)).co_tStorage = rq.cr_tStorage /\
  (FST (take_outcome rq os)).co_logs = [] /\
  (FST (take_outcome rq os)).co_toDelete = []
Proof
  rw[take_outcome_def] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  rename1 `SOME result` >> Cases_on `result` >> simp[]
QED

Theorem adopt_outcome_computed:
  computed_precompile rq ==>
  adopt_outcome rq (FST (take_outcome rq os))
    (rq.cr_accounts, rq.cr_tStorage, logs, pending) =
      (rq.cr_accounts, rq.cr_tStorage, logs, pending)
Proof
  strip_tac >> drule computed_precompile_state >> strip_tac >>
  simp[adopt_outcome_def]
QED
