(* Concrete target bytecode runs through Verifereum, not outcome injection.
   The direct eval_raw_call path and the CPS expression path both execute in CV. *)
Theory vyperDelegateRawCallTest
Ancestors
  vyperSmallStep[ignore_grammar] vyperInterpreter
  vfmExecution[ignore_grammar] vfmState[ignore_grammar]
  vyperState vyperContext vyperAST vyperValue vyperTypeSystem
  list option pair finite_map words vfmTypes
Libs cv_transLib wordsLib

Definition delegate_context_def:
  delegate_context = empty_evaluation_context with txn :=
    empty_call_txn with <|sender := 43w; target := 41w; value := 19;
      calldata := [1w;2w;3w;4w;99w]|>
End
val () = cv_auto_trans delegate_context_def;

Definition delegate_flags_def:
  delegate_flags outsize revert =
    <|rcf_max_outsize := outsize; rcf_is_delegate := T;
      rcf_is_static := F; rcf_revert_on_failure := revert;
      rcf_kws := [EKValue]|>
End
val () = cv_auto_trans delegate_flags_def;

(* CALLER/CALLVALUE/ADDRESS into proxy slots 1/2/3; read preexisting
   transient slot 0 into persistent slot 4; update proxy slot 0 and transient
   slot 0. Return caller/value/address/new transient value as four ABI words;
   LOG0 emits the first three words. *)
Definition delegate_effects_def:
  delegate_effects : word8 list =
    [0x33w;0x60w;1w;0x55w; 0x34w;0x60w;2w;0x55w;
     0x30w;0x60w;3w;0x55w; 0x60w;0w;0x5cw;0x60w;4w;0x55w;
     0x60w;42w;0x60w;0w;0x55w; 0x60w;8w;0x60w;0w;0x5dw;
     0x33w;0x60w;0w;0x52w; 0x34w;0x60w;32w;0x52w;
     0x30w;0x60w;64w;0x52w; 0x60w;0w;0x5cw;0x60w;96w;0x52w;
     0x60w;96w;0x60w;0w;0xa0w]
End
val () = cv_auto_trans delegate_effects_def;

Definition delegate_success_code_def:
  delegate_success_code = delegate_effects ++ [0x60w;128w;0x60w;0w;0xf3w]
End
val () = cv_auto_trans delegate_success_code_def;

Definition delegate_revert_code_def:
  delegate_revert_code = delegate_effects ++
    [0x60w;0xaaw;0x60w;0w;0x53w; 0x60w;0xbbw;0x60w;1w;0x53w;
     0x60w;0xccw;0x60w;2w;0x53w; 0x60w;3w;0x60w;0w;0xfdw]
End
val () = cv_auto_trans delegate_revert_code_def;

Definition delegate_state_def:
  delegate_state code = empty_state with
    <|accounts := update_account 41w
        (empty_account_state with <|balance := 3; nonce := 2; code := [0w];
          storage := update_storage 0w 2w empty_storage|>)
        (update_account 42w
          (empty_account_state with <|balance := 5; nonce := 4; code := code;
            storage := update_storage 0w 99w empty_storage|>)
          (update_account 43w (empty_account_state with <|balance := 7; nonce := 6|>)
            empty_accounts));
      tStorage := vfmExecution$update_transient_storage 41w
        (update_storage 0w 4w empty_storage)
        (vfmExecution$update_transient_storage 42w
          (update_storage 0w 9w empty_storage) empty_transient_storage);
      logs := [<|logger := 43w; topics := []; data := [99w]|>];
      scopes := [FEMPTY]; immutables := [(41w,[])]|>
End
val () = cv_auto_trans delegate_state_def;

Definition delegate_expression_def:
  delegate_expression calldata_form flags amount =
    Call (raw_call_return_type flags)
      (if calldata_form then RawCallCalldataTarget flags else RawCallTarget flags)
      ([Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [42w]))] ++
       (if calldata_form then [] else
         [Literal (BaseT (BytesT (Dynamic 5))) (BytesL [1w;2w;3w;4w;99w])]) ++
       [Literal (BaseT (UintT 256)) (IntL (&amount))]) NONE
End
val () = cv_auto_trans delegate_expression_def;

Definition delegate_words_def:
  delegate_words = FLAT (MAP (\n. REPLICATE 31 (0w:word8) ++ [n]) [43w;19w;41w;8w])
End
val () = cv_auto_trans delegate_words_def;

Definition delegate_logs_def:
  delegate_logs = [<|logger := 43w; topics := []; data := [99w]|>;
    <|logger := 41w; topics := []; data := TAKE 96 delegate_words|>]
End
val () = cv_auto_trans delegate_logs_def;

(* Snapshot every participating account's balance, nonce and code; persistent
   slots touched by the bytecode, both transient namespaces, logs and interpreter
   locals. No function-valued account equality or fabricated oracle result. *)
Definition delegate_observe_def:
  delegate_observe cps calldata_form code flags amount expected slots transient logs =
    let st = delegate_state code in
    let r = if cps then vyperSmallStep$fromtvk (vyperSmallStep$cont
        (vyperSmallStep$eval_expr_cps delegate_context
          (delegate_expression calldata_form flags amount) st vyperSmallStep$DoneK))
      else eval_raw_call delegate_context flags 42w delegate_context.txn.calldata amount
        default_evm_gas_limit st in
    FST r = expected /\
    let final = SND r in
    MAP (\a. let acc = lookup_account a final.accounts in
      (acc.balance,acc.nonce,acc.code)) [41w;42w;43w] =
      [(3,2,[0w]);(5,4,code);(7,6,[])] /\
    MAP (\slot. lookup_storage slot (lookup_account 41w final.accounts).storage)
      [0w;1w;2w;3w;4w] = slots /\
    MAP (\slot. lookup_storage slot (lookup_account 42w final.accounts).storage)
      [0w;1w;2w;3w;4w] = [99w;0w;0w;0w;0w] /\
    lookup_storage 0w (vfmExecution$lookup_transient_storage 41w final.tStorage) = transient /\
    lookup_storage 0w (vfmExecution$lookup_transient_storage 42w final.tStorage) = 9w /\
    final.logs = logs /\ final.scopes = [FEMPTY] /\ final.immutables = [(41w,[])] /\
    final.requests = [] /\ IS_NONE final.outcomes
End
val () = cv_auto_trans delegate_observe_def;

Theorem delegate_inherits_context_without_transfer_and_isolates_storage:
  EVERY (\mode.
    delegate_observe (FST mode) (SND mode) delegate_success_code (delegate_flags 128 T) 0
      (INL (Value (BytesV delegate_words))) [42w;43w;19w;41w;4w] 8w delegate_logs)
    [(F,F);(T,F);(T,T)]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

Theorem delegate_revert_bytes_truncate_and_rollback:
  EVERY (\mode.
    delegate_observe (FST mode) (SND mode) delegate_revert_code (delegate_flags 2 F) 0
      (INL (Value (ArrayV (TupleV [BoolV F; BytesV [0xaaw;0xbbw]]))))
      [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>])
    [(F,F);(T,F);(T,T)]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

Theorem delegate_revert_on_failure_restores_state:
  EVERY (\cps. delegate_observe cps T delegate_revert_code (delegate_flags 3 T) 0
    (INR (Error (RevertData [0xaaw;0xbbw;0xccw])))
    [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>]) [F;T]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

(* INVALID is an EVM exceptional halt, after visible writes and a log. It
   returns false with no bytes and rolls back, unlike a model/domain abort. *)
Theorem delegate_exceptional_halt_returns_failure_and_rolls_back:
  EVERY (\cps. delegate_observe cps F (delegate_effects ++ [0xfew]) (delegate_flags 4 F) 0
    (INL (Value (ArrayV (TupleV [BoolV F; BytesV []]))))
    [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>]) [F;T]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

(* A regular CALL (not delegate) fails the same way: an exceptional halt
   returns false with no bytes, a REVERT with revert_on_failure re-raises the
   callee's bytes, a value the caller cannot pay fails before entry, and an
   SSTORE under STATICCALL halts.
   Every case rolls the callee back. *)
Definition regular_flags_def:
  regular_flags outsize revert = delegate_flags outsize revert with rcf_is_delegate := F
End
val () = cv_auto_trans regular_flags_def;

Theorem regular_call_failures_return_false_and_roll_back:
  EVERY (\cps.
    delegate_observe cps F (delegate_effects ++ [0xfew]) (regular_flags 4 F) 0
      (INL (Value (ArrayV (TupleV [BoolV F; BytesV []]))))
      [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>] /\
    delegate_observe cps T delegate_revert_code (regular_flags 3 T) 0
      (INR (Error (RevertData [0xaaw;0xbbw;0xccw])))
      [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>] /\
    delegate_observe cps T delegate_success_code (regular_flags 0 F) 100
      (INL (Value (BoolV F)))
      [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>] /\
    delegate_observe cps F delegate_success_code
      ((regular_flags 4 F) with rcf_is_static := T) 0
      (INL (Value (ArrayV (TupleV [BoolV F; BytesV []]))))
      [2w;0w;0w;0w;0w] 4w [<|logger := 43w; topics := []; data := [99w]|>]) [F;T]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

Theorem delegate_no_output_success_and_failure_results:
  EVERY (\cps.
    delegate_observe cps T delegate_success_code (delegate_flags 0 T) 0
      (INL (Value NoneV)) [42w;43w;19w;41w;4w] 8w delegate_logs /\
    delegate_observe cps F delegate_success_code (delegate_flags 0 F) 0
      (INL (Value (BoolV T))) [42w;43w;19w;41w;4w] 8w delegate_logs /\
    delegate_observe cps T delegate_revert_code (delegate_flags 0 F) 0
      (INL (Value (BoolV F))) [2w;0w;0w;0w;0w] 4w
      [<|logger := 43w; topics := []; data := [99w]|>]) [F;T]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

Theorem raw_call_invalid_flags_value_before_execution:
  EVERY (\cps. EVERY (\flags_amount.
    delegate_observe cps T delegate_success_code (FST flags_amount) (SND flags_amount)
      (INR (Error (TypeError "raw_call flags/value"))) [2w;0w;0w;0w;0w] 4w
      [<|logger := 43w; topics := []; data := [99w]|>])
    [(delegate_flags 0 F,1);
     ((delegate_flags 0 F) with rcf_is_static := T,0);
     ((delegate_flags 0 F) with <|rcf_is_delegate := F; rcf_is_static := T|>,1)]) [F;T]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED

(* An authorized account supplies an EIP-7702 designation, not executable code.
   Resolve its implementation while retaining the proxy's message and storage. *)
Definition delegate_designation_state_def:
  delegate_designation_state =
    let st = delegate_state (vfmContext$make_delegation 44w) in
    st with accounts := update_account 44w
      (empty_account_state with <|balance := 11; nonce := 8;
        code := delegate_success_code;
        storage := update_storage 0w 66w empty_storage|>) st.accounts
End
val () = cv_auto_trans delegate_designation_state_def;

Theorem delegate_designation_executes_implementation_in_proxy_context:
  EVERY (\mode.
    let r = if FST mode then vyperSmallStep$fromtvk (vyperSmallStep$cont
        (vyperSmallStep$eval_expr_cps delegate_context
          (delegate_expression (SND mode) (delegate_flags 128 T) 0)
          delegate_designation_state vyperSmallStep$DoneK))
      else eval_raw_call delegate_context (delegate_flags 128 T) 42w
        delegate_context.txn.calldata 0 default_evm_gas_limit
        delegate_designation_state in
    FST r = INL (Value (BytesV delegate_words)) /\
    let final = SND r in
    MAP (\slot. lookup_storage slot (lookup_account 41w final.accounts).storage)
      [0w;1w;2w;3w;4w] = [42w;43w;19w;41w;4w] /\
    MAP (\a. let acc = lookup_account a final.accounts in
      (acc.balance,acc.nonce,acc.code,lookup_storage 0w acc.storage)) [42w;43w;44w] =
      [(5,4,vfmContext$make_delegation 44w,99w);
       (7,6,[],0w);(11,8,delegate_success_code,66w)] /\
    (lookup_account 41w final.accounts).balance = 3 /\
    lookup_storage 0w (vfmExecution$lookup_transient_storage 41w final.tStorage) = 8w /\
    lookup_storage 0w (vfmExecution$lookup_transient_storage 42w final.tStorage) = 9w /\
    final.logs = delegate_logs)
    [(F,F);(T,F);(T,T)]
Proof
  simp[EVERY_DEF] >> CONV_TAC cv_eval
QED
