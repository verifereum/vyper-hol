Theory vyperCreateSelfdestruct
Ancestors
  vyperCreate vyperInterpreter vyperSmallStep[ignore_grammar]
  vyperContext vfmExecution vfmState finite_set finite_map
Libs
  wordsLib cv_transLib

(* Constructor SELFDESTRUCT must see an empty original account even though the
   live account has already received its nonce-one creation prelude. *)
Definition constructor_selfdestruct_state_def:
  constructor_selfdestruct_state =
    let accounts = create_prelude_accounts (1w:address) (2w:address) 0
      empty_accounts in
    let start = make_create_state (1w:address) (2w:address) [] 0
      accounts empty_transient_storage [] (vyper_to_tx_params empty_call_txn) in
    start with contexts :=
      [(FST (HD start.contexts) with stack := [3w], SND (HD start.contexts))]
End

Theorem constructor_original_empty:
  account_empty (lookup_account (2w:address)
    (SND (HD constructor_selfdestruct_state.contexts)).accounts) /\
  (lookup_account (2w:address) constructor_selfdestruct_state.rollback.accounts).nonce = 1
Proof
  EVAL_TAC >> simp[]
QED

Theorem constructor_selfdestruct_deferred:
  case step_self_destruct constructor_selfdestruct_state of
  | (INR NONE, finished) =>
      MEM (2w:address) finished.rollback.toDelete /\
      (lookup_account (2w:address) finished.rollback.accounts).nonce = 1 /\
      account_empty (lookup_account (2w:address)
        (process_deletions finished.rollback.toDelete finished.rollback.accounts))
  | _ => F
Proof
  EVAL_TAC >> simp[MEM_fset_REP, fIN_fset_ABS] >>
  EVAL_TAC >> simp[MEM_fset_REP, fIN_fset_ABS]
QED

Theorem constructor_transaction_commit:
  case step_self_destruct constructor_selfdestruct_state of
  | (INR NONE, finished) =>
      let am = initial_machine_state with
        <|accounts := finished.rollback.accounts;
          pending_deletions := finished.rollback.toDelete|> in
      (finalize_pending_deletions am).pending_deletions = [] /\
      account_empty (lookup_account (2w:address)
        (finalize_pending_deletions am).accounts)
  | _ => F
Proof
  mp_tac constructor_selfdestruct_deferred >>
  simp[vyperInterpreterTheory.finalize_pending_deletions_def,
       AllCaseEqs()] >>
  Cases_on `step_self_destruct constructor_selfdestruct_state` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED

(* These regressions execute actual constructor bytecode.  Recursive evaluation
   is translated through the proved CPS correspondence, not an injected outcome. *)
Definition blueprint_test_context_def:
  blueprint_test_context = empty_evaluation_context with txn :=
    empty_call_txn with <|sender := 43w; target := 41w|>
End
val () = cv_auto_trans blueprint_test_context_def;

Definition blueprint_test_state_def:
  blueprint_test_state code = empty_state with
    <|accounts := update_account 41w
        (empty_account_state with <|balance := 100; nonce := 2; code := [0w]|>)
        (update_account 42w
          (empty_account_state with <|balance := 7; nonce := 4; code := code|>)
          empty_accounts);
      scopes := [FEMPTY];
      logs := [<|logger := 43w; topics := []; data := [99w]|>]|>
End
val () = cv_auto_trans blueprint_test_state_def;

Definition blueprint_test_run_def:
  blueprint_test_run e st = vyperSmallStep$fromtvk (vyperSmallStep$cont
    (vyperSmallStep$eval_expr_cps blueprint_test_context e st vyperSmallStep$DoneK))
End
val () = cv_auto_trans blueprint_test_run_def;

Definition blueprint_test_address_def:
  blueprint_test_address =
    Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [42w]))
End
val () = cv_auto_trans blueprint_test_address_def;

Definition blueprint_test_expr_def:
  blueprint_test_expr target raw salted rof offset ctor =
    Call (BaseT AddressT) (CreateTarget (CreateFromBlueprint raw) salted rof [])
      ([target; Literal (BaseT (UintT 256)) (IntL 0)] ++
       (if salted then
         [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w))]
        else []) ++
       [Literal (BaseT (UintT 256)) (IntL (&offset))] ++ ctor) NONE
End
val () = cv_auto_trans blueprint_test_expr_def;

Definition blueprint_test_raw_arg_def:
  blueprint_test_raw_arg bs =
    Literal (BaseT (BytesT (Dynamic (LENGTH bs)))) (BytesL bs)
End
val () = cv_auto_trans blueprint_test_raw_arg_def;

(* This twelve-byte loader returns the two raw constructor bytes copied from
   offset twelve of initcode, proving that the blueprint prefix was skipped. *)
Definition blueprint_test_loader_def:
  blueprint_test_loader : byte list =
    [0x60w;2w;0x60w;12w;0x60w;0w;0x39w;
     0x60w;2w;0x60w;0w;0xf3w]
End
val () = cv_auto_trans blueprint_test_loader_def;

Definition blueprint_test_code_def:
  blueprint_test_code = [0xfew;0x71w;0w] ++ blueprint_test_loader
End
val () = cv_auto_trans blueprint_test_code_def;

Definition blueprint_test_observe_def:
  blueprint_test_observe code e expected sender_nonce address nonce runtime =
    let r = blueprint_test_run e (blueprint_test_state code) in
    eval_expr blueprint_test_context e (blueprint_test_state code) = r /\
    FST r = expected /\
    let final = SND r in
    (lookup_account 41w final.accounts).balance = 100 /\
    (lookup_account 41w final.accounts).nonce = sender_nonce /\
    (lookup_account 41w final.accounts).code = [0w] /\
    (lookup_account 42w final.accounts).balance = 7 /\
    (lookup_account 42w final.accounts).nonce = 4 /\
    (lookup_account 42w final.accounts).code = code /\
    (lookup_account address final.accounts).nonce = nonce /\
    (lookup_account address final.accounts).code = runtime /\
    final.logs = [<|logger := 43w; topics := []; data := [99w]|>] /\
    final.scopes = [FEMPTY] /\ final.immutables = [] /\
    final.requests = [] /\ IS_NONE final.outcomes
End
val () = blueprint_test_observe_def
  |> SRULE [vyperSmallStepTheory.eval_expr_eq_cont_cps,
            GSYM blueprint_test_run_def]
  |> cv_auto_trans;

Theorem blueprint_offset_and_constructor_bytes:
  blueprint_initcode (blueprint_copy_size 3 blueprint_test_code)
    3 blueprint_test_code [0xaaw;0xbbw] =
      blueprint_test_loader ++ [0xaaw;0xbbw] /\
  blueprint_test_observe blueprint_test_code
    (blueprint_test_expr blueprint_test_address T F T 3
      [blueprint_test_raw_arg [0xaaw;0xbbw]])
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))))
    3 (vfmContext$address_for_create 41w 2) 1 [0xaaw;0xbbw]
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_wrapped_offset_pads_small_positive_size:
  blueprint_copy_size (2 ** 256 - 1) [0w] = 2 /\
  blueprint_initcode 2 (2 ** 256 - 1) [0w] [0xaaw;0xbbw] =
    [0w;0w;0xaaw;0xbbw] /\
  blueprint_test_observe [0w]
    (blueprint_test_expr blueprint_test_address T F T (2 ** 256 - 1)
      [blueprint_test_raw_arg [0xaaw;0xbbw]])
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))))
    3 (vfmContext$address_for_create 41w 2) 1 []
Proof
  CONV_TAC cv_eval
QED

(* Equal length gives zero, length+one gives -one, and the sign-bit boundary
   gives -2^255.  These hard source failures do not become soft zero returns. *)
Theorem blueprint_zero_and_signed_negative_source_sizes:
  EVERY (\offset.
    EVERY (\rof.
      blueprint_test_observe [0w]
        (blueprint_test_expr blueprint_test_address T F rof offset
          [blueprint_test_raw_arg []])
        (INR (Error (RuntimeError "create source has no deployable code")))
        2 (vfmContext$address_for_create 41w 2) 0 [])
      [F;T])
    [1;2;2 ** 255 + 1]
Proof
  simp[listTheory.EVERY_DEF] >> CONV_TAC cv_eval
QED

(* Project the built initcode as well as the checks: an oversized accepted
   signed-positive size must produce [] rather than materializing its padding. *)
Definition blueprint_test_guard_def:
  blueprint_test_guard offset raw ctor tys =
    OPTION_MAP (\info. (info.cc_source_ok,info.cc_size_ok,info.cc_initcode))
      (build_create_code (get_tenv blueprint_test_context)
        (CreateFromBlueprint raw)
        <|co_code_src := AddressCodeSource 42w; co_ctor_args := ctor;
          co_value := 0; co_code_offset := SOME offset; co_salt := SOME 0w|>
        (blueprint_test_state [0w]).accounts tys NONE)
End
val () = cv_auto_trans blueprint_test_guard_def;

Theorem blueprint_oversized_copy_rejected_before_padding:
  blueprint_copy_size (2 ** 255 + 2) [0w] = 2 ** 255 - 1 /\
  blueprint_test_guard (2 ** 255 + 2) T [BytesV []]
    [BaseT (BytesT (Dynamic 0))] = SOME (T,F,[]) /\
  blueprint_test_observe [0w]
    (blueprint_test_expr blueprint_test_address T T F (2 ** 255 + 2)
      [blueprint_test_raw_arg []])
    (INR (Error (RuntimeError "create initcode too large")))
    2 (vfmContext$address_for_create 41w 2) 0 []
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_encoded_constructor_counts_toward_size_limit:
  blueprint_copy_size (2 ** 256 - 49120) [0w] = 49121 /\
  blueprint_test_guard (2 ** 256 - 49120) F [IntV 7]
    [BaseT (UintT 256)] = SOME (T,F,[]) /\
  blueprint_test_observe [0w]
    (blueprint_test_expr blueprint_test_address F T T (2 ** 256 - 49120)
      [Literal (BaseT (UintT 256)) (IntL 7)])
    (INR (Error (RuntimeError "create initcode too large")))
    2 (vfmContext$address_for_create 41w 2) 0 [] /\
  blueprint_test_observe [0w]
    (blueprint_test_expr blueprint_test_address F F T (2 ** 256 - 49119)
      [Literal (BaseT (UintT 256)) (IntL 7)])
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))))
    3 (vfmContext$address_for_create 41w 2) 1 []
Proof
  CONV_TAC cv_eval
QED

Definition blueprint_test_nested_create_def:
  blueprint_test_nested_create =
    Call (BaseT AddressT) (CreateTarget RawCreate F T [])
      [blueprint_test_raw_arg [0w];
       Literal (BaseT (UintT 256)) (IntL 0)] NONE
End
val () = cv_auto_trans blueprint_test_nested_create_def;

Definition blueprint_test_nested_post_def:
  blueprint_test_nested_post = blueprint_test_state [] with accounts :=
    create_prelude_accounts 41w (vfmContext$address_for_create 41w 2) 0
      (blueprint_test_state []).accounts
End
val () = cv_auto_trans blueprint_test_nested_post_def;

Theorem blueprint_test_nested_run:
  blueprint_test_run blueprint_test_nested_create (blueprint_test_state []) =
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))),
     blueprint_test_nested_post)
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_test_nested_eval:
  eval_expr blueprint_test_context blueprint_test_nested_create
    (blueprint_test_state []) =
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))),
     blueprint_test_nested_post)
Proof
  simp[vyperSmallStepTheory.eval_expr_eq_cont_cps,
       GSYM blueprint_test_run_def, blueprint_test_nested_run]
QED

Theorem blueprint_test_nested_source_check:
  check_create_blueprint T
    [AddressV (vfmContext$address_for_create 41w 2); IntV 0;
     BytesV (REPLICATE 32 0w); IntV 0] blueprint_test_nested_post =
    (INR (Error (RuntimeError "create source has no deployable code")),
     blueprint_test_nested_post) /\
  check_create_blueprint F
    [AddressV (vfmContext$address_for_create 41w 2); IntV 0; IntV 0]
    blueprint_test_nested_post =
    (INR (Error (RuntimeError "create source has no deployable code")),
     blueprint_test_nested_post)
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_test_outer_failure:
  blueprint_test_run
    (blueprint_test_expr blueprint_test_nested_create F salted rof 0
      [blueprint_test_nested_create]) (blueprint_test_state []) =
  (INR (Error (RuntimeError "create source has no deployable code")),
   blueprint_test_nested_post)
Proof
  rewrite_tac[blueprint_test_run_def,
    GSYM vyperSmallStepTheory.eval_expr_eq_cont_cps] >>
  Cases_on `salted` >>
  simp[blueprint_test_expr_def, Once evaluate_def] >>
  simp[Once evaluate_def, vyperStateTheory.bind_def,
       blueprint_test_nested_eval] >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  ntac 8 (simp[Once evaluate_def, vyperStateTheory.bind_def,
    vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    vyperValueOperationTheory.evaluate_literal_def]) >>
  simp[blueprint_test_nested_source_check]
QED

(* The prefix deploys an empty-runtime target, then fails its source check.
   The identical nested deployment in the constructor suffix must not run.
   Nonce three and the first deployed account survive the expression error;
   the second prospective deployment is still absent. *)
Theorem blueprint_nested_deployment[local]:
  eval_expr blueprint_test_context blueprint_test_nested_create
    (blueprint_test_state []) =
  (INL (Value (AddressV (vfmContext$address_for_create 41w 2))),
   blueprint_test_state [] with accounts :=
     update_account (vfmContext$address_for_create 41w 2)
       (empty_account_state with nonce := 1)
       (update_account 41w
         (empty_account_state with <|balance := 100; nonce := 3; code := [0w]|>)
         (update_account 42w
           (empty_account_state with <|balance := 7; nonce := 4; code := []|>)
           empty_accounts)))
Proof
  rewrite_tac[vyperSmallStepTheory.eval_expr_eq_cont_cps] >>
  CONV_TAC cv_eval
QED

Theorem blueprint_empty_source_check[local]:
  let st = blueprint_test_state [] with accounts :=
     update_account (vfmContext$address_for_create 41w 2)
       (empty_account_state with nonce := 1)
       (update_account 41w
         (empty_account_state with <|balance := 100; nonce := 3; code := [0w]|>)
         (update_account 42w
           (empty_account_state with <|balance := 7; nonce := 4; code := []|>)
           empty_accounts)) in
  check_create_blueprint salted
    ([AddressV (vfmContext$address_for_create 41w 2); IntV 0] ++
     (if salted then [BytesV (REPLICATE 32 0w)] else []) ++ [IntV 0]) st =
  (INR (Error (RuntimeError "create source has no deployable code")),st)
Proof
  Cases_on `salted` >> CONV_TAC cv_eval
QED

Theorem blueprint_invalid_source_result[local]:
  eval_expr blueprint_test_context
    (blueprint_test_expr blueprint_test_nested_create F salted rof 0
      [blueprint_test_nested_create]) (blueprint_test_state []) =
  (INR (Error (RuntimeError "create source has no deployable code")),
   blueprint_test_state [] with accounts :=
     update_account (vfmContext$address_for_create 41w 2)
       (empty_account_state with nonce := 1)
       (update_account 41w
         (empty_account_state with <|balance := 100; nonce := 3; code := [0w]|>)
         (update_account 42w
           (empty_account_state with <|balance := 7; nonce := 4; code := []|>)
           empty_accounts)))
Proof
  Cases_on `salted` >>
  simp[blueprint_test_expr_def, evaluate_def, blueprint_nested_deployment,
       SRULE [LET_THM] (Q.INST [`salted` |-> `F`] blueprint_empty_source_check),
       SRULE [LET_THM] (Q.INST [`salted` |-> `T`] blueprint_empty_source_check),
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.read_result_def,
       vyperStateTheory.read_results_def, vyperValueOperationTheory.evaluate_literal_def] >>
  CONV_TAC cv_eval
QED

Theorem blueprint_invalid_source_precedes_constructor_effects:
  EVERY (\salted.
    EVERY (\rof.
        let e = blueprint_test_expr blueprint_test_nested_create F salted rof 0
          [blueprint_test_nested_create] in
        let r = blueprint_test_run e (blueprint_test_state []) in
        eval_expr blueprint_test_context e (blueprint_test_state []) = r /\
        FST r = INR (Error (RuntimeError "create source has no deployable code")) /\
        let final = SND r in
        (lookup_account 41w final.accounts).nonce = 3 /\
        (lookup_account 41w final.accounts).balance = 100 /\
        (lookup_account (vfmContext$address_for_create 41w 2) final.accounts).nonce = 1 /\
        (lookup_account (vfmContext$address_for_create 41w 2) final.accounts).code = [] /\
        (lookup_account (vfmContext$address_for_create 41w 3) final.accounts).nonce = 0 /\
        (lookup_account (vfmContext$address_for_create 41w 3) final.accounts).code = [] /\
        final.logs = [<|logger := 43w; topics := []; data := [99w]|>] /\
        final.requests = [] /\ IS_NONE final.outcomes)
    [F;T])
  [F;T]
Proof
  simp[vyperSmallStepTheory.eval_expr_eq_cont_cps,
       GSYM blueprint_test_run_def, listTheory.EVERY_DEF,
       blueprint_test_outer_failure] >>
  CONV_TAC cv_eval
QED

(* An empty source is legal at U-1: the signed wrapped size is one.  During
   constructor-argument evaluation, CREATE deposits one byte at that previously
   empty source address.  CREATE2's observable address distinguishes the saved
   one-byte size from an incorrect recomputation producing two zero bytes. *)
Definition blueprint_test_populate_source_def:
  blueprint_test_populate_source =
    Call (BaseT AddressT) (CreateTarget RawCreate F T [])
      [blueprint_test_raw_arg [0x60w;1w;0x60w;0w;0xf3w];
       Literal (BaseT (UintT 256)) (IntL 0)] NONE
End
val () = cv_auto_trans blueprint_test_populate_source_def;

(* The constructor argument would install nonempty code at the blueprint
   address itself.  At offset zero that source is invalid before evaluation,
   so it cannot be repaired by running the constructor expression early. *)
Theorem blueprint_constructor_cannot_make_invalid_source_valid:
  EVERY (\salted.
    EVERY (\rof.
      blueprint_test_observe []
        (blueprint_test_expr
          (Literal (BaseT AddressT)
            (BytesL (word_to_bytes (vfmContext$address_for_create 41w 2) T)))
          F salted rof 0 [blueprint_test_populate_source])
        (INR (Error (RuntimeError "create source has no deployable code")))
        2 (vfmContext$address_for_create 41w 2) 0 [])
      [F;T])
    [F;T]
Proof
  simp[listTheory.EVERY_DEF] >> CONV_TAC cv_eval
QED

Definition blueprint_test_captured_address_def:
  blueprint_test_captured_address =
    vfmExecution$address_for_create2 41w 0w
      ([0w] ++ REPLICATE 12 0w ++
       word_to_bytes (vfmContext$address_for_create 41w 2) T)
End
val () = cv_auto_trans blueprint_test_captured_address_def;

Definition blueprint_test_captured_post_def:
  blueprint_test_captured_post =
    let populated = update_account (vfmContext$address_for_create 41w 2)
      (empty_account_state with <|nonce := 1; code := [0w]|>)
      blueprint_test_nested_post.accounts in
    blueprint_test_nested_post with accounts :=
      create_prelude_accounts 41w blueprint_test_captured_address 0 populated
End
val () = cv_auto_trans blueprint_test_captured_post_def;

Theorem blueprint_test_captured_run:
  blueprint_test_run
    (blueprint_test_expr
      (Literal (BaseT AddressT)
        (BytesL (word_to_bytes (vfmContext$address_for_create 41w 2) T)))
      F T T (2 ** 256 - 1) [blueprint_test_populate_source])
    (blueprint_test_state []) =
  (INL (Value (AddressV blueprint_test_captured_address)),
   blueprint_test_captured_post)
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_size_is_captured_before_constructor_changes_source:
  blueprint_copy_size (2 ** 256 - 1) [] = 1 /\
  let e = blueprint_test_expr
    (Literal (BaseT AddressT)
      (BytesL (word_to_bytes (vfmContext$address_for_create 41w 2) T)))
    F T T (2 ** 256 - 1) [blueprint_test_populate_source] in
  let r = blueprint_test_run e (blueprint_test_state []) in
  eval_expr blueprint_test_context e (blueprint_test_state []) = r /\
    FST r = INL (Value (AddressV blueprint_test_captured_address)) /\
    let final = SND r in
    (lookup_account 41w final.accounts).nonce = 4 /\
    (lookup_account 41w final.accounts).balance = 100 /\
    (lookup_account (vfmContext$address_for_create 41w 2) final.accounts).nonce = 1 /\
    (lookup_account (vfmContext$address_for_create 41w 2) final.accounts).code = [0w] /\
    (lookup_account blueprint_test_captured_address final.accounts).nonce = 1 /\
    (lookup_account blueprint_test_captured_address final.accounts).code = [] /\
    final.logs = [<|logger := 43w; topics := []; data := [99w]|>] /\
    final.requests = [] /\ IS_NONE final.outcomes
Proof
  rewrite_tac[vyperSmallStepTheory.eval_expr_eq_cont_cps,
       GSYM blueprint_test_run_def, LET_THM] >>
  BETA_TAC >> rewrite_tac[blueprint_test_captured_run] >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  CONV_TAC cv_eval
QED

(* These execution regressions must remain kernel-closed. *)
val () = List.app (fn th =>
  if List.all (fn tag => tag = "DISK_THM")
       (fst (Tag.dest_tag (Thm.tag th)))
  then () else raise Fail "create regression has oracle dependencies")
  [blueprint_test_nested_run, blueprint_test_nested_source_check,
   blueprint_test_outer_failure, blueprint_test_captured_run,
   blueprint_invalid_source_precedes_constructor_effects,
   blueprint_size_is_captured_before_constructor_changes_source,
   blueprint_constructor_cannot_make_invalid_source_valid,
   blueprint_wrapped_offset_pads_small_positive_size,
   blueprint_oversized_copy_rejected_before_padding,
   blueprint_encoded_constructor_counts_toward_size_limit,
   blueprint_zero_and_signed_negative_source_sizes,
   vyperSmallStepTheory.eval_expr_eq_cont_cps];

(* The constructor tuple is (DynArray[uint256,3],uint256), whose array-length
   word is 64 bytes into its ABI encoding. This loader returns that word from
   initcode offset 12+64 as the deployed runtime. *)
Definition create_argument_loader_def:
  create_argument_loader : byte list =
    [0x60w;32w;0x60w;76w;0x60w;0w;0x39w;
     0x60w;32w;0x60w;0w;0xf3w]
End
val () = cv_auto_trans create_argument_loader_def;

Definition create_argument_state_def:
  create_argument_state =
    blueprint_test_state ([0xfew;0x71w;0w] ++ create_argument_loader) with
      scopes := [FEMPTY |+ ("d",
        <|assignable := T;
          type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
          value := ArrayV (DynArrayV [IntV 1; IntV 2; IntV 3]); popped := []|>)]
End
val () = cv_auto_trans create_argument_state_def;

Definition create_argument_expr_def:
  create_argument_expr raw =
    let salt = TypeBuiltin (BaseT (BytesT (Fixed 32))) Convert
      (BaseT (BytesT (Fixed 32)))
      [Pop (BaseT (UintT 256)) (NameTarget "d")];
        ctor = [Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "d";
                Pop (BaseT (UintT 256)) (NameTarget "d")]
    in if raw then
      Call (BaseT AddressT) (CreateTarget RawCreate T T [])
        ([blueprint_test_raw_arg create_argument_loader;
          Literal (BaseT (UintT 256)) (IntL 0)] ++ ctor ++ [salt]) NONE
    else
      Call (BaseT AddressT) (CreateTarget (CreateFromBlueprint F) T T [])
        ([blueprint_test_address;
          Literal (BaseT (UintT 256)) (IntL 0); salt;
          Literal (BaseT (UintT 256)) (IntL 3)] ++ ctor) NONE
End
val () = cv_auto_trans create_argument_expr_def;

Definition create_argument_result_def:
  create_argument_result raw =
    blueprint_test_run (create_argument_expr raw) create_argument_state
End
val () = cv_auto_trans create_argument_result_def;

(* Raw creation reads constructor arguments before evaluating salt; blueprint
   creation evaluates salt in its prefix. Both read the array after the later
   constructor pop. The differing deployed lengths distinguish all three stages. *)
Theorem create_constructor_reads_and_salt_order:
  EVERY (\raw.
    eval_expr blueprint_test_context (create_argument_expr raw)
      create_argument_state = create_argument_result raw /\
    (lookup_account 41w (SND (create_argument_result raw)).accounts).nonce = 3 /\
    (case FST (create_argument_result raw) of
     | INL (Value result) =>
         (case dest_AddressV result of
          | SOME address =>
              (lookup_account address (SND (create_argument_result raw)).accounts).nonce = 1 /\
              (lookup_account address (SND (create_argument_result raw)).accounts).code =
                REPLICATE 31 0w ++ [if raw then 2w else 1w]
          | NONE => F)
     | _ => F) /\
    OPTION_MAP (\entry. entry.value)
      (lookup_scopes "d" (SND (create_argument_result raw)).scopes) =
        SOME (ArrayV (DynArrayV [IntV 1])))
  [F;T]
Proof
  simp[vyperSmallStepTheory.eval_expr_eq_cont_cps,
       GSYM blueprint_test_run_def, create_argument_result_def,
       listTheory.EVERY_DEF, Excl "OPTION_MAP_EQ_SOME"] >>
  conj_tac
  >- (conj_tac >- CONV_TAC cv_eval >>
      conj_tac >- CONV_TAC cv_eval >>
      CONV_TAC (LAND_CONV (RAND_CONV cv_eval)) >> simp[]) >>
  conj_tac >- CONV_TAC cv_eval >>
  conj_tac >- CONV_TAC cv_eval >>
  CONV_TAC (LAND_CONV (RAND_CONV cv_eval)) >> simp[]
QED
