Theory vyperCreateSelfdestruct
Ancestors
  vyperCreate vyperInterpreter vyperSmallStep[ignore_grammar]
  vyperAST vyperContext vyperState vyperValue vyperValueOperation vyperEvalPureExpr
  constSubst vyperPinFold vyperPinFoldProps list vfmExecution vfmState finite_set finite_map
Libs
  wordsLib cv_transLib vyperConstEvalLib

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

Definition blueprint_test_offset_expr_def:
  blueprint_test_offset_expr offset =
    Call (BaseT AddressT) (CreateTarget (CreateFromBlueprint F) F T [])
      [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0); offset] NONE
End
val () = cv_auto_trans blueprint_test_offset_expr_def;

Theorem blueprint_prefix_rejected[local]:
  eval_pure_exprs cx st
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0); off] =
      SOME vs /\
  ~blueprint_literal_offset cx F
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0); off] /\
  blueprint_prefix_size F F vs st.accounts = NONE ==>
  eval_expr cx (blueprint_test_offset_expr off) st =
    (INR (Error (RuntimeError "create source has no deployable code")), st)
Proof
  strip_tac >> drule (CONJUNCT2 eval_pure_to_eval_mutual) >> strip_tac >>
  simp[blueprint_test_offset_expr_def, Once evaluate_def] >>
  simp[vyperStateTheory.bind_def, check_create_blueprint_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Definition blueprint_runtime_state_def:
  blueprint_runtime_state offset =
    (blueprint_test_state [0w]) with scopes :=
      [FEMPTY |+ ("offset", <|assignable := F; type := BaseTV (UintT 256);
                            value := IntV (&offset); popped := []|>)]
End

Definition blueprint_runtime_offset_rejected_def:
  blueprint_runtime_offset_rejected offset =
    let st = blueprint_runtime_state offset in
    let e = blueprint_test_offset_expr (Name (BaseT (UintT 256)) "offset") in
    let expected =
      (INR (Error (RuntimeError "create source has no deployable code")), st) in
    eval_expr blueprint_test_context e st = expected
End

Theorem blueprint_address_bytes_decode[local]:
  dest_AddressV (BytesV (REPLICATE 19 0w ++ [42w])) = SOME 42w
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_source_code_projection[local]:
  (lookup_account 42w (blueprint_test_state [0w]).accounts).code = [0w]
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_runtime_pure_prefix[local]:
  eval_pure_exprs blueprint_test_context (blueprint_runtime_state offset)
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
     Name (BaseT (UintT 256)) "offset"] =
    SOME [BytesV (REPLICATE 19 0w ++ [42w]); IntV 0; IntV (&offset)]
Proof
  simp[eval_pure_expr_def, blueprint_test_address_def, evaluate_literal_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       vyperStateTheory.read_place_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.lift_sum_def, vyperStateTheory.read_memory_path_def,
       vyperStateTheory.evaluate_subscripts_def, vyperStateTheory.lookup_scopes_def,
       blueprint_runtime_state_def, FLOOKUP_UPDATE]
QED

Theorem blueprint_runtime_prefix_guard[local]:
  0 < offset ==>
  blueprint_prefix_size F F
    [BytesV (REPLICATE 19 0w ++ [42w]); IntV 0; IntV (&offset)]
    (blueprint_test_state [0w]).accounts = NONE
Proof
  rw[blueprint_prefix_size_def, dest_create_args_def, make_create_operands_def,
     blueprint_address_bytes_decode, dest_optional_num_def,
     dest_optional_salt_def, dest_NumV_def, blueprint_source_code_projection] >>
  decide_tac
QED

Theorem blueprint_runtime_positive_offset_rejected[local]:
  0 < offset ==> blueprint_runtime_offset_rejected offset
Proof
  strip_tac >> simp_tac bool_ss [blueprint_runtime_offset_rejected_def, LET_THM] >>
  irule blueprint_prefix_rejected >>
  simp[blueprint_literal_offset_def, subst_consts_expr_def,
       pin_fold_expr_def, is_int_literal_def] >>
  qexists_tac `[BytesV (REPLICATE 19 0w ++ [42w]); IntV 0; IntV (&offset)]` >>
  simp[blueprint_runtime_pure_prefix, blueprint_runtime_state_def,
       blueprint_runtime_prefix_guard]
QED

(* A local input remains a runtime operand even when its value is max_uint. *)
Theorem blueprint_runtime_wrapped_offset_rejected:
  EVERY blueprint_runtime_offset_rejected
    [1; 2; 2 ** 255; 2 ** 256 - 1; 2 ** 256 - 2]
Proof
  rewrite_tac[listTheory.EVERY_DEF] >> rpt conj_tac >>
  irule blueprint_runtime_positive_offset_rejected >> CONV_TAC cv_eval
QED

Theorem blueprint_folded_and_runtime_offset_values:
  blueprint_test_observe [0w;0w]
    (blueprint_test_offset_expr
      (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
        [Literal (BaseT (IntT 128)) (IntL 1)]))
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))))
    3 (vfmContext$address_for_create 41w 2) 1 [] /\
  blueprint_test_observe [0w]
    (blueprint_test_offset_expr
      (Builtin (BaseT (UintT 256)) (AsWeiValue Wei)
        [Literal (BaseT (UintT 256)) (IntL (&(2 ** 256 - 1)))]))
    (INL (Value (AddressV (vfmContext$address_for_create 41w 2))))
    3 (vfmContext$address_for_create 41w 2) 1 []
Proof
  CONV_TAC cv_eval
QED

Definition blueprint_literal_test_context_def:
  blueprint_literal_test_context = blueprint_test_context with sources :=
    [(41w, [(NONE,
      [VariableDecl Private
        (Constant (Literal (BaseT (UintT 256)) (IntL (&(2 ** 256 - 1)))))
        "OFFSET" (BaseT (UintT 256)) NONE;
       VariableDecl Private
        (Constant (Literal (BaseT (StringT 4)) (StringL "f()")))
        "SIG" (BaseT (StringT 4)) NONE;
       VariableDecl Private
        (Constant (Builtin (BaseT (BytesT (Fixed 4))) MethodId
          [TopLevelName (BaseT (StringT 4)) (NONE,"SIG")]))
        "SELECTOR" (BaseT (BytesT (Fixed 4))) NONE])])]
End
val () = cv_auto_trans blueprint_literal_test_context_def;

Theorem blueprint_module_constant_literal_modes:
  blueprint_literal_offset blueprint_literal_test_context F
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
     TopLevelName (BaseT (UintT 256)) (NONE,"OFFSET")] /\
  ~blueprint_literal_offset blueprint_literal_test_context F
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
     Name (BaseT (UintT 256)) "OFFSET"]
Proof
  CONV_TAC cv_eval
QED

(* The full module environment expands earlier constants inside a later one. *)
Theorem blueprint_module_constant_signature_expansion:
  subst_consts_expr
    (module_consts_env
      (THE (get_module_code blueprint_literal_test_context NONE)) [])
    (TopLevelName (BaseT (BytesT (Fixed 4))) (NONE,"SELECTOR")) =
  Builtin (BaseT (BytesT (Fixed 4))) MethodId
    [Literal (BaseT (StringT 4)) (StringL "f()")]
Proof
  EVAL_TAC
QED

Definition blueprint_flag_test_context_def:
  blueprint_flag_test_context = blueprint_test_context with sources :=
    [(41w, [(NONE,
      [FlagDecl "Flags" (GENLIST (\n. REPLICATE (SUC n) #"F") 256)])])]
End
val () = cv_auto_trans blueprint_flag_test_context_def;

Definition blueprint_flag_offset_def:
  blueprint_flag_offset =
    TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
      [TypeBuiltin (FlagT (NONE,"Flags")) Convert (FlagT (NONE,"Flags"))
        [TypeBuiltin (BaseT (UintT 256)) MaxValue (BaseT (UintT 256)) []]]
End
val () = cv_auto_trans blueprint_flag_offset_def;

Theorem blueprint_flag_type_environment[local]:
  get_tenv blueprint_flag_test_context =
    FEMPTY |+ ((NONE,"Flags"), FlagArgs 256)
Proof
  simp_tac bool_ss [blueprint_flag_test_context_def] >>
  qabbrev_tac `members = GENLIST (\n. REPLICATE (SUC n) #"F") 256` >>
  `LENGTH members = 256` by
    (qunabbrev_tac `members` >> rewrite_tac[LENGTH_GENLIST]) >>
  simp[get_tenv_def, blueprint_test_context_def,
       type_env_all_modules_def, type_env_for_module_def]
QED

Theorem blueprint_flag_conversion_values[local]:
  evaluate_max_value (BaseT (UintT 256)) =
    INL (IntV (&(2 ** 256 - 1))) /\
  evaluate_convert_from (FEMPTY |+ ((NONE,"Flags"), FlagArgs 256))
    (BaseT (UintT 256)) (IntV (&(2 ** 256 - 1))) (FlagT (NONE,"Flags")) =
    INL (FlagV (2 ** 256 - 1)) /\
  evaluate_convert_from (FEMPTY |+ ((NONE,"Flags"), FlagArgs 256))
    (FlagT (NONE,"Flags")) (FlagV (2 ** 256 - 1)) (BaseT (UintT 256)) =
    INL (IntV (&(2 ** 256 - 1)))
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_flag_runtime_mode[local]:
  ~blueprint_literal_offset blueprint_flag_test_context F
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
     blueprint_flag_offset]
Proof
  simp[blueprint_literal_offset_def, blueprint_flag_offset_def,
       subst_consts_expr_def, pin_fold_expr_def, is_int_literal_def]
QED

Definition blueprint_flag_runtime_rejected_def:
  blueprint_flag_runtime_rejected =
    let st = blueprint_test_state [0w] in
    let e = blueprint_test_offset_expr blueprint_flag_offset in
    ~blueprint_literal_offset blueprint_flag_test_context F
      [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
       blueprint_flag_offset] /\
    eval_expr blueprint_flag_test_context e st =
    (INR (Error (RuntimeError "create source has no deployable code")), st)
End

(* Both conversions preserve max_uint at runtime, but Python does not fold them. *)
Theorem blueprint_full_flag_offset_uses_runtime_guard:
  blueprint_flag_runtime_rejected
Proof
  simp_tac bool_ss [blueprint_flag_runtime_rejected_def, LET_THM,
                    blueprint_flag_runtime_mode] >>
  irule blueprint_prefix_rejected >>
  simp[blueprint_flag_runtime_mode] >>
  qexists_tac `[BytesV (REPLICATE 19 0w ++ [42w]); IntV 0;
               IntV (&(2 ** 256 - 1))]` >>
  simp[blueprint_flag_runtime_mode, eval_pure_expr_def,
       blueprint_flag_offset_def, blueprint_test_address_def, evaluate_literal_def,
       type_builtin_args_length_ok_def, evaluate_type_builtin_def,
       blueprint_flag_type_environment, SRULE [] blueprint_flag_conversion_values,
       expr_type_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  irule blueprint_runtime_prefix_guard >> CONV_TAC cv_eval
QED

Definition blueprint_high_wei_offset_def:
  blueprint_high_wei_offset =
    Builtin (BaseT (UintT 256)) (AsWeiValue Gwei)
      [Literal (BaseT (UintT 256)) (IntL (&((2 ** 256 - 1) DIV 10 ** 9)))]
End
val () = cv_auto_trans blueprint_high_wei_offset_def;

Theorem blueprint_high_wei_normal_form[local]:
  pin_fold_expr blueprint_high_wei_offset =
    Literal (BaseT (UintT 256))
      (IntL (&(((2 ** 256 - 1) DIV 10 ** 9) * 10 ** 9)))
Proof
  CONV_TAC cv_eval
QED

Definition blueprint_high_wei_prefix_def:
  blueprint_high_wei_prefix =
    let st = blueprint_test_state [0w] in
    let n = ((2 ** 256 - 1) DIV 10 ** 9) * 10 ** 9 in
    blueprint_literal_offset blueprint_test_context F
      [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
       blueprint_high_wei_offset] /\
    eval_expr blueprint_test_context blueprint_high_wei_offset st =
      (INL (Value (IntV (&n))), st) /\
    check_create_blueprint F T
      [BytesV (REPLICATE 19 0w ++ [42w]); IntV 0; IntV (&n)] st =
      (INL 129639937, st)
End

Theorem blueprint_high_wei_literal_mode[local]:
  blueprint_literal_offset blueprint_test_context F
    [blueprint_test_address; Literal (BaseT (UintT 256)) (IntL 0);
     blueprint_high_wei_offset]
Proof
  CONV_TAC cv_eval
QED

Theorem blueprint_high_wei_prefix_size[local]:
  blueprint_prefix_size F T
    [BytesV (REPLICATE 19 0w ++ [42w]); IntV 0;
     IntV (&(((2 ** 256 - 1) DIV 10 ** 9) * 10 ** 9))]
    (blueprint_test_state [0w]).accounts = SOME 129639937
Proof
  CONV_TAC cv_eval
QED

(* The folded high value passes the signed wrapped-size guard before the
   separate initcode-size limit; this test does not allocate that initcode. *)
Theorem blueprint_folded_high_wei_uses_literal_guard:
  blueprint_high_wei_prefix
Proof
  simp_tac bool_ss [blueprint_high_wei_prefix_def, LET_THM,
                    blueprint_high_wei_literal_mode] >>
  conj_tac
  >- (irule (MATCH_MP pin_fold_expr_literal_sound blueprint_high_wei_normal_form
              |> REWRITE_RULE [evaluate_literal_def])) >>
  simp[check_create_blueprint_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.return_def, SRULE [] blueprint_high_wei_prefix_size]
QED

Theorem blueprint_folded_high_wei_create_reaches_size_guard:
  blueprint_test_observe [0w]
    (blueprint_test_offset_expr blueprint_high_wei_offset)
    (INR (Error (RuntimeError "create initcode too large")))
    2 (vfmContext$address_for_create 41w 2) 0 []
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
  check_create_blueprint T T
    [AddressV (vfmContext$address_for_create 41w 2); IntV 0;
     BytesV (REPLICATE 32 0w); IntV 0] blueprint_test_nested_post =
    (INR (Error (RuntimeError "create source has no deployable code")),
     blueprint_test_nested_post) /\
  check_create_blueprint F T
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
  simp[blueprint_test_nested_source_check, blueprint_literal_offset_def,
       subst_consts_expr_def, pin_fold_expr_def, is_int_literal_def]
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
  check_create_blueprint salted T
    ([AddressV (vfmContext$address_for_create 41w 2); IntV 0] ++
     (if salted then [BytesV (REPLICATE 32 0w)] else []) ++ [IntV 0]) st =
  (INR (Error (RuntimeError "create source has no deployable code")),st)
Proof
  Cases_on `salted` >> CONV_TAC cv_eval
QED

Theorem blueprint_invalid_source_result:
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
       blueprint_literal_offset_def, subst_consts_expr_def,
       pin_fold_expr_def, is_int_literal_def,
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
