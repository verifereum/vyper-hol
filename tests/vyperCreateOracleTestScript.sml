(* Oracle-mode execution matrix for all creation builtins. The final sentinel
   makes both over-consumption and failure to consume observable. *)
Theory vyperCreateOracleTest
Ancestors
  vyperCreateSelfdestruct vyperCreate vyperCallOutcome extCallOracle
  vyperContext vyperState vfmState vfmExecution list
Libs
  wordsLib cv_transLib

Definition create_oracle_test_code_def:
  create_oracle_test_code kind : byte list =
    case kind of
      CreateMinimalProxy =>
        [0x60w;0x2dw;0x3dw;0x81w;0x60w;0x09w;0x3dw;0x39w;0xf3w;
         0x36w;0x3dw;0x3dw;0x37w;0x3dw;0x3dw;0x3dw;0x36w;0x3dw;0x73w] ++
        REPLICATE 19 0w ++ [42w] ++
        [0x5aw;0xf4w;0x3dw;0x82w;0x80w;0x3ew;0x90w;0x3dw;
         0x91w;0x60w;0x2bw;0x57w;0xfdw;0x5bw;0xf3w]
    | CreateCopyOf =>
        [0x62w;0w;0w;1w;0x3dw;0x81w;0x60w;0x0bw;0x3dw;0x39w;0xf3w;0w]
    | CreateFromBlueprint _ => [0w]
    | RawCreate => [0w]
End
val () = cv_auto_trans create_oracle_test_code_def;

Definition create_oracle_test_values_def:
  create_oracle_test_values kind salted =
    [if kind = RawCreate then BytesV [0w] else AddressV 42w; IntV 0] ++
    (if salted then [BytesV (REPLICATE 31 0w ++ [7w])] else []) ++
    (case kind of CreateFromBlueprint _ => [IntV 0] | _ => [])
End
val () = cv_auto_trans create_oracle_test_values_def;

Definition create_oracle_test_types_def:
  create_oracle_test_types kind salted =
    [if kind = RawCreate then BaseT (BytesT (Dynamic 1)) else BaseT AddressT;
     BaseT (UintT 256)] ++
    (if salted then [BaseT (BytesT (Fixed 32))] else []) ++
    (case kind of CreateFromBlueprint _ => [BaseT (UintT 256)] | _ => [])
End
val () = cv_auto_trans create_oracle_test_types_def;

Definition create_oracle_test_request_def:
  create_oracle_test_request kind salted =
    create_outcome_request (if salted then Create2Call 7w else CreateCall)
      0 (create_oracle_test_code kind) (blueprint_test_state [0w])
End
val () = cv_auto_trans create_oracle_test_request_def;

Definition create_oracle_test_outcome_def:
  create_oracle_test_outcome kind salted success data =
    (failed_outcome (create_oracle_test_request kind salted)) with
      <|co_success := success; co_created := if success then 55w else 0w;
        co_returnData := data;
        co_accounts := increment_nonce 41w (blueprint_test_state [0w]).accounts;
        co_logs := [<|logger := 55w; topics := []; data := [88w]|>];
        co_toDelete := [55w]|>
End
val () = cv_auto_trans create_oracle_test_outcome_def;

Definition create_oracle_test_state_def:
  create_oracle_test_state kind salted success data =
    (blueprint_test_state [0w]) with
      <|pending_deletions := [44w];
        outcomes := SOME [create_oracle_test_outcome kind salted success data;
                          failed_outcome (create_oracle_test_request kind salted)]|>
End
val () = cv_auto_trans create_oracle_test_state_def;

Definition create_oracle_test_observe_def:
  create_oracle_test_observe kind salted rof success data =
    let (result,final) = eval_create blueprint_test_context kind salted rof
      (create_oracle_test_types kind salted)
      (create_oracle_test_values kind salted) (SOME 1)
      (create_oracle_test_state kind salted success data) in
    result = (if success then INL (Value (AddressV 55w))
              else if rof then INR (Error (RevertData data))
              else INL (Value (AddressV 0w))) ∧
    final.requests = [create_oracle_test_request kind salted] ∧
    final.outcomes = SOME [failed_outcome (create_oracle_test_request kind salted)] ∧
    (lookup_account 41w final.accounts).nonce = 3 ∧
    final.logs = (blueprint_test_state [0w]).logs ++
      (if success then [<|logger := 55w; topics := []; data := [88w]|>] else []) ∧
    final.pending_deletions = (if success then [55w] else [44w]) ∧
    final.scopes = (blueprint_test_state [0w]).scopes ∧
    final.immutables = (blueprint_test_state [0w]).immutables
End
val () = cv_auto_trans create_oracle_test_observe_def;

Theorem create_oracle_builtin_outcome_matrix:
  EVERY (λkind. EVERY (λsalted. EVERY (λrof.
    create_oracle_test_observe kind salted rof T [] ∧
    create_oracle_test_observe kind salted rof F [0xaaw;0xbbw] ∧
    create_oracle_test_observe kind salted rof F []) [F;T]) [F;T])
    [CreateMinimalProxy; CreateCopyOf; CreateFromBlueprint F; RawCreate]
Proof
  simp[listTheory.EVERY_DEF] >> CONV_TAC cv_eval
QED

(* A blueprint rejection precedes CREATE and must leave the stream untouched. *)
Theorem create_oracle_source_failure_does_not_consume:
  EVERY (λrof.
    let st = create_oracle_test_state (CreateFromBlueprint F) F F [] in
    let (result,final) = eval_create blueprint_test_context (CreateFromBlueprint F)
      F rof (create_oracle_test_types (CreateFromBlueprint F) F)
      [AddressV 42w; IntV 0; IntV 1] (SOME 0) st in
    result = INR (Error (RuntimeError "create source has no deployable code")) ∧
    final.outcomes = st.outcomes ∧ final.requests = []) [F;T]
Proof
  simp[listTheory.EVERY_DEF] >> CONV_TAC cv_eval
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "vyperCreateOracleTest");
