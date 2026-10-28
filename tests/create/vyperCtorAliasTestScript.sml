(* Constructor argument aliasing: an earlier local array is mutated by a later
   argument before the generated code copies the earlier value to its tuple. *)
Theory vyperCtorAliasTest
Ancestors
  vyperCreateMemoryTest createCtorAliasCompileTest vyperCreateSelfdestruct
  vyperSmallStep[ignore_grammar] vyperCreate vyperState vyperContext
  vfmCompute vfmContext vfmState finite_map finite_set list
Libs
  cv_transLib wordsLib memoryStoreWitnessLib evalCompilerBytecodeLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["constructor-alias/oracle"]
val pinned_runtime = #2 (pairSyntax.dest_pair
  (memoryStoreWitnessLib.oracle "constructor-alias/oracle" "ctor_alias"))
val checked_runtime = rhs (concl
  createCtorAliasCompileTestTheory.create_ctor_alias_runtime_def)
val pinned_hex = memoryStoreWitnessLib.hex_list pinned_runtime
val checked_hex = memoryStoreWitnessLib.hex_list checked_runtime
(* The merged compiler now closes this bytecode-parity gap. Keep the
   aliasing observations for both runtimes and require exact parity as well. *)
val () = if checked_hex = pinned_hex then ()
  else raise Fail "Constructor alias runtime differs from pinned Vyper"

Definition ctor_alias_pinned_runtime_def:
  ctor_alias_pinned_runtime = ^pinned_runtime
End
val () = cv_auto_trans ctor_alias_pinned_runtime_def;

Theorem ctor_alias_runtime_matches_pinned:
  create_ctor_alias_runtime = ctor_alias_pinned_runtime
Proof
  simp[create_ctor_alias_runtime_def, ctor_alias_pinned_runtime_def]
QED

Definition ctor_alias_accounts_def:
  ctor_alias_accounts runtime =
    update_account 41w
      (empty_account_state with
        <|balance := 100; nonce := 2; code := runtime|>)
      (update_account 42w
        (empty_account_state with code := [0w]) empty_accounts)
End
val () = cv_auto_trans ctor_alias_accounts_def;

Definition ctor_alias_array_type_def:
  ctor_alias_array_type = ArrayT (BaseT (UintT 256)) (Dynamic 2)
End
val () = cv_auto_trans ctor_alias_array_type_def;

Definition ctor_alias_expr_def:
  ctor_alias_expr =
    Call (BaseT AddressT) (CreateTarget RawCreate F F [])
      [Name (BaseT (BytesT (Dynamic 1))) "b";
       Literal (BaseT (UintT 256)) (IntL 0);
       Name ctor_alias_array_type "xs";
       Pop (BaseT (UintT 256)) (NameTarget "xs")] NONE
End
val () = cv_auto_trans ctor_alias_expr_def;

Definition ctor_alias_source_state_def:
  ctor_alias_source_state =
    let local_scope =
      (FEMPTY |+ ("b", <|assignable := F;
                         type := BaseTV (BytesT (Dynamic 1));
                         value := BytesV [0w]|>))
             |+ ("xs", <|assignable := T;
                          type := ArrayTV (BaseTV (UintT 256)) (Dynamic 2);
                          value := ArrayV (DynArrayV [IntV 1; IntV 2])|>) in
    let st = empty_state with
      <|accounts := ctor_alias_accounts ctor_alias_pinned_runtime;
        scopes := [local_scope]|> in
    st with outcomes :=
      SOME [failed_outcome (create_outcome_request CreateCall 0 [] st)]
End
val () = cv_auto_trans ctor_alias_source_state_def;

Definition ctor_alias_source_result_def:
  ctor_alias_source_result =
    blueprint_test_run ctor_alias_expr ctor_alias_source_state
End
val () = cv_auto_trans ctor_alias_source_result_def;

Theorem ctor_alias_source_is_big_step:
  eval_expr blueprint_test_context ctor_alias_expr ctor_alias_source_state =
    ctor_alias_source_result
Proof
  simp[vyperSmallStepTheory.eval_expr_eq_cont_cps,
       GSYM blueprint_test_run_def, ctor_alias_source_result_def]
QED

Definition ctor_alias_vm_def:
  ctor_alias_vm runtime =
    let rb = <|accounts := ctor_alias_accounts runtime;
               tStorage := empty_transient_storage; toDelete := [];
               accesses := <|addresses := fINSERT 43w (fINSERT 41w fEMPTY);
                             storageKeys := fEMPTY |> |> in
    let ctxt = initial_context 41w runtime F
      empty_return_destination
      (make_evm_tx 43w 41w 0 (create_memory_calldata RawCreate) 1000000) in
    <|contexts := [(ctxt,rb)]; rollback := rb;
      originalAccounts := ctor_alias_accounts runtime;
      txParams := vyper_to_tx_params blueprint_test_context.txn;
      msdomain := Collect empty_domain|>
End
val () = cv_auto_trans ctor_alias_vm_def;

Definition ctor_alias_observation_def:
  ctor_alias_observation runtime =
    let src = SND ctor_alias_source_result in
    let src_code = case src.requests of [] => NONE | rq::rest => SOME rq.cr_data in
    let vm_code = case seek_create 1000 (ctor_alias_vm runtime) of
      NONE => NONE
    | SOME es => case create_memory_fields es of
        NONE => NONE
      | SOME (kind,amount,code) => SOME (kind,amount,code) in
    (src_code,vm_code,src.outcomes,
     lookup_scopes_val "xs" src.scopes)
End
val () = cv_auto_trans ctor_alias_observation_def;

Definition ctor_alias_request_agrees_def:
  ctor_alias_request_agrees runtime =
    case ctor_alias_observation runtime of
      (SOME src_code,SOME (kind,amount,vm_code),SOME outcomes,SOME xs) =>
        kind = CreateCall /\ amount = 0 /\ outcomes = [] /\
        xs = ArrayV (DynArrayV [IntV 1]) /\
        LENGTH src_code = 129 /\ LENGTH vm_code = 129 /\
        src_code = vm_code
    | _ => F
End
val () = cv_auto_trans ctor_alias_request_agrees_def;

Theorem ctor_alias_request_agrees:
  ctor_alias_request_agrees create_ctor_alias_runtime /\
  ctor_alias_request_agrees ctor_alias_pinned_runtime
Proof
  CONV_TAC cv_eval
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "vyperCtorAliasTest");
