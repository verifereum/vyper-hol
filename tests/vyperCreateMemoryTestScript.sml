(* Execute the checked HOL compiler's runtime until CREATE, then compare the
   production observer's initcode fields with the source oracle request. *)
Theory vyperCreateMemoryTest
Ancestors
  vyperCreateOracleTest vyperCreateSelfdestruct vyperCreate vyperCallOutcome
  vyperState vyperContext vyperEvmBoundary extCallOracle callTrace
  vfmCompute vfmContext vfmState vfmExecution finite_map finite_set list
  createProxyCompileTest createCopyCompileTest
  createBlueprintCompileTest createRawCompileTest
Libs
  cv_transLib wordsLib

Definition create_memory_runtime_def:
  create_memory_runtime kind =
    case kind of
      CreateMinimalProxy => create_proxy_runtime
    | CreateCopyOf => create_copy_runtime
    | CreateFromBlueprint _ => create_blueprint_runtime
    | RawCreate => create_raw_runtime
End
val () = cv_auto_trans create_memory_runtime_def;

Definition create_memory_calldata_def:
  create_memory_calldata kind : byte list =
    if kind = RawCreate then
      [0x30w;0xc8w;0xd1w;0xdaw] ++
      REPLICATE 31 0w ++ [32w] ++ REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w
    else [0xfdw;0xf8w;0x0bw;0xdaw] ++ REPLICATE 31 0w ++ [42w]
End
val () = cv_auto_trans create_memory_calldata_def;

Definition create_memory_accounts_def:
  create_memory_accounts kind =
    update_account 41w
      (empty_account_state with
        <|balance := 100; nonce := 2; code := create_memory_runtime kind|>)
      (update_account 42w
        (empty_account_state with code :=
          (case kind of CreateFromBlueprint _ => [0xfew;0x71w;0w;0w] | _ => [0w]))
        empty_accounts)
End
val () = cv_auto_trans create_memory_accounts_def;

Definition create_memory_vm_def:
  create_memory_vm kind =
    let rb = <|accounts := create_memory_accounts kind;
               tStorage := empty_transient_storage; toDelete := [];
               accesses := <|addresses := fINSERT 43w (fINSERT 41w fEMPTY);
                             storageKeys := fEMPTY |> |> in
    let ctxt = initial_context 41w (create_memory_runtime kind) F
      empty_return_destination
      (make_evm_tx 43w 41w 0 (create_memory_calldata kind) 1000000) in
    <|contexts := [(ctxt,rb)]; rollback := rb;
      txParams := vyper_to_tx_params blueprint_test_context.txn;
      msdomain := Collect empty_domain|>
End
val () = cv_auto_trans create_memory_vm_def;

val () = cv_auto_trans next_opcode_def;

(* The bound is test fuel, not a replacement for the production observer's
   total traversal. Stop before executing the actual CREATE instruction. *)
Definition seek_create_def:
  seek_create 0 es = NONE ∧
  seek_create (SUC fuel) es =
    (case es.contexts of [] => NONE | (ctxt,rb)::rest =>
       if next_opcode ctxt = SOME Create ∨ next_opcode ctxt = SOME Create2
       then SOME es
       else case step es of
         (INL (),post) => seek_create fuel post
       | (INR _,post) => NONE)
End
val () = cv_auto_trans seek_create_def;

(* Total projection, with a checked link to request_of below. Explicit stack
   patterns keep malformed states out of HD/EL's partial computation cases. *)
Definition create_memory_fields_def:
  create_memory_fields es =
    case es.contexts of [] => NONE | (ctxt,rb)::rest =>
      case (next_opcode ctxt,ctxt.stack) of
        (SOME Create,v::off::sz::tail) =>
          SOME (CreateCall,w2n v,take_pad_0 (w2n sz) (DROP (w2n off) ctxt.memory))
      | (SOME Create2,v::off::sz::salt::tail) =>
          SOME (Create2Call salt,w2n v,
                take_pad_0 (w2n sz) (DROP (w2n off) ctxt.memory))
      | _ => NONE
End
val () = cv_auto_trans create_memory_fields_def;

Theorem create_memory_fields_is_observer_request:
  ∀es kind amount code.
  create_memory_fields es = SOME (kind,amount,code) ⇒
  (request_of es).cr_kind = kind ∧ (request_of es).cr_value = amount ∧
  (request_of es).cr_data = code ∧ observable_call (FST (HD es.contexts))
Proof
  rw[create_memory_fields_def, AllCaseEqs()] >>
  gvs[request_of_def, observable_call_def]
QED

Definition create_memory_source_def:
  create_memory_source kind =
    let st = empty_state with
      <|accounts := create_memory_accounts kind; scopes := [FEMPTY]|> in
    let initial = st with outcomes :=
      SOME [failed_outcome (create_outcome_request CreateCall 0 [] st)] in
    let tys = if kind = RawCreate then
        [BaseT (BytesT (Dynamic 100)); BaseT (UintT 256)]
      else create_oracle_test_types kind F in
    let vals = case kind of CreateFromBlueprint _ => [AddressV 42w; IntV 0; IntV 3]
      | _ => create_oracle_test_values kind F in
    SND (eval_create blueprint_test_context kind F T tys vals (SOME 1) initial)
End
val () = cv_auto_trans create_memory_source_def;

Definition create_memory_observe_def:
  create_memory_observe kind =
    case seek_create 1000 (create_memory_vm kind) of
      NONE => F
    | SOME es =>
        case create_memory_fields es of
          NONE => F
        | SOME fields =>
            let final = create_memory_source kind in
            final.outcomes = SOME [] ∧
            MAP (λrq. (rq.cr_kind,rq.cr_value,rq.cr_data)) final.requests = [fields]
End
val () = cv_auto_trans create_memory_observe_def;

Theorem compiled_create_memory_matches_source_request:
  EVERY create_memory_observe
    [CreateMinimalProxy; CreateCopyOf; CreateFromBlueprint F; RawCreate]
Proof
  simp[listTheory.EVERY_DEF] >> CONV_TAC cv_eval
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "vyperCreateMemoryTest");
