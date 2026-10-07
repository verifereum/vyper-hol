(*
 * High-level semantics for Vyper contract-creation builtins.
 *
 * TOP-LEVEL:
 *   dest_create_args       — decode evaluated operands by kind/layout
 *   create_arg_ctor_types  — recover constructor-argument types
 *   minimal_proxy_initcode — EIP-1167 initcode (54 bytes)
 *   create_address         — CREATE/CREATE2 address selection
 *   eval_create            — shared interpreter/CPS creation semantics
 *)

Theory vyperCreate
Ancestors
  arithmetic byte combin integer list option pair rich_list words
  contractABI sptree vfmConstants vfmState vfmContext
  vfmExecution[ignore_grammar] vyperAST vyperABI vyperMisc vyperValue
  vyperContext vyperState
Libs
  cv_transLib wordsLib monadsyntax

Datatype:
  create_code_source
  = AddressCodeSource address
  | BytecodeCodeSource (byte list)
End

Datatype:
  create_operands = <|
    co_code_src: create_code_source
  ; co_ctor_args: value list
  ; co_value: num
  ; co_code_offset: num option
  ; co_salt: bytes32 option
  |>
End

(* ===== Operand decoding ===== *)

Definition dest_create_salt_def:
  dest_create_salt v =
    case dest_BytesV v of
    | SOME bs => if LENGTH bs = 32 then SOME (word_of_bytes_be bs : bytes32)
                 else NONE
    | NONE => NONE
End

val () = cv_auto_trans dest_create_salt_def;

Definition dest_optional_num_def:
  dest_optional_num NONE = SOME NONE /\
  dest_optional_num (SOME v) = OPTION_MAP SOME (dest_NumV v)
End

val () = cv_auto_trans dest_optional_num_def;

Definition dest_optional_salt_def:
  dest_optional_salt NONE = SOME NONE /\
  dest_optional_salt (SOME v) = OPTION_MAP SOME (dest_create_salt v)
End

val () = cv_auto_trans dest_optional_salt_def;

Definition make_create_operands_def:
  make_create_operands address_src src_v value_v offset_v salt_v ctor_args =
    case (if address_src then OPTION_MAP AddressCodeSource (dest_AddressV src_v)
          else OPTION_MAP BytecodeCodeSource (dest_BytesV src_v)) of
    | NONE => NONE
    | SOME src =>
        case dest_NumV value_v of
        | NONE => NONE
        | SOME amount =>
            case dest_optional_num offset_v of
            | NONE => NONE
            | SOME offset =>
                case dest_optional_salt salt_v of
                | NONE => NONE
                | SOME salt => SOME <|
                    co_code_src := src;
                    co_ctor_args := ctor_args;
                    co_value := amount;
                    co_code_offset := offset;
                    co_salt := salt
                  |>
End

val () = cv_auto_trans make_create_operands_def;

Definition dest_create_args_def:
  dest_create_args kind has_salt vs =
    case kind of
    | CreateMinimalProxy =>
        if has_salt then
          (case vs of [target; value; salt] =>
             make_create_operands T target value NONE (SOME salt) []
           | _ => NONE)
        else
          (case vs of [target; value] =>
             make_create_operands T target value NONE NONE []
           | _ => NONE)
    | CreateCopyOf =>
        if has_salt then
          (case vs of [target; value; salt] =>
             make_create_operands T target value NONE (SOME salt) []
           | _ => NONE)
        else
          (case vs of [target; value] =>
             make_create_operands T target value NONE NONE []
           | _ => NONE)
    | CreateFromBlueprint raw_args =>
        if has_salt then
          (case vs of target::value::salt::code_offset::ctor_args =>
             make_create_operands T target value (SOME code_offset)
               (SOME salt) ctor_args
           | _ => NONE)
        else
          (case vs of target::value::code_offset::ctor_args =>
             make_create_operands T target value (SOME code_offset) NONE ctor_args
           | _ => NONE)
    | RawCreate =>
        (case vs of
         | bytecode::value::rest =>
             if has_salt then
               if NULL rest then NONE
               else make_create_operands F bytecode value NONE
                 (SOME (LAST rest)) (FRONT rest)
             else make_create_operands F bytecode value NONE NONE rest
         | _ => NONE)
End

val dest_create_args_pre_def =
  cv_auto_trans_pre "dest_create_args_pre" dest_create_args_def;

Theorem dest_create_args_pre[cv_pre]:
  !kind has_salt vs. dest_create_args_pre kind has_salt vs
Proof
  rw[dest_create_args_pre_def]
QED

(* Recover only the constructor-argument suffix/middle from the static types. *)
Definition create_arg_ctor_types_def:
  create_arg_ctor_types kind has_salt tys =
    case kind of
    | CreateMinimalProxy =>
        if has_salt then
          (case tys of [_; _; _] => SOME [] | _ => NONE)
        else (case tys of [_; _] => SOME [] | _ => NONE)
    | CreateCopyOf =>
        if has_salt then
          (case tys of [_; _; _] => SOME [] | _ => NONE)
        else (case tys of [_; _] => SOME [] | _ => NONE)
    | CreateFromBlueprint raw_args =>
        if has_salt then
          (case tys of _::_::_::_::ctor_tys => SOME ctor_tys | _ => NONE)
        else (case tys of _::_::_::ctor_tys => SOME ctor_tys | _ => NONE)
    | RawCreate =>
        (case tys of
         | _::_::rest =>
             if has_salt then
               if NULL rest then NONE else SOME (FRONT rest)
             else SOME rest
         | _ => NONE)
End

val create_arg_ctor_types_pre_def =
  cv_auto_trans_pre "create_arg_ctor_types_pre" create_arg_ctor_types_def;

Theorem create_arg_ctor_types_pre[cv_pre]:
  !kind has_salt tys. create_arg_ctor_types_pre kind has_salt tys
Proof
  rw[create_arg_ctor_types_pre_def]
QED

(* ===== Initcode construction ===== *)

Definition minimal_proxy_loader_def:
  minimal_proxy_loader : byte list =
    [0x60w; 0x2dw; 0x3dw; 0x81w; 0x60w; 0x09w; 0x3dw; 0x39w; 0xf3w]
End

Definition minimal_proxy_forwarder_pre_def:
  minimal_proxy_forwarder_pre : byte list =
    [0x36w; 0x3dw; 0x3dw; 0x37w; 0x3dw;
     0x3dw; 0x3dw; 0x36w; 0x3dw; 0x73w]
End

Definition minimal_proxy_forwarder_post_def:
  minimal_proxy_forwarder_post : byte list =
    [0x5aw; 0xf4w; 0x3dw; 0x82w; 0x80w;
     0x3ew; 0x90w; 0x3dw; 0x91w; 0x60w;
     0x2bw; 0x57w; 0xfdw; 0x5bw; 0xf3w]
End

Definition minimal_proxy_runtime_def:
  minimal_proxy_runtime (target : address) =
    minimal_proxy_forwarder_pre ++ word_to_bytes target T ++
    minimal_proxy_forwarder_post
End

Definition minimal_proxy_initcode_def:
  minimal_proxy_initcode (target : address) =
    minimal_proxy_loader ++ minimal_proxy_runtime target
End

Definition create_copy_initcode_def:
  create_copy_initcode code =
    [0x62w] ++
    DROP 29 (word_to_bytes_be ((n2w (LENGTH code)) : bytes32)) ++
    [0x3dw; 0x81w; 0x60w; 0x0bw; 0x3dw; 0x39w; 0xf3w] ++ code
End

Definition blueprint_initcode_def:
  blueprint_initcode code_offset code args_enc =
    DROP code_offset code ++ args_enc
End

Definition raw_create_initcode_def:
  raw_create_initcode bytecode args_enc = bytecode ++ args_enc
End

Definition blueprint_code_ok_def:
  blueprint_code_ok code_offset code =
    (0i < w2i ((n2w (LENGTH code) - n2w code_offset) : bytes32))
End

Definition encode_create_ctor_args_def:
  encode_create_ctor_args tenv tys vs =
    case vyper_to_abi_list tenv tys vs of
    | NONE => NONE
    | SOME avs =>
        SOME (contractABI$enc
          (contractABI$Tuple (vyper_to_abi_types tenv tys))
          (contractABI$ListV avs))
End

Definition create_address_def:
  create_address self nonce salt_opt initcode =
    case salt_opt of
    | NONE => vfmContext$address_for_create self nonce
    | SOME salt => vfmExecution$address_for_create2 self salt initcode
End

val () = cv_auto_trans minimal_proxy_loader_def;
val () = cv_auto_trans minimal_proxy_forwarder_pre_def;
val () = cv_auto_trans minimal_proxy_forwarder_post_def;
val () = cv_auto_trans minimal_proxy_runtime_def;
val () = cv_auto_trans minimal_proxy_initcode_def;
val () = cv_auto_trans create_copy_initcode_def;
val () = cv_auto_trans blueprint_initcode_def;
val () = cv_auto_trans raw_create_initcode_def;
val () = cv_auto_trans blueprint_code_ok_def;
val () = cv_auto_trans encode_create_ctor_args_def;
val () = cv_auto_trans create_address_def;

Theorem LENGTH_minimal_proxy_runtime[simp]:
  LENGTH (minimal_proxy_runtime target) = 45
Proof
  simp[minimal_proxy_runtime_def, minimal_proxy_forwarder_pre_def,
       minimal_proxy_forwarder_post_def]
QED

Theorem LENGTH_minimal_proxy_initcode[simp]:
  LENGTH (minimal_proxy_initcode target) = 54
Proof
  simp[minimal_proxy_initcode_def, minimal_proxy_loader_def]
QED

(* ===== Kind-specific code and account effects ===== *)

Datatype:
  create_code = <|
    cc_initcode: byte list
  ; cc_runtime_code: byte list option
  ; cc_source_ok: bool
  |>
End

Definition build_create_code_def:
  build_create_code tenv CreateMinimalProxy ops accounts ctor_tys =
    (case ops.co_code_src of
     | AddressCodeSource target => SOME <|
         cc_initcode := minimal_proxy_initcode target;
         cc_runtime_code := SOME (minimal_proxy_runtime target);
         cc_source_ok := T
       |>
     | _ => NONE) /\
  build_create_code tenv CreateCopyOf ops accounts ctor_tys =
    (case ops.co_code_src of
     | AddressCodeSource target =>
         let code = (lookup_account target accounts).code in
           SOME <| cc_initcode := create_copy_initcode code;
                   cc_runtime_code := SOME code;
                   cc_source_ok := (code <> []) |>
     | _ => NONE) /\
  build_create_code tenv (CreateFromBlueprint raw_args) ops accounts ctor_tys =
    (case (ops.co_code_src, ops.co_code_offset) of
     | (AddressCodeSource target, SOME code_offset) =>
         let code = (lookup_account target accounts).code in
         let args_enc_opt =
           if raw_args then
             case ops.co_ctor_args of [BytesV bs] => SOME bs | _ => NONE
           else encode_create_ctor_args tenv ctor_tys ops.co_ctor_args
         in
           (case args_enc_opt of
            | NONE => NONE
            | SOME args_enc => SOME <|
                cc_initcode := blueprint_initcode code_offset code args_enc;
                cc_runtime_code := NONE;
                cc_source_ok := blueprint_code_ok code_offset code
              |>)
     | _ => NONE) /\
  build_create_code tenv RawCreate ops accounts ctor_tys =
    (case ops.co_code_src of
     | BytecodeCodeSource bytecode =>
         (case encode_create_ctor_args tenv ctor_tys ops.co_ctor_args of
          | NONE => NONE
          | SOME args_enc => SOME <|
              cc_initcode := raw_create_initcode bytecode args_enc;
              cc_runtime_code := NONE;
              cc_source_ok := T
            |>)
     | _ => NONE)
End

val () = cv_auto_trans build_create_code_def;

Definition install_created_code_def:
  install_created_code address NONE accounts = accounts /\
  install_created_code address (SOME code) accounts =
    update_account address ((lookup_account address accounts) with code := code)
      accounts
End

val () = cv_auto_trans install_created_code_def;

Definition proceed_create_accounts_def:
  proceed_create_accounts sender address amount runtime_code accounts =
    let accounts1 = vfmExecution$increment_nonce sender accounts in
    let accounts2 =
      (vfmExecution$transfer_value sender address amount o
       vfmExecution$increment_nonce address) accounts1 in
      install_created_code address runtime_code accounts2
End

val () = cv_auto_trans proceed_create_accounts_def;

Theorem install_created_code_storage[simp]:
  (lookup_account a (install_created_code address runtime_code accounts)).storage =
  (lookup_account a accounts).storage
Proof
  Cases_on `runtime_code` >>
  simp[install_created_code_def, vfmStateTheory.lookup_account_def,
       vfmStateTheory.update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem increment_nonce_storage[simp]:
  (lookup_account a (vfmExecution$increment_nonce address accounts)).storage =
  (lookup_account a accounts).storage
Proof
  simp[vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `a = address` >> gvs[combinTheory.APPLY_UPDATE_THM]
QED

Theorem proceed_create_accounts_storage[simp]:
  (lookup_account a
    (proceed_create_accounts sender address amount runtime_code accounts)).storage =
  (lookup_account a accounts).storage
Proof
  Cases_on `runtime_code` >>
  simp[proceed_create_accounts_def, install_created_code_def,
       vfmExecutionTheory.transfer_value_def,
       vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `amount = 0` >> Cases_on `sender = address` >>
  Cases_on `a = address` >> Cases_on `a = sender` >>
  gvs[combinTheory.APPLY_UPDATE_THM]
QED

Definition create_soft_failure_def:
  create_soft_failure rof msg =
    if rof then raise (Error (RuntimeError msg))
    else return (Value (AddressV 0w))
End

val () = create_soft_failure_def
  |> SRULE [FUN_EQ_THM, return_def, raise_def, COND_RATOR]
  |> cv_auto_trans;

(* ===== Verifereum-backed creation execution =====

   Like the external-call boundary (run_ext_call in vyperInterpreter), the
   creation boundary defers execution to Verifereum's EVM semantics.  The
   Vyper adapter mirrors Verifereum's step_create prelude: increment the
   sender nonce, reset the target account to empty_account_state, transfer
   the value, and increment the (fresh) target nonce.  It then pushes a
   Code-destination context over the initcode and runs it, letting Verifereum
   own constructor execution, code deposit (handle_create), failure, and
   rollback.  The adapter returns:
     - SOME (addr, SOME code, accounts', tStorage', logs') on success, where
       code is the returned runtime code installed by the EVM;
     - SOME (addr, NONE, accounts, tStorage, []) on revert (effects rolled
       back to the pre-call snapshot but nonce/value effects kept);
     - NONE for EVM exceptions (caller decides how to approximate). *)

Definition make_create_tx_def:
  make_create_tx sender address value gas_limit : transaction =
    <| from := sender
     ; to := SOME address
     ; data := []
     ; nonce := 0
     ; value := value
     ; gasLimit := gas_limit
     ; gasPrice := 0
     ; accessList := []
     ; blobVersionedHashes := []
     ; maxFeePerBlobGas := NONE
     ; maxFeePerGas := NONE
     ; authorizationList := []
    |>
End

val () = cv_auto_trans make_create_tx_def;

(* Transaction parameters built directly from the Vyper call_txn (mirrors
   vyperInterpreter$vyper_to_tx_params, which lives in a downstream theory to
   avoid a dependency cycle). *)
Definition create_tx_params_def:
  create_tx_params (txn: call_txn) : transaction_parameters =
    <| origin := txn.origin
     ; gasPrice := txn.gas_price
     ; baseFeePerGas := txn.base_fee
     ; baseFeePerBlobGas := txn.blob_base_fee
     ; blockNumber := txn.block_number
     ; blockTimeStamp := txn.time_stamp
     ; blockCoinBase := txn.coinbase
     ; blockGasLimit := txn.gas_limit
     ; prevRandao := n2w txn.prev_randao
     ; prevHashes := txn.block_hashes
     ; blobHashes := txn.blob_hashes
     ; chainId := txn.chain_id
     ; authRefund := 0
    |>
End

val () = cv_auto_trans create_tx_params_def;

(* Effectively infinite gas for creation execution (see
   vyperInterpreter$default_call_gas_limit). *)
Definition default_create_gas_limit_def:
  default_create_gas_limit : num = 2 ** 64
End

val () = cv_auto_trans default_create_gas_limit_def;

(* Mirror of make_ext_call_state for creation: build the single-context
   execution state whose message runs the initcode with a Code destination. *)
Definition make_create_state_def:
  make_create_state sender address initcode value
                    accounts tStorage txParams =
    let gas_limit = default_create_gas_limit in
    let tx = make_create_tx sender address value gas_limit in
    let ctxt = initial_context address initcode F (Code address) tx in
    let accesses = <| addresses := fINSERT sender (fINSERT address fEMPTY)
                    ; storageKeys := fEMPTY |> in
    let rollback = <| accounts := accounts
                    ; tStorage := tStorage
                    ; accesses := accesses
                    ; toDelete := [] |> in
    <| contexts := [(ctxt, rollback)]
     ; txParams := txParams
     ; rollback := rollback
     ; msdomain := Collect empty_domain
    |>
End

(* Extract creation results from Verifereum execution.  Success yields the
   deposited runtime code (the initcode's RETURN data); revert yields the
   original state snapshot with no code. *)
Definition extract_create_result_def:
  extract_create_result orig_accounts orig_tStorage
    (result : unit + vfmExecution$exception option, final_state) =
    case final_state.contexts of
    | [(ctxt, _)] =>
        (case result of
         | INR NONE =>
             SOME (SOME ctxt.returnData,
                   final_state.rollback.accounts,
                   final_state.rollback.tStorage, ctxt.logs)
         | INR (SOME Reverted) =>
             SOME (NONE, orig_accounts, orig_tStorage, [])
         | _ => NONE)
    | _ => NONE
End

val () = cv_auto_trans make_create_state_def;
val () = cv_auto_trans extract_create_result_def;

(* Account well-typedness gate for the creation outcome, mirroring
   vyperInterpreter$ext_call_success_accounts_ok.  The quantified form over
   evm_accounts has a function type the cv translator rejects, so (as there)
   the gate is routed through the spt encoding via a [cv_rep] registration. *)
Definition create_account_ok_def:
  create_account_ok (a : account_state) <=>
    a.balance < 2 ** 256 /\ LENGTH a.code <= 24576
End

val () = cv_auto_trans create_account_ok_def;

(* Quantified accounts gate; not cv-translated directly (the quantifier is
   over a function type) — routed through the spt encoding via a [cv_rep]
   registration, mirroring vyperInterpreter$accounts_runtime_well_typed. *)
Definition create_accounts_ok_def:
  create_accounts_ok (accounts : evm_accounts) <=>
    !addr. create_account_ok (lookup_account addr accounts)
End

Definition create_accounts_spt_ok_def:
  (create_accounts_spt_ok (LN : account_state spt) <=> T) /\
  (create_accounts_spt_ok (LS a) <=> create_account_ok a) /\
  (create_accounts_spt_ok (BN l r) <=>
    create_accounts_spt_ok l /\ create_accounts_spt_ok r) /\
  (create_accounts_spt_ok (BS l a r) <=>
    create_accounts_spt_ok l /\ create_account_ok a /\
    create_accounts_spt_ok r)
End

val () = cv_auto_trans create_accounts_spt_ok_def;

Theorem create_accounts_spt_ok_lookup:
  !t k a. wf t /\ create_accounts_spt_ok t /\ lookup k t = SOME a ==>
          create_account_ok a
Proof
  Induct >> rw[create_accounts_spt_ok_def, sptreeTheory.lookup_def,
               sptreeTheory.wf_def]
  >> metis_tac[]
QED

Theorem create_accounts_spt_ok_insert:
  !k a t. create_accounts_spt_ok t /\ create_account_ok a ==>
          create_accounts_spt_ok (sptree$insert k a t)
Proof
  recInduct sptreeTheory.insert_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[create_accounts_spt_ok_def] >>
  Cases_on `k = 0` >-
    simp[Once sptreeTheory.insert_def, create_accounts_spt_ok_def] >>
  Cases_on `EVEN k` >-
    (PURE_ONCE_REWRITE_TAC [sptreeTheory.insert_def] >>
     gvs[create_accounts_spt_ok_def]) >>
  PURE_ONCE_REWRITE_TAC [sptreeTheory.insert_def] >>
  gvs[create_accounts_spt_ok_def]
QED

Theorem create_account_ok_empty_account_state[simp]:
  create_account_ok empty_account_state
Proof
  simp[create_account_ok_def, empty_account_state_def]
QED

Theorem create_accounts_spt_ok_build_spt:
  !accounts. create_accounts_spt_ok
    (build_spt empty_account_state (dimword (:160)) accounts) <=>
    create_accounts_ok accounts
Proof
  rw[create_accounts_ok_def, EQ_IMP_THM]
  >- (
    Cases_on `accounts addr = empty_account_state` >- simp[lookup_account_def] >>
    `lookup (w2n addr) (build_spt empty_account_state (dimword (:160)) accounts) =
       SOME (accounts addr)`
      by (simp[lookup_build_spt] >> qspec_then `addr` mp_tac wordsTheory.w2n_lt >> simp[]) >>
    simp[lookup_account_def] >>
    irule create_accounts_spt_ok_lookup >>
    qexistsl [`w2n addr`, `build_spt empty_account_state (dimword (:160)) accounts`] >>
    simp[] ) >>
  qsuff_tac `!n. create_accounts_spt_ok
                  (build_spt empty_account_state n accounts)` >- simp[] >>
  Induct >- simp[build_spt_def, create_accounts_spt_ok_def] >>
  simp[build_spt_def] >> rw[] >>
  irule create_accounts_spt_ok_insert >> simp[] >>
  first_x_assum (qspec_then `n2w n` mp_tac) >> simp[lookup_account_def]
QED

val cv_create_accounts_spt_ok_thm = theorem "cv_create_accounts_spt_ok_thm";

Theorem create_accounts_ok_cv_rep[cv_rep]:
  cv_rep T
    (cv_create_accounts_spt_ok (from_evm_accounts accounts))
    b2c
    (create_accounts_ok accounts)
Proof
  simp[cv_repTheory.cv_rep_def, from_evm_accounts_def,
       GSYM cv_create_accounts_spt_ok_thm] >>
  AP_TERM_TAC >>
  simp[Once (GSYM create_accounts_spt_ok_build_spt)]
QED

Definition create_accounts_ok_aux_def:
  create_accounts_ok_aux
    (result : unit + vfmExecution$exception option) accounts =
    case result of
    | INR NONE => create_accounts_ok accounts
    | _ => T
End

val () = cv_auto_trans create_accounts_ok_aux_def;

(* Run a creation through Verifereum.  Accounts should already reflect the
   step_create prelude (sender nonce incremented, target account reset to
   empty, value transferred, target nonce incremented). *)
Definition run_create_evm_def:
  run_create_evm sender address initcode value accounts tStorage txParams =
    case vfmExecution$run_call
           (make_create_state sender address initcode value
              accounts tStorage txParams) of
    | SOME outcome =>
        if create_accounts_ok_aux (FST outcome) (SND outcome).rollback.accounts
        then extract_create_result accounts tStorage outcome
        else NONE
    | NONE => NONE
End

val () = cv_auto_trans run_create_evm_def;

(* Verifereum's proceed_create account prelude: reset target, transfer value,
   bump both nonces.  Sender-nonce increment is done separately so that the
   pre-collision nonce snapshot is available. *)
Definition create_prelude_accounts_def:
  create_prelude_accounts sender address value accounts =
    let accounts0 = update_account address empty_account_state accounts in
    let accounts1 =
      (vfmExecution$transfer_value sender address value o
       vfmExecution$increment_nonce address) accounts0 in
      vfmExecution$increment_nonce sender accounts1
End

val () = cv_auto_trans create_prelude_accounts_def;

(* Shared by the recursive interpreter and the CPS machine.  All operands have
   already been evaluated before this helper is entered.  Vyper-specific
   pre-creation checks (operand shape, source availability, balance, nonce,
   initcode size, address collision) stay at this builtin boundary; the
   creation itself is executed by Verifereum via run_create_evm, including
   constructor effects, code deposit, and revert rollback.

   revert_on_failure: a hard failure (bad operands/source, insufficient
   balance, collision, EVM exception) reverts the Vyper frame when rof holds;
   with rof = F it yields the zero address.  A plain EVM revert inside the
   created initcode returns the zero address regardless of rof, matching the
   EVM: CREATE/CREATE2 push 0 on revert rather than propagating an exception. *)
Definition eval_create_def:
  eval_create cx kind has_salt rof arg_tys vs = do
    ops <- lift_option_type (dest_create_args kind has_salt vs)
      "create operand shape";
    ctor_tys <- lift_option_type (create_arg_ctor_types kind has_salt arg_tys)
      "create argument type shape";
    accounts <- get_accounts;
    code_info <- lift_option_type
      (build_create_code (get_tenv cx) kind ops accounts ctor_tys)
      "create operands";
    (* copy-of/blueprint ASSERTs are emitted before CREATE and always revert. *)
    check code_info.cc_source_ok "create source has no deployable code";
    self_acct <<- lookup_account cx.txn.target accounts;
    new_addr <<- create_address cx.txn.target self_acct.nonce ops.co_salt
      code_info.cc_initcode;
    check (LENGTH code_info.cc_initcode <= 2 * max_code_size)
      "create initcode too large";
    if self_acct.balance < ops.co_value \/
       SUC self_acct.nonce >= 2 ** 64
    then create_soft_failure rof "create insufficient balance or nonce limit"
    else do
      existing <<- lookup_account new_addr accounts;
      if vfmExecution$account_already_created existing then do
        update_accounts (vfmExecution$increment_nonce cx.txn.target);
        create_soft_failure rof "create address collision"
      od else do
        check (existing.balance + ops.co_value < 2 ** 256)
          "create recipient balance overflow";
        tStorage <- get_transient_storage;
        update_accounts
          (create_prelude_accounts cx.txn.target new_addr ops.co_value);
        post <- get_accounts;
        case run_create_evm cx.txn.target new_addr code_info.cc_initcode
               ops.co_value post tStorage
               (create_tx_params cx.txn) of
        | NONE => create_soft_failure rof "create failed"
        | SOME (code_opt, accounts', tStorage', logs') => do
            update_accounts (K accounts');
            update_transient (K tStorage');
            case code_opt of
            | SOME _ => return (Value (AddressV new_addr))
            | NONE => return (Value (AddressV 0w))
          od
      od
    od
  od
End

(* eval_create is cv-translated by first inlining the higher-order monad
   plumbing (ignore_bind / bind / lift_option / liftk), the same way the
   *_pre definitions in vyperSmallStepScript.sml are prepared.  Without this
   the translator hits ignore_bind, whose g argument has the higher-order type
   'evaluation_state -> (α + exception) # evaluation_state, and aborts with
   "Argument contains function type".  The adapter result itself is plain
   data: run_create_evm and extract_create_result are both cv-translated above
   and return a 4-tuple of code_opt / accounts / tStorage / logs. *)
val eval_create_cv_def = eval_create_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, lift_option_def, lift_option_type_def,
            lift_sum_def, lift_sum_runtime_def, prod_CASE_rator, LET_RATOR,
            UNCURRY, sum_CASE_rator, option_CASE_rator, COND_RATOR]
  |> cv_auto_trans;

(* KEY LEMMA: the EVM-backed branch of eval_create only updates accounts,
   transient storage, and logs — never scopes or immutables. *)
(* The two-step accessor chain leaves a combined record update, which the
   per-field accfupds theorems do not directly simplify. *)
Theorem evaluation_state_accounts_tStorage_acc:
  (s with <| accounts := a; tStorage := t |>).scopes = s.scopes /\
  (s with <| accounts := a; tStorage := t |>).immutables = s.immutables /\
  (s with <| accounts := a; tStorage := t |>).accounts = a /\
  (s with <| accounts := a; tStorage := t |>).tStorage = t
Proof
  Cases_on `s` >> simp[evaluation_state_accfupds]
QED

(* KEY LEMMA: the EVM-backed tail of eval_create only updates accounts,
   transient storage, and logs — never scopes or immutables.  Stated with
   create_soft_failure and the accessor monads already unfolded, so that it
   matches eval_create's body directly. *)
Theorem create_tail_preserves_scopes:
  (case run_create_evm a b c d e f g of
   | NONE =>
       if rof then raise (Error (RuntimeError "create failed"))
       else return (Value (AddressV 0w))
   | SOME (code_opt, accounts', tStorage', logs') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          case code_opt of
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => return (Value (AddressV 0w))
       od) s = (res, st') ==>
  st'.scopes = s.scopes /\ st'.immutables = s.immutables
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e f g` >|
   [(* adapter returned NONE: soft failure, state untouched *)
    (Cases_on `rof` >>
     gvs[update_accounts_def, update_transient_def, return_def,
         raise_def, AllCaseEqs(), evaluation_state_accfupds]),
    (* adapter returned SOME: install accounts and transient storage *)
    (PairCases_on `x` >> Cases_on `x0` >>
     gvs[bind_apply, ignore_bind_apply, update_accounts_def,
         update_transient_def, return_def, AllCaseEqs()] >>
     strip_tac >>
     qpat_x_assum `Y = st'` (fn tm => ONCE_ASM_REWRITE_TAC[GSYM tm]) >>
     simp[evaluation_state_accounts_tStorage_acc])]
QED

(* The EVM-backed tail never touches the log list: the adapter's logs' is
   bound but deliberately not installed, so logs are unchanged.  TODO(#379):
   once constructors may emit logs semantically, eval_create should append
   logs' and this should become a prefix (append) extension instead. *)
Theorem create_tail_preserves_logs:
  (case run_create_evm a b c d e1 g txp of
   | NONE =>
       if rof then raise (Error (RuntimeError "create failed"))
       else return (Value (AddressV 0w))
   | SOME (code_opt, accounts', tStorage', logs') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          case code_opt of
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => return (Value (AddressV 0w))
       od) s = (res, st') ==>
  st'.logs = s.logs
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp`
  >- (Cases_on `rof` >> gvs[return_def, raise_def]) >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `Y = st'` (fn tm => ONCE_ASM_REWRITE_TAC[GSYM tm]) >>
  simp[evaluation_state_accounts_tStorage_acc]
QED

(* The soft-failure and collision pre-checks also leave logs untouched. *)
Theorem create_prelude_preserves_logs:
  (if b1 then
     create_soft_failure rof "create insufficient balance or nonce limit"
   else if b2 then
     do update_accounts f;
        create_soft_failure rof "create address collision"
     od
   else
     do x <- assert b3 (Error (RuntimeError "create recipient balance overflow"));
        return $ Value (AddressV 0w)
     od) s = (res, st') ==>
  st'.logs = s.logs
Proof
  strip_tac >>
  Cases_on `b1`
  >- (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]) >>
  Cases_on `b2`
  >- (Cases_on `rof` >>
      gvs[ignore_bind_apply, update_accounts_def, create_soft_failure_def,
          return_def, raise_def,           evaluation_state_accounts_tStorage_acc]) >>
  gvs[assert_def, bind_apply, return_def, raise_def, AllCaseEqs()]
QED

(* Every raise in the pre-creation checks raises an Error. *)
Theorem create_soft_failure_exception_is_error:
  create_soft_failure rof msg s = (INR ex, st') ==> ?err. ex = Error err
Proof
  Cases_on `rof`
  >- (strip_tac >> gvs[create_soft_failure_def, raise_def] >>
      qexists_tac `RuntimeError msg` >> simp[]) >>
  (* rof = F: returns the zero address, so no exception is possible *)
  strip_tac >>
  gvs[create_soft_failure_def, return_def]
QED

(* Every raise on the EVM-backed tail raises an Error; the remaining outcomes
   all come from return. *)
Theorem create_tail_exception_is_error:
  (case run_create_evm a b c d e1 g txp of
   | NONE =>
       if rof then raise (Error (RuntimeError "create failed"))
       else return (Value (AddressV 0w))
   | SOME (code_opt, accounts', tStorage', logs') =>
       do update_accounts (K accounts');
          update_transient (K tStorage');
          case code_opt of
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => return (Value (AddressV 0w))
       od) s = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp`
  >- (Cases_on `rof` >> gvs[return_def, raise_def]) >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, return_def, raise_def, AllCaseEqs()]
QED

(* The eval_create body, abstracted over its three Vyper-side pre-conditions
   (insufficient balance/nonce, address collision, recipient balance
   overflow).  Splitting these booleans here keeps eval_create's own proof free
   of IF_CASES_TAC on the nested conditionals, which cannot split a
   conditional that is applied to arguments. *)
Theorem eval_create_body_scopes:
  !b1 b2 b3 rof f g a b c d e1 txp new_addr s res st'.
    (if b1 then
       create_soft_failure rof "create insufficient balance or nonce limit"
     else if b2 then
       do x <- update_accounts f;
          create_soft_failure rof "create address collision"
       od
     else
       do x <- assert b3 (Error (RuntimeError "create recipient balance overflow"));
          tStorage <- get_transient_storage;
          x <- update_accounts f;
          post <- get_accounts;
          case run_create_evm a b c d e1 g txp of
          | NONE => create_soft_failure rof "create failed"
          | SOME (code_opt, accounts', tStorage', logs') =>
              do x <- update_accounts (K accounts');
                 x <- update_transient (K tStorage');
                 case code_opt of
                 | SOME _ => return (Value (AddressV new_addr))
                 | NONE => return (Value (AddressV 0w))
              od
       od) s = (res, st') ==>
    st'.scopes = s.scopes /\ st'.immutables = s.immutables
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `b1`
  >- (Cases_on `rof` >>
      gvs[create_soft_failure_def, return_def, raise_def]) >>
  Cases_on `b2`
  >- (Cases_on `rof` >>
      gvs[bind_apply, update_accounts_def, create_soft_failure_def,
          evaluation_state_accfupds, return_def, raise_def]) >>
  (* b3 = T: the balance check passed, so creation proceeds *)
  Cases_on `b3` >-
    (gvs[assert_def, bind_apply, get_transient_storage_def,
         update_accounts_def, get_accounts_def, return_def,
         evaluation_state_accfupds, AllCaseEqs()] >>
     Cases_on `run_create_evm a b c d e1 g txp`
     >- (Cases_on `rof` >>
         gvs[create_soft_failure_def, return_def, raise_def]) >>
     PairCases_on `x` >> Cases_on `x0` >>
     gvs[bind_apply, ignore_bind_apply, update_accounts_def,
         update_transient_def, return_def, evaluation_state_accfupds,
         AllCaseEqs()])
  >>
  (* b3 = F: recipient balance overflow, hard failure before any update *)
  gvs[assert_def, bind_apply, return_def, raise_def]
QED

(* Vyper-local state is untouched by the soft-failure path: it either returns
   the zero address or raises, never updating scopes or immutables. *)
Theorem create_soft_failure_scopes:
  create_soft_failure rof msg st = (res, st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  Cases_on `rof` >> simp[create_soft_failure_def, return_def, raise_def]
QED

(* Logs are unchanged by every eval_create path. *)
Theorem eval_create_preserves_logs:
  eval_create cx kind has_salt rof arg_tys vs st = (res, st') ==>
  st'.logs = st.logs
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys` >>
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, check_def, return_def, raise_def, AllCaseEqs()] >>
  rename1 `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys =
            SOME code_info` >>
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, update_accounts_def, get_transient_storage_def,
      update_transient_def, check_def, assert_def, return_def,
      raise_def, AllCaseEqs(), COND_RATOR] >>
  (* Split out the pre-conditions into a form create_prelude_preserves_logs
     matches, then hand the EVM tail to create_tail_preserves_logs. *)
  gvs[COND_RATOR] >|
  [(* balance / nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* balance / nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* address collision: nonce bump, then soft failure *)
   (Cases_on `rof` >>
    gvs[ignore_bind_apply, update_accounts_def, create_soft_failure_def,
        return_def, raise_def, evaluation_state_accounts_tStorage_acc]),
   (* EVM-backed creation *)
   (gvs[assert_def, bind_apply, get_transient_storage_def,
         get_accounts_def, update_accounts_def, return_def, raise_def,
         AllCaseEqs(), create_soft_failure_def] >>
    qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
      (fn tm => mp_tac tm) >>
    drule create_tail_preserves_logs >>
    simp[])]
QED

Theorem eval_create_preserves_scopes_immutables:
  eval_create cx kind has_salt rof arg_tys vs st = (res, st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys` >>
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, check_def, return_def,
      raise_def, AllCaseEqs()] >>
  rename1 `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys =
            SOME code_info` >>
  (* The pre-conditions are conditionals applied to arguments, which gvs
     cannot case-split.  COND_RATOR eta-expands both of them so that the
     following gvs splits them, leaving four goals in the order
     (balance, collision) = (T,T), (T,F), (F,T), (F,F). *)
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, update_accounts_def, get_transient_storage_def,
      update_transient_def, check_def, assert_def, return_def,
      raise_def, AllCaseEqs(), COND_RATOR,
      evaluation_state_accounts_tStorage_acc] >|
  [(* insufficient balance or nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* insufficient balance or nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* address collision: nonce bump, then soft failure *)
   (Cases_on `rof` >>
    gvs[create_soft_failure_def, return_def, raise_def,
        evaluation_state_accfupds]),
   (* EVM-backed creation *)
   gvs[bind_apply, get_transient_storage_def, update_accounts_def,
       get_accounts_def, return_def, evaluation_state_accfupds, AllCaseEqs(),
       create_soft_failure_def] >>
   qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
     (fn tm => mp_tac tm) >>
   drule create_tail_preserves_scopes >>
   simp[]]
QED

(* Storage is NOT preserved across creation in general: the constructor runs
   arbitrary EVM code that may write any account's storage, including the
   created account's own.  There is therefore no frame rule to prove here,
   and the old eval_create_preserves_storage theorem has been removed as
   false.

   Downstream storage preservation must handle creation the same way it
   handles external calls: by postulating the analogous property at the EVM
   boundary.  Cf. protected_storage_calls_preserve_def in
   vyperTypeStoragePreservationScript.sml, which is postulated for
   run_ext_call.  The matching postulate for run_create_evm belongs beside
   it; create_tail_preserves_scopes above is the shape lemma that hook
   consumes. *)

(* KEY LEMMA for the type-soundness consumer.

   Once the three operand-shape decodes and the initcode construction have
   succeeded, every remaining failure in eval_create is a RuntimeError raised
   by check/assert/create_soft_failure, or comes from the EVM-backed tail —
   which itself performs no typing checks.  So no TypeError is reachable.

   The shape hypotheses are essential: lift_option_type raises
   Error (TypeError _), so without them the lemma is false. *)

(* the soft-failure path either returns the zero address or raises RuntimeError *)
Theorem create_soft_failure_no_type_error:
  create_soft_failure rof msg s = (res, st') ==>
  !m. res <> INR (Error (TypeError m))
Proof
  Cases_on `rof` >> strip_tac >> 
  gvs [create_soft_failure_def] >> gvs [raise_def , return_def]
QED



 (*TRY (qpat_x_assum `raise (Error (RuntimeError msg)) s = (res,st')` mp_tac >>
       simp[raise_def]) >>
  TRY (qpat_x_assum `return (Value (AddressV 0w)) s = (res,st')` mp_tac >>*)

(* the pre-creation checks (balance/nonce, collision, overflow) likewise *)
Theorem create_prelude_no_type_error:
  (if b1 then
     create_soft_failure rof "create insufficient balance or nonce limit"
   else if b2 then
     do update_accounts f;
        create_soft_failure rof "create address collision"
     od
   else
     do x <- assert b3 (Error (RuntimeError "create recipient balance overflow"));
        return $ Value (AddressV 0w)
     od) s = (res, st') ==>
  !m. res <> INR (Error (TypeError m))
Proof
  strip_tac >>
  Cases_on `b1` >- metis_tac[create_soft_failure_no_type_error] >>
  Cases_on `b2`
  >- (gvs[ignore_bind_apply, update_accounts_def, return_def] >>
      metis_tac[create_soft_failure_no_type_error]) >>
  gvs[assert_def, bind_apply, return_def, raise_def, AllCaseEqs()]
QED

(* KEY LEMMA for the type-soundness consumer.  The EVM-backed tail runs no
   typing checks at all: every outcome is either a returned address or a
   RuntimeError, never a TypeError. *)
Theorem create_tail_no_type_error:
  (case run_create_evm a b c d e1 g txp of
   | NONE => create_soft_failure rof "create failed"
   | SOME (code_opt, accounts', tStorage', logs') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          case code_opt of
          | NONE => return (Value (AddressV 0w))
          | SOME _ => return (Value (AddressV new_addr))
       od) s = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp`
  >- (gs[] >> metis_tac[create_soft_failure_no_type_error]) >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `INL _ = res` (fn th => ONCE_ASM_REWRITE_TAC[GSYM th]) >>
  simp[]
QED

(* Variant of the above for the sub-branch where create_soft_failure has
   already been resolved to a raise (rof = T). *)
Theorem create_tail_raise_no_type_error:
  (case run_create_evm a b c d e1 g txp of
   | NONE => raise (Error (RuntimeError "create failed"))
   | SOME (code_opt, accounts', tStorage', logs') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
case code_opt of
           | NONE => return (Value (AddressV 0w))
           | SOME _ => return (Value (AddressV new_addr))
        od) s = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp`
  >- simp[raise_def] >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `INL _ = res` (fn th => ONCE_ASM_REWRITE_TAC[GSYM th]) >>
  simp[]
QED

Theorem eval_create_exception_is_error:
  eval_create cx kind has_salt rof arg_tys vs st = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- gvs[eval_create_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys` >>
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, get_transient_storage_def, update_accounts_def,
      check_def, assert_def, create_soft_failure_def, return_def, raise_def,
      AllCaseEqs(), COND_RATOR] >>
  (* Only the EVM-backed tail can produce an exception: the pre-creation
     checks raise via create_soft_failure or assert, and both are covered by
     their own lemmas. *)
  gvs[COND_RATOR, assert_def, bind_apply, get_transient_storage_def,
      get_accounts_def, update_accounts_def, return_def, raise_def,
      AllCaseEqs()] >>
  qpat_x_assum
    `(case run_create_evm _ _ _ _ _ _ _ of
        NONE =>
          if rof then raise (Error (RuntimeError "create failed"))
          else return (Value (AddressV 0w))
      | SOME (code_opt, accounts', tStorage', logs') =>
          do update_accounts (K accounts');
             update_transient (K tStorage');
             case code_opt of
             | SOME _ =>
                 return (Value (AddressV
                   (create_address cx.txn.target
                     (lookup_account cx.txn.target st.accounts).nonce
                     ops.co_salt x.cc_initcode)))
             | NONE => return (Value (AddressV 0w))
             od) _ = (INR ex, st')` (fn tm => mp_tac tm) >>
  metis_tac[create_tail_exception_is_error]
QED

(* KEY LEMMA for the type-soundness consumer.  Derived now that the
   tail lemmas are available. *)

(* KEY LEMMA for the type-soundness consumer.  Once the two outermost guards
   (source has deployable code, initcode fits in the code limit) hold, the rest
   of eval_create is a three-way chain: two soft failures, or the EVM-backed
   implementation body.  Neither raises a TypeError. *)
Theorem create_body_no_type_error:
  (if g1 then
     create_soft_failure rof "create insufficient balance or nonce limit"
   else if g2 then
     do x <- update_accounts f1;
        create_soft_failure rof "create address collision"
     od
   else
     do x <- assert g3 (Error (RuntimeError "create recipient balance overflow"));
        tStorage <- get_transient_storage;
        x <- update_accounts f2;
        post <- get_accounts;
        (case run_create_evm a b c' d e1 g txp of
           NONE => create_soft_failure rof "create failed"
         | SOME (code_opt,accounts',tStorage',logs') =>
             do x <- update_accounts (K accounts');
                x <- update_transient (K tStorage');
                case code_opt of
                  NONE => return (Value (AddressV 0w))
                | SOME v => return (Value (AddressV new_addr))
                od)
     od) s = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >>
  Cases_on `g1` >- metis_tac[create_soft_failure_no_type_error] >>
  Cases_on `g2`
  >- (gvs[ignore_bind_apply, ignore_bind_def, bind_apply,
         update_accounts_def, return_def] >>
      metis_tac[create_soft_failure_no_type_error]) >>
  gvs[assert_def, bind_apply, ignore_bind_apply, update_accounts_def,
      get_transient_storage_def, return_def, raise_def] >>
  (* overflow guard: failing it is a RuntimeError, passing it exposes the tail *)
  Cases_on `g3`
  >- (gvs[get_accounts_def, return_def] >>
      strip_tac >>
      (* NONE is a create_soft_failure; SOME is the result-application tail *)
      Cases_on `run_create_evm a b c' d e1 g txp`
>- (gs[] >> metis_tac[create_soft_failure_no_type_error]) >>
      PairCases_on `x` >> Cases_on `x0` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          update_transient_def, return_def, raise_def, AllCaseEqs()] >>
      strip_tac >>
      qpat_x_assum `INL _ = res` (fn th => ONCE_ASM_REWRITE_TAC[GSYM th]) >>
      simp[]) >>
  gvs[] >> simp[]
QED

Theorem eval_create_no_type_error:
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys /\
  build_create_code (get_tenv cx) kind ops st.accounts ctor_tys =
    SOME code_info /\
  eval_create cx kind has_salt rof arg_tys vs st = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >>
  qpat_x_assum `eval_create _ _ _ _ _ _ st = _` mp_tac >>
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, update_accounts_def, get_transient_storage_def,
      update_transient_def, check_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, update_accounts_def, get_transient_storage_def,
      update_transient_def, check_def, assert_def, return_def, raise_def,
      AllCaseEqs(), COND_RATOR] >>
  gvs[COND_RATOR] >>
  (* AllCaseEqs has normalised the body into a disjunction whose only
     exceptional results are RuntimeErrors: every disjunct is either a
     create_soft_failure or the EVM-backed tail. *)
  strip_tac >>
  rpt (FIRST [metis_tac[create_soft_failure_no_type_error],
              metis_tac[create_tail_no_type_error],
              gvs[]])
QED
