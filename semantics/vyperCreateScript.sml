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
  vyperContext vyperState vyperEvmBoundary
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
  ; cc_source_ok: bool
  |>
End

Definition build_create_code_def:
  build_create_code tenv CreateMinimalProxy ops accounts ctor_tys =
    (case ops.co_code_src of
     | AddressCodeSource target => SOME <|
         cc_initcode := minimal_proxy_initcode target;
         cc_source_ok := T
       |>
     | _ => NONE) /\
  build_create_code tenv CreateCopyOf ops accounts ctor_tys =
    (case ops.co_code_src of
     | AddressCodeSource target =>
         let code = (lookup_account target accounts).code in
SOME <| cc_initcode := create_copy_initcode code;
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
              cc_source_ok := T
            |>)
     | _ => NONE)
End

val () = cv_auto_trans build_create_code_def;

Theorem increment_nonce_storage[simp]:
  (lookup_account a (vfmExecution$increment_nonce address accounts)).storage =
  (lookup_account a accounts).storage
Proof
  simp[vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `a = address` >> gvs[combinTheory.APPLY_UPDATE_THM]
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
   Vyper adapter mirrors Verifereum's step_create / proceed_create: bump the
   sender nonce, transfer the endowment to the fresh address, bump that
   account's nonce, then push a Code-destination context over the initcode and
   run it, letting Verifereum own constructor execution, code deposit
   (handle_create), failure, and rollback.

   The adapter's `accounts' argument must already reflect the live prelude
   (create_prelude_accounts), while `revert_accounts is the snapshot that a
   failed creation rolls back to — Verifereum's proceed_create captures its
   sub-context rollback record after the sender nonce bump and before the
   endowment is transferred, so a reverting constructor keeps only the nonce
   bump and gives the endowment back.  The adapter returns:
     - SOME (SOME code, accounts', tStorage', logs') on success, where code is
       the deposited runtime code (already installed in accounts');
     - SOME (NONE, revert_accounts, revert_tStorage, []) on EVM revert, i.e.
       the constructor's effects and logs are discarded;
     - NONE for EVM exceptions (caller decides how to approximate). *)

(* Verifereum's proceed_create account prelude: bump the sender nonce, transfer
   the endowment, bump the (fresh) target nonce.  The target account is not
   reset -- Verifereum only rewrites `original`, the sub-context snapshot used
   for SSTORE gas and SELFDESTRUCT, so a pre-existing balance at that address
   survives and simply receives the endowment. *)
Definition create_prelude_accounts_def:
  create_prelude_accounts sender address value accounts =
    let accounts0 = vfmExecution$increment_nonce sender accounts in
      (vfmExecution$transfer_value sender address value o
       vfmExecution$increment_nonce address) accounts0
End

val () = cv_auto_trans create_prelude_accounts_def;

(* The account map a failed creation rolls back to: Verifereum's proceed_create
   captures its sub-context rollback record immediately after the sender nonce
   bump, so this is the pre-endowment state. *)
Definition create_rollback_accounts_def:
  create_rollback_accounts sender accounts =
    vfmExecution$increment_nonce sender accounts
End

val () = cv_auto_trans create_rollback_accounts_def;

(* Mirror of make_ext_call_state for creation: build the single-context
   execution state whose message runs the initcode with a Code destination. *)
Definition make_create_state_def:
  make_create_state sender address initcode value
                    accounts tStorage txParams =
    let gas_limit = default_evm_gas_limit in
    let tx = make_evm_tx sender address value [] gas_limit in
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
   deposited runtime code (the initcode's RETURN data) together with the
   post-constructor accounts and the logs it emitted; revert yields the
   rollback snapshot with no code and no logs. *)
Definition extract_create_result_def:
  extract_create_result revert_accounts revert_tStorage
    (result : unit + vfmExecution$exception option, final_state) =
    case final_state.contexts of
    | [(ctxt, _)] =>
        (case result of
         | INR NONE =>
             SOME (SOME ctxt.returnData,
                   final_state.rollback.accounts,
                   final_state.rollback.tStorage, ctxt.logs)
         | INR (SOME Reverted) =>
             SOME (NONE, revert_accounts, revert_tStorage, [])
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
        then extract_create_result (create_rollback_accounts sender accounts)
                                 tStorage outcome
        else NONE
    | NONE => NONE
End

val () = cv_auto_trans run_create_evm_def;

(* Shared by the recursive interpreter and the CPS machine.  All operands have
   already been evaluated before this helper is entered.  Vyper-specific
   pre-creation checks (operand shape, source availability, balance, nonce,
   initcode size, address collision) stay at this builtin boundary; the
   creation itself is executed by Verifereum via run_create_evm, including
   constructor effects, code deposit, and revert rollback.

   revert_on_failure: every failure mode -- bad operands/source, insufficient
   balance, collision, EVM exception, and a constructor that reverts -- reverts
   the Vyper frame when rof holds, and yields the zero address when rof = F.
   The last case is what Vyper's `check_create_operation` does: the EVM pushes
   0 for a failed CREATE/CREATE2, and the builtin turns that 0 into a revert
   unless revert_on_failure is False.  (Revert-data bubbling is still
   approximated by a generic RuntimeError; see TODO(#379).) *)
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
        (* the prelude adds to, rather than replaces, any balance already at
           the target address *)
        check (existing.balance + ops.co_value < 2 ** 256)
          "create recipient balance overflow";
        tStorage <- get_transient_storage;
        update_accounts
          (create_prelude_accounts cx.txn.target new_addr ops.co_value);
        post <- get_accounts;
        case run_create_evm cx.txn.target new_addr code_info.cc_initcode
               ops.co_value post tStorage
               (vyper_to_tx_params cx.txn) of
        | NONE => create_soft_failure rof "create failed"
        | SOME (code_opt, accounts', tStorage', logs') => do
            update_accounts (K accounts');
            update_transient (K tStorage');
            (* TODO(#379): the constructor's logs are dropped here.  Appending
               them is the right semantics (cf. the external-call boundary's
               `append_logs emitted_logs`), but see the issue for why this is
               still outstanding. *)
            case code_opt of
            | SOME _ => return (Value (AddressV new_addr))
            | NONE => create_soft_failure rof "create failed"
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

(* The adapter-result chain leaves a combined record update, which the
   per-field accfupds theorems do not directly simplify. *)
Theorem evaluation_state_accounts_tStorage_acc:
  (s with <| accounts := a; tStorage := t |>).scopes = s.scopes /\
  (s with <| accounts := a; tStorage := t |>).immutables = s.immutables /\
  (s with <| accounts := a; tStorage := t |>).logs = s.logs /\
  (s with <| accounts := a; tStorage := t |>).accounts = a /\
  (s with <| accounts := a; tStorage := t |>).tStorage = t
Proof
  Cases_on `s` >> simp[evaluation_state_accfupds]
QED

(* KEY LEMMA: the EVM-backed tail of eval_create only updates accounts,
   transient storage, and logs — never scopes or immutables.  Stated with
   the accessor monads already unfolded, so that it matches eval_create's body
   directly. *)
Theorem create_tail_preserves_scopes:
  (case run_create_evm a b c d e f g of
   | NONE => create_soft_failure rof "create failed"
   | SOME (code_opt, accounts', tStorage', logs') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          case code_opt of
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => create_soft_failure rof "create failed"
       od) s = (res, st') ==>
  st'.scopes = s.scopes /\ st'.immutables = s.immutables
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e f g` >|
   [(* adapter returned NONE: soft failure, state untouched *)
    (Cases_on `rof` >>
     gvs[create_soft_failure_def, update_accounts_def, update_transient_def,
         append_logs_def, return_def, raise_def, AllCaseEqs(),
         evaluation_state_accfupds]),
    (* adapter returned SOME: install accounts, transient storage and logs *)
    (PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
     gvs[bind_apply, ignore_bind_apply, update_accounts_def,
         update_transient_def, create_soft_failure_def,
         return_def, raise_def, AllCaseEqs()] >>
     strip_tac >>
     qpat_x_assum `Y = st'` (fn tm => ONCE_ASM_REWRITE_TAC[GSYM tm]) >>
     simp[evaluation_state_accounts_tStorage_acc])]
QED

(* KEY LEMMA: the EVM-backed tail leaves the log list untouched.  The adapter
   reports the constructor's logs in logs', but eval_create does not yet install
   them; see the TODO(#379) at the append_logs site in eval_create. *)
Theorem create_tail_preserves_logs:
  (case run_create_evm a b c d e1 g txp of
   | NONE => create_soft_failure rof "create failed"
   | SOME (code_opt, accounts', tStorage', logs') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          case code_opt of
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => create_soft_failure rof "create failed"
       od) s = (res, st') ==>
  st'.logs = s.logs
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp` >|
   [(* adapter NONE: the soft failure appends nothing *)
    (Cases_on `rof` >>
     gvs[create_soft_failure_def, return_def, raise_def] >>
     simp[evaluation_state_accfupds]),
    (* adapter SOME: only accounts and transient storage are installed *)
    (PairCases_on `x` >> Cases_on `rof` >>
     gvs[bind_apply, ignore_bind_apply, create_soft_failure_def,
         return_def, raise_def, AllCaseEqs()] >>
     rpt strip_tac >>
     gvs[update_accounts_def, update_transient_def] >>
     Cases_on `x0` >> gvs[create_soft_failure_def, return_def, raise_def] >>
     strip_tac >>
     qpat_x_assum `Y = st'` (fn tm => ONCE_ASM_REWRITE_TAC[GSYM tm]) >>
     simp[evaluation_state_accfupds])]
QED

(* Every raise on the EVM-backed tail raises an Error; the remaining outcomes
   all come from return. *)
Theorem create_tail_exception_is_error:
  (case run_create_evm a b c d e1 g txp of
   | NONE => create_soft_failure rof "create failed"
   | SOME (code_opt, accounts', tStorage', logs') =>
       do update_accounts (K accounts');
          update_transient (K tStorage');
          case code_opt of
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => create_soft_failure rof "create failed"
       od) s = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp`
  >- (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]) >>
  PairCases_on `x` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `x0` >> gvs[create_soft_failure_def, return_def, raise_def]
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
  (* The pre-creation checks touch only accounts, so they append nothing; the
     EVM-backed tail is handed to create_tail_log_extends. *)
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
         get_accounts_def, update_accounts_def, return_def,
         raise_def, AllCaseEqs()] >>
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
       get_accounts_def, return_def, evaluation_state_accfupds,
       AllCaseEqs()] >>
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
  gvs[create_soft_failure_def] >> gvs[raise_def, return_def]
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
          | SOME _ => return (Value (AddressV new_addr))
          | NONE => create_soft_failure rof "create failed"
       od) s = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >>
  qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _`
    (fn tm => mp_tac tm) >>
  Cases_on `run_create_evm a b c d e1 g txp`
  >- (gs[] >> metis_tac[create_soft_failure_no_type_error]) >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
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
  (* Only the EVM-backed tail can produce an exception: the pre-creation
     checks raise via create_soft_failure or assert, and both are covered by
     their own lemmas.  create_soft_failure is left unfolded in the tail so
     that the tail still matches create_tail_exception_is_error. *)
  gvs[eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
      get_accounts_def, get_transient_storage_def, update_accounts_def,
      check_def, assert_def, return_def, raise_def, AllCaseEqs(),
      COND_RATOR] >|
  [(* insufficient balance or nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* insufficient balance or nonce limit: soft failure *)
   (Cases_on `rof` >> gvs[create_soft_failure_def, return_def, raise_def]),
   (* address collision: nonce bump, then soft failure *)
   (Cases_on `rof` >>
    gvs[ignore_bind_apply, update_accounts_def, create_soft_failure_def,
        return_def, raise_def]),
   (* the EVM-backed tail *)
   (qpat_x_assum `(case run_create_evm _ _ _ _ _ _ _ of _ => _) _ = (INR ex, st')`
      (fn tm => mp_tac tm) >>
    metis_tac[create_tail_exception_is_error])]
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
      update_transient_def, check_def, assert_def,
      return_def, raise_def, AllCaseEqs(), COND_RATOR] >>
  gvs[COND_RATOR] >>
  (* AllCaseEqs has normalised the body into a disjunction whose only
     exceptional results are RuntimeErrors: every disjunct is either a
     create_soft_failure or the EVM-backed tail.  Each is closed by its own
     shape lemma, so no metis search over the full goal is needed. *)
  strip_tac >>
  rpt (FIRST [metis_tac[create_soft_failure_no_type_error],
              metis_tac[create_tail_no_type_error],
              gvs[]])
QED
