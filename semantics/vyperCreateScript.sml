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
  contractABI sptree vfmTypes vfmConstants vfmState vfmContext
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

Definition blueprint_copy_size_def:
  blueprint_copy_size code_offset (code : byte list) =
    w2n ((n2w (LENGTH code) - n2w code_offset) : bytes32)
End

(* The size is captured before constructor operands; EXTCODECOPY reads later. *)
Definition blueprint_initcode_def:
  blueprint_initcode n code_offset (code : byte list) args_enc =
    take_pad_0 n (DROP code_offset code) ++ args_enc
End

Definition raw_create_initcode_def:
  raw_create_initcode bytecode args_enc = bytecode ++ args_enc
End

Definition blueprint_size_ok_def:
  blueprint_size_ok n = (0i < w2i (n2w n : bytes32))
End

Definition blueprint_code_ok_def:
  blueprint_code_ok code_offset code =
    blueprint_size_ok (blueprint_copy_size code_offset code)
End

Definition blueprint_prefix_size_def:
  blueprint_prefix_size has_salt vs accounts =
    case dest_create_args (CreateFromBlueprint F) has_salt vs of
    | NONE => NONE
    | SOME ops =>
        case (ops.co_code_src, ops.co_code_offset) of
        | (AddressCodeSource target, SOME offset) =>
            let n = blueprint_copy_size offset
              (lookup_account target accounts).code in
            if blueprint_size_ok n then SOME n else NONE
        | _ => NONE
End

Definition check_create_blueprint_def:
  check_create_blueprint has_salt vs = do
    accounts <- get_accounts;
    lift_option (blueprint_prefix_size has_salt vs accounts)
      "create source has no deployable code"
  od
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
val () = cv_auto_trans blueprint_copy_size_def;
val () = cv_auto_trans blueprint_initcode_def;
val () = cv_auto_trans raw_create_initcode_def;
val () = cv_auto_trans blueprint_size_ok_def;
val () = cv_auto_trans blueprint_code_ok_def;
val () = cv_auto_trans blueprint_prefix_size_def;
val () = check_create_blueprint_def
  |> SRULE [FUN_EQ_THM, bind_def, get_accounts_def, return_def,
            lift_option_def, prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, COND_RATOR]
  |> cv_auto_trans;

Theorem check_create_blueprint_state[simp]:
  SND (check_create_blueprint has_salt vs st) = st
Proof
  simp[check_create_blueprint_def, bind_def, get_accounts_def,
       lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def]
QED

Theorem check_create_blueprint_result_state:
  check_create_blueprint has_salt vs st = (res, st') ==> st' = st
Proof
  metis_tac[check_create_blueprint_state, pairTheory.SND]
QED

Theorem check_create_blueprint_exception_is_error:
  check_create_blueprint has_salt vs st = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  simp[check_create_blueprint_def, bind_def, get_accounts_def,
       lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def]
QED

Theorem check_create_blueprint_no_type_error:
  check_create_blueprint has_salt vs st = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  simp[check_create_blueprint_def, bind_def, get_accounts_def,
       lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> rw[return_def, raise_def]
QED
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
  ; cc_size_ok: bool
  |>
End

Definition build_create_code_def:
  build_create_code tenv CreateMinimalProxy ops accounts ctor_tys blueprint_size =
    (case ops.co_code_src of
     | AddressCodeSource target => SOME <|
         cc_initcode := minimal_proxy_initcode target;
         cc_source_ok := T;
         cc_size_ok := T
       |>
     | _ => NONE) /\
  build_create_code tenv CreateCopyOf ops accounts ctor_tys blueprint_size =
    (case ops.co_code_src of
     | AddressCodeSource target =>
         let code = (lookup_account target accounts).code in
         SOME <| cc_initcode := create_copy_initcode code;
                 cc_source_ok := (code <> []);
                 cc_size_ok := T |>
     | _ => NONE) /\
  build_create_code tenv (CreateFromBlueprint raw_args) ops accounts ctor_tys blueprint_size =
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
            | SOME args_enc =>
                let n = case blueprint_size of
                        | NONE => blueprint_copy_size code_offset code
                        | SOME n => n in
                let size_ok = (n + LENGTH args_enc <= 2 * max_code_size) in
                SOME <|
                  cc_initcode := if size_ok then
                    blueprint_initcode n code_offset code args_enc else [];
                  cc_source_ok := blueprint_size_ok n;
                  cc_size_ok := size_ok
                |>)
     | _ => NONE) /\
  build_create_code tenv RawCreate ops accounts ctor_tys blueprint_size =
    (case ops.co_code_src of
     | BytecodeCodeSource bytecode =>
         (case encode_create_ctor_args tenv ctor_tys ops.co_ctor_args of
          | NONE => NONE
          | SOME args_enc => SOME <|
              cc_initcode := raw_create_initcode bytecode args_enc;
              cc_source_ok := T;
              cc_size_ok := T
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

   The adapter receives pre-creation accounts and builds the live prelude
   internally.  A failed constructor restores the pre-endowment snapshot
   after one creator nonce increment.  On success it returns deposited code,
   accounts, transient storage, emitted logs, and queued deletions; on REVERT
   it also returns the constructor's revert bytes.  Other EVM exceptions return NONE. *)

(* Verifereum's proceed_create account prelude: bump the sender nonce, transfer
   the endowment, bump the (fresh) target nonce.  The live target account is not
   reset: only the original-account snapshot used for SSTORE gas and
   SELFDESTRUCT is emptied, preserving any pre-existing balance plus endowment. *)
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
                    accounts tStorage pending txParams =
    let gas_limit = default_evm_gas_limit in
    let tx = make_evm_tx sender address value [] gas_limit in
    let ctxt = initial_context address initcode F (Code address) tx in
    let accesses = <| addresses := fINSERT sender (fINSERT address fEMPTY)
                    ; storageKeys := fEMPTY |> in
    let rollback = <| accounts := accounts
                    ; tStorage := tStorage
                    ; accesses := accesses
                    ; toDelete := pending |> in
    <| contexts := [(ctxt, rollback with accounts :=
                      update_account address empty_account_state accounts)]
     ; txParams := txParams
     ; rollback := rollback
     ; msdomain := Collect empty_domain
    |>
End

(* Extract creation results from Verifereum execution. Success yields the
   deposited runtime code, post-constructor state, emitted logs, and pending
   deletions; revert yields the rollback snapshot and its return data. *)
Definition extract_create_result_def:
  extract_create_result revert_accounts revert_tStorage pending
    (result : unit + vfmExecution$exception option, final_state) =
    case final_state.contexts of
    | [(ctxt, _)] =>
        (case result of
         | INR NONE =>
             SOME (SOME ctxt.returnData,
                   final_state.rollback.accounts,
                   final_state.rollback.tStorage, ctxt.logs, [],
                   final_state.rollback.toDelete)
         | INR (SOME Reverted) =>
             SOME (NONE, revert_accounts, revert_tStorage, [], ctxt.returnData,
                   pending)
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

(* Run initcode with the EVM prelude, retaining the pre-endowment account map
   so failed creation restores everything except the creator nonce bump. *)
Definition run_create_evm_def:
  run_create_evm sender address initcode value accounts tStorage pending txParams =
    let post = create_prelude_accounts sender address value accounts in
    case vfmExecution$run_call
           (make_create_state sender address initcode value
              post tStorage pending txParams) of
    | SOME outcome =>
        if create_accounts_ok_aux (FST outcome) (SND outcome).rollback.accounts
        then extract_create_result (create_rollback_accounts sender accounts)
                                 tStorage pending outcome
        else NONE
    | NONE => NONE
End

val () = cv_auto_trans run_create_evm_def;

(* Shared execution boundary after operand evaluation. Blueprint callers pass
   the copy size captured by check_create_blueprint before constructor operands;
   direct callers use NONE to derive it from the supplied account state.
   Source/size ASSERTs always revert, independently of revert_on_failure.
   CREATE failure returns zero when rof = F; constructor REVERT data bubbles
   as RevertData when rof holds. *)
Definition eval_create_def:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size = do
    ops <- lift_option_type (dest_create_args kind has_salt vs)
      "create operand shape";
    ctor_tys <- lift_option_type (create_arg_ctor_types kind has_salt arg_tys)
      "create argument type shape";
    accounts <- get_accounts;
    code_info <- lift_option_type
      (build_create_code (get_tenv cx) kind ops accounts ctor_tys blueprint_size)
      "create operands";
    (* copy-of/blueprint ASSERTs are emitted before CREATE and always revert. *)
    check code_info.cc_source_ok "create source has no deployable code";
    check code_info.cc_size_ok "create initcode too large";
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
        pending <- get_pending_deletions;
        update_accounts
          (create_prelude_accounts cx.txn.target new_addr ops.co_value);
        case run_create_evm cx.txn.target new_addr code_info.cc_initcode
               ops.co_value accounts tStorage pending
               (vyper_to_tx_params cx.txn) of
        | NONE => do
            update_accounts (K (create_rollback_accounts cx.txn.target accounts));
            create_soft_failure rof "create failed"
          od
        | SOME (code_opt, accounts', tStorage', logs', revertData, pending') => do
            update_accounts (K accounts');
            update_transient (K tStorage');
            update_pending_deletions (K pending');
            case code_opt of
            | SOME _ => do
                append_logs logs';
                return (Value (AddressV new_addr))
              od
            | NONE => if rof then raise (Error (RevertData revertData))
                      else return (Value (AddressV 0w))
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
   and return code, accounts, transient storage, logs, revert data, and
   pending deletions. *)
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
   transient storage, pending deletions, and logs — never scopes or immutables.
   Stated with the accessor monads already unfolded, so it matches eval_create's body
   directly. *)
Theorem create_tail_preserves_scopes:
  (case run_create_evm a b c d e f h g of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (res, st') ==>
  st'.scopes = s.scopes /\ st'.immutables = s.immutables
Proof
  Cases_on `run_create_evm a b c d e f h g`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[evaluation_state_accfupds]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs(), evaluation_state_accfupds] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[evaluation_state_accounts_tStorage_acc,
                       evaluation_state_accfupds]
QED

(* Every creation path leaves the old log sequence as a prefix. *)
Theorem create_tail_log_extends:
  (case run_create_evm a b c d e1 g h txp of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e1));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (res, st') ==>
  isPREFIX s.logs st'.logs
Proof
  Cases_on `run_create_evm a b c d e1 g h txp`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >>
      gvs[evaluation_state_accfupds, rich_listTheory.IS_PREFIX_REFL]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs(), evaluation_state_accfupds,
      rich_listTheory.IS_PREFIX_REFL, rich_listTheory.IS_PREFIX_APPEND] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[evaluation_state_accounts_tStorage_acc, evaluation_state_accfupds,
      rich_listTheory.IS_PREFIX_REFL, rich_listTheory.IS_PREFIX_APPEND]
QED

(* Every raise on the EVM-backed tail raises an Error; the remaining outcomes
   all come from return. *)
Theorem create_tail_exception_is_error:
  (case run_create_evm a b c d e1 g h txp of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e1));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  Cases_on `run_create_evm a b c d e1 g h txp`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* Reduce only the executed monadic head. In particular, never simplify a
   continuation or the context containing the guarded operand equations. *)
local
  val head_rules = map (REWR_CONV o CONV_RULE (DEPTH_CONV ETA_CONV))
    (List.concat (map (CONJUNCTS o SPEC_ALL)
    [eval_create_def, bind_apply, ignore_bind_apply, lift_option_type_def,
     get_accounts_def, check_def, assert_def, return_def, raise_def,
     update_accounts_def, get_transient_storage_def,
     get_pending_deletions_def, create_soft_failure_def,
     pairTheory.pair_case_thm, sumTheory.sum_case_def,
     optionTheory.option_case_def, LET_THM, COND_RATOR, COND_CLAUSES]));
  val guard_ss = bool_ss;
  val frame_ss = bool_ss ++ rewrites [evaluation_state_accfupds];
  val log_ss = frame_ss ++ rewrites [rich_listTheory.IS_PREFIX_REFL];
  val error_ss = bool_ss ++ rewrites
    [sumTheory.INR_11, sumTheory.sum_distinct, exception_11,
     vyperValueOperationTheory.error_distinct];

  fun create_head_conv facts tm =
    let
      fun equation th =
        if is_eq (concl th) then th
        else if is_neg (concl th) then EQF_INTRO th else EQT_INTRO th;
      val root = FIRST_CONV
        (BETA_CONV :: map (REWR_CONV o equation) facts @ head_rules);
      fun step tm =
        (CHANGED_CONV root ORELSEC
         (fn tm =>
           let val (h,args) = strip_comb tm in
             if is_const h andalso
                ((fst (dest_const h) = "pair_CASE" andalso length args = 2) orelse
                 (mem (fst (dest_const h)) ["sum_CASE", "option_CASE"] andalso
                  length args = 3))
             then funpow (length args - 1) RATOR_CONV
                    (RAND_CONV (CHANGED_CONV (create_head_conv facts))) tm
             else if is_cond tm then
               RATOR_CONV (RATOR_CONV
                 (RAND_CONV (CHANGED_CONV (SIMP_CONV guard_ss facts)))) tm
             else RATOR_CONV (CHANGED_CONV (create_head_conv facts)) tm
           end)) tm;
    in REPEATC step tm end;

  fun create_guard tm =
    if is_cond tm then #1 (dest_cond tm)
    else
      let val (h,args) = strip_comb tm in
        if is_const h andalso
           ((fst (dest_const h) = "pair_CASE" andalso length args = 2) orelse
            (mem (fst (dest_const h)) ["sum_CASE", "option_CASE"] andalso
             length args = 3))
        then create_guard (hd args)
        else create_guard (rator tm)
      end;

  fun create_paths tail finish (asl,w) =
    let
      val cv = create_head_conv (map ASSUME asl);
      val tm = lhs (fst (dest_imp w));
      val th = cv tm;
      val next = rhs (concl th);
      val reduce = CONV_TAC (LAND_CONV (LAND_CONV (K th)));
    in
      (reduce >>
       (case total create_guard next of
          SOME guard => ASM_CASES_TAC guard >> create_paths tail finish
        | NONE =>
            DISCH_THEN (fn result =>
              if pairSyntax.is_pair next then finish (SOME result)
              else mp_tac (MATCH_MP tail result) >> finish NONE))) (asl,w)
    end;

  (* Only substitute the final-state equation in the goal; leave the
     guarded decode and check facts untouched. A tail lemma already supplies
     the conclusion, so only its accessor updates need simplifying. *)
  fun create_state_finish ss result =
    (case result of
       NONE => ALL_TAC
     | SOME result =>
         let
           val snd = rator (pairSyntax.mk_snd (lhs (concl result)));
           val state = REWRITE_RULE [pairTheory.SND] (AP_TERM snd result);
         in SUBST1_TAC (SYM state) end) >> simp_tac ss [];

  (* Outcome properties need only the result projection, not the state or
     any decode/check assumptions. *)
  fun create_error_finish result =
    (case result of
       NONE => ALL_TAC
     | SOME result =>
         let
           val fst = rator (pairSyntax.mk_fst (lhs (concl result)));
           val outcome = SIMP_RULE error_ss []
             (REWRITE_RULE [pairTheory.FST] (AP_TERM fst result));
         in
           if aconv (concl outcome) F then CONTR_TAC outcome
           else SUBST1_TAC (SYM outcome)
         end) >> simp_tac error_ss [];

in
  fun create_result_tac tail finish =
    qpat_x_assum `eval_create _ _ _ _ _ _ _ _ = _` mp_tac >>
    create_paths (REWRITE_RULE [GSYM ignore_bind_def] tail) finish;
  val create_frame_tac =
    create_result_tac create_tail_preserves_scopes (create_state_finish frame_ss);
  val create_logs_tac =
    create_result_tac create_tail_log_extends (create_state_finish log_ss);
  fun create_outcome_tac tail = create_result_tac tail create_error_finish;
  val create_exception_tac = create_outcome_tac create_tail_exception_is_error;
end;

(* Constructor events extend, rather than preserve, the log sequence. *)
Theorem eval_create_logs_extend:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  isPREFIX st.logs st'.logs
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- create_logs_tac >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- create_logs_tac >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  create_logs_tac
QED

Theorem eval_create_preserves_scopes_immutables:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- create_frame_tac >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- create_frame_tac >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  create_frame_tac
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
   succeeded, every remaining failure in eval_create is an Error raised
   by check/assert or the EVM-backed tail, which performs no typing checks.

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
   typing checks: every outcome is an address or a non-TypeError Error. *)
Theorem create_tail_no_type_error:
  (case run_create_evm a b c d e1 g h txp of
   | NONE => do
       x <- update_accounts (K (create_rollback_accounts a e1));
       create_soft_failure rof "create failed"
     od
   | SOME (code_opt, accounts', tStorage', logs', revertData, pending') =>
       do x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          x <- update_pending_deletions (K pending');
          case code_opt of
          | SOME _ => do x <- append_logs logs'; return (Value (AddressV new_addr)) od
          | NONE => if rof then raise (Error (RevertData revertData))
                    else return (Value (AddressV 0w))
       od) s = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  Cases_on `run_create_evm a b c d e1 g h txp`
  >- (Cases_on `rof` >>
      gvs[bind_apply, ignore_bind_apply, update_accounts_def,
          create_soft_failure_def, return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  PairCases_on `x` >> Cases_on `x0` >> Cases_on `rof` >>
  gvs[bind_apply, ignore_bind_apply, update_accounts_def,
      update_transient_def, update_pending_deletions_def, append_logs_def, create_soft_failure_def,
      return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_create_exception_is_error:
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (INR ex, st') ==>
  ?err. ex = Error err
Proof
  strip_tac >>
  Cases_on `dest_create_args kind has_salt vs`
  >- create_exception_tac >>
  rename1 `dest_create_args kind has_salt vs = SOME ops` >>
  Cases_on `create_arg_ctor_types kind has_salt arg_tys`
  >- create_exception_tac >>
  rename1 `create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys` >>
  Cases_on `build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size` >>
  create_exception_tac
QED

Theorem eval_create_no_type_error:
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys /\
  build_create_code (get_tenv cx) kind ops st.accounts ctor_tys blueprint_size =
    SOME code_info /\
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res, st') ==>
  !msg. res <> INR (Error (TypeError msg))
Proof
  strip_tac >> create_outcome_tac create_tail_no_type_error
QED
