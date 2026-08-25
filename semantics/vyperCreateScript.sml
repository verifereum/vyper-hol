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
  contractABI vfmConstants vfmState vfmContext
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

(* Shared by the recursive interpreter and the CPS machine.  All operands have
   already been evaluated before this helper is entered. *)
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
        update_accounts (proceed_create_accounts cx.txn.target new_addr
          ops.co_value code_info.cc_runtime_code);
        return (Value (AddressV new_addr))
      od
    od
  od
End

val () = eval_create_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, lift_option_type_def,
            option_CASE_rator, LET_RATOR, COND_RATOR, check_def, assert_def]
  |> cv_auto_trans;

Theorem eval_create_preserves_non_accounts:
  eval_create cx kind has_salt rof arg_tys vs st = (res, st') ==>
  st'.scopes = st.scopes /\ st'.immutables = st.immutables /\
  st'.logs = st.logs /\ st'.tStorage = st.tStorage
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
      get_accounts_def, update_accounts_def, check_def, assert_def,
      create_soft_failure_def, return_def, raise_def, AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt (IF_CASES_TAC >>
       gvs[bind_def, update_accounts_def, return_def, raise_def, assert_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem eval_create_preserves_storage:
  eval_create cx kind has_salt rof arg_tys vs st = (res, st') ==>
  (lookup_account address st'.accounts).storage =
  (lookup_account address st.accounts).storage
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
      get_accounts_def, update_accounts_def, check_def, assert_def,
      create_soft_failure_def, return_def, raise_def, AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt (IF_CASES_TAC >>
       gvs[bind_def, update_accounts_def, return_def, raise_def, assert_def]) >>
  rpt strip_tac >> gvs[]
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
  gvs[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
      get_accounts_def, update_accounts_def, check_def, assert_def,
      create_soft_failure_def, return_def, raise_def, AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt (IF_CASES_TAC >>
       gvs[bind_def, update_accounts_def, return_def, raise_def, assert_def])
QED
