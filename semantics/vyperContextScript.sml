Theory vyperContext
Ancestors
  arithmetic alist combin option list finite_map pair rich_list
  cv cv_std vfmState vfmCompute[ignore_grammar] sha2
  vyperAST vyperABI vyperMisc vyperValue vyperValueOperation vyperStorage
Libs
  cv_transLib wordsLib

(* Environment and context for a contract call *)

(* external environment (tx, msg, block) *)
Datatype:
  call_txn = <|
    sender: address
  ; target: address
  ; function_name: identifier
  ; args: value list
  ; value: num
  ; time_stamp: num
  ; block_number: num
  ; block_hashes: bytes32 list
  ; blob_hashes: bytes32 list
  ; blob_base_fee: num
  ; gas_price: num
  ; chain_id: num
  ; is_creation: bool
  (* Block context fields *)
  ; coinbase: address
  ; gas_limit: num
  ; base_fee: num
  ; prev_randao: num
  (* Transaction origin *)
  ; origin: address
  |>
End

Definition empty_call_txn_def:
  empty_call_txn = <|
    sender := 0w;
    target := 0w;
    function_name := "";
    args := [];
    value := 0;
    time_stamp := 0;
    block_number := 0;
    block_hashes := [];
    blob_hashes := [];
    blob_base_fee := 0;
    gas_price := 0;
    chain_id := 0;
    is_creation := F;
    coinbase := 0w;
    gas_limit := 0;
    base_fee := 0;
    prev_randao := 0;
    origin := 0w
  |>
End

(* Vyper-internal environment *)
(* sources maps address to module map, where NONE is the main contract and SOME n is module with source_id=n *)
Datatype:
  evaluation_context = <|
    stk: (num option # identifier) list
  ; txn: call_txn
  ; sources: (address, (num option, toplevel list) alist) alist
  ; layouts: (address, storage_layout # storage_layout) alist  (* (storage, transient) *)
  ; in_deploy: bool  (* T when executing during deployment, allows calling Deploy functions *)
  ; nonreentrant_slot: num option  (* SOME slot if contract has reentrancy lock in transient storage *)
  |>
End

Theorem with_stk_updated_by_id[simp]:
  (cx with stk updated_by (λx. x)) = cx
Proof
  rw[theorem"evaluation_context_component_equality"]
QED

Definition empty_evaluation_context_def:
  empty_evaluation_context = <|
    stk := []
  ; txn := empty_call_txn
  ; sources := []
  ; layouts := []
  ; in_deploy := F
  ; nonreentrant_slot := NONE
  |>
End

val () = cv_auto_trans empty_evaluation_context_def;

(* Current module source_id: top of call stack, or NONE for main module *)
Definition current_module_def:
  current_module cx = case cx.stk of [] => NONE | (src,_)::_ => src
End

val () = cv_auto_trans current_module_def;

(* Now we can define semantics for builtins that depend on the environment *)

Definition evaluate_account_op_def:
  evaluate_account_op Address bs _ = BytesV bs ∧
  evaluate_account_op Balance _ a = IntV &a.balance ∧
  evaluate_account_op Codehash _ a = BytesV (Keccak_256_w64 a.code) ∧
  evaluate_account_op Codesize _ a = IntV $ &LENGTH a.code ∧
  evaluate_account_op IsContract _ a = BoolV (a.code ≠ []) ∧
  evaluate_account_op Code _ a = BytesV a.code
End

val () = cv_auto_trans evaluate_account_op_def;

Definition evaluate_block_hash_def:
  evaluate_block_hash t n =
  let pbn = t.block_number - 1 in
  if t.block_number ≤ n ∨
     LENGTH t.block_hashes ≤ pbn - n
  then INR (RuntimeError "evaluate_block_hash")
  else INL $ BytesV
    (word_to_bytes_be (EL (pbn - n) t.block_hashes))
End

(* evaluate_block_hash returns RuntimeError since block availability is runtime *)

val evaluate_block_hash_pre_def = cv_auto_trans_pre "evaluate_block_hash_pre" evaluate_block_hash_def;

Theorem evaluate_block_hash_pre[cv_pre]:
  evaluate_block_hash_pre t n
Proof
  rw[evaluate_block_hash_pre_def]
QED

Definition evaluate_blob_hash_def:
  evaluate_blob_hash t n =
    BytesV $
      word_to_bytes_be $
        if n < LENGTH t.blob_hashes
        then EL n t.blob_hashes
        else 0w
End

val () = cv_auto_trans evaluate_blob_hash_def;

(* Get code for a specific module by source_id (NONE = main contract) *)
Definition get_module_code_def:
  get_module_code cx src_id_opt =
    case ALOOKUP cx.sources cx.txn.target of
      NONE => NONE
    | SOME mods => ALOOKUP mods src_id_opt
End

val () = cv_auto_trans get_module_code_def;

(* Get main contract code (source_id = NONE) *)
Definition get_self_code_def:
  get_self_code cx = get_module_code cx NONE
End

val () = cv_auto_trans get_self_code_def;

Definition type_env_def:
  type_env [] = FEMPTY ∧
  type_env (StructDecl id args :: ts) =
    type_env ts |+ (string_to_num id, StructArgs args) ∧
  type_env (FlagDecl id ls :: ts) =
    type_env ts |+ (string_to_num id, FlagArgs (LENGTH ls)) ∧
  type_env (InterfaceDecl id funcs :: ts) =
    type_env ts |+ (string_to_num id, InterfaceArgs funcs) ∧
  type_env (_ :: ts) = type_env ts
End

val () = cv_auto_trans type_env_def;

(* Build combined type_env from all modules for a contract.
   This is needed because a function in one module can return a type from another. *)
Definition type_env_all_modules_def:
  type_env_all_modules [] = FEMPTY ∧
  type_env_all_modules ((src_id, ts) :: rest) =
    FUNION (type_env ts) (type_env_all_modules rest)
End

val () = cv_auto_trans type_env_all_modules_def;

(* Combined type env for the current contract *)
Definition get_tenv_def:
  get_tenv cx =
    case ALOOKUP cx.sources cx.txn.target of
      SOME mods => type_env_all_modules mods
    | NONE => FEMPTY
End

val () = cv_auto_trans get_tenv_def;

(* Look up an interface by nsid (source_id, name) *)
Definition lookup_interface_def:
  lookup_interface cx (src_id_opt, iface_name) =
    case get_module_code cx src_id_opt of
    | NONE => NONE
    | SOME ts =>
        case FLOOKUP (type_env ts) (string_to_num iface_name) of
        | SOME (InterfaceArgs funcs) => SOME funcs
        | _ => NONE
End

val () = cv_auto_trans lookup_interface_def;

(* Look up a function signature within an interface *)
Definition lookup_interface_func_def:
  lookup_interface_func [] fn_name = NONE ∧
  lookup_interface_func ((name, args, ret_ty, mutability) :: rest) fn_name =
    if name = fn_name then SOME (args, ret_ty, mutability)
    else lookup_interface_func rest fn_name
End

val () = cv_auto_trans lookup_interface_func_def;

Definition evaluate_extract32_def:
  evaluate_extract32 bs n bt =
  if n < LENGTH bs then let
    bs = DROP n bs
  in case bt
     of BytesT (Fixed m) =>
          if m ≤ LENGTH bs then
            INL $ BytesV (TAKE m bs)
          else INR (RuntimeError "evaluate_extract32 bytesM")
      | UintT m =>
          evaluate_convert FEMPTY (BytesV (TAKE 32 bs)) (BaseT (UintT m))
      | IntT m =>
          evaluate_convert FEMPTY (BytesV (TAKE 32 bs)) (BaseT (IntT m))
      | AddressT =>
          if 32 ≤ LENGTH bs then
            if EVERY ($= 0w) (TAKE 12 bs) then
              INL $ BytesV (DROP 12 (TAKE 32 bs))
            else INR (RuntimeError "evaluate_extract32 address clamp")
          else INR (RuntimeError "evaluate_extract32 address")
      | _ => INR (TypeError "evaluate_extract32 type")
  else INR (RuntimeError "evaluate_extract32 start")
End

val () = cv_auto_trans evaluate_extract32_def;

Definition evaluate_type_builtin_def:
  evaluate_type_builtin cx Empty typ vs =
  (case evaluate_type (get_tenv cx) typ
   of SOME tv => INL $ default_value tv
    | NONE => INR (TypeError "Empty evaluate_type")) ∧
  evaluate_type_builtin cx MaxValue typ vs =
    evaluate_max_value typ ∧
  evaluate_type_builtin cx MinValue typ vs =
    evaluate_min_value typ ∧
  evaluate_type_builtin cx Convert typ [v] =
    evaluate_convert (get_tenv cx) v typ ∧
  evaluate_type_builtin cx Epsilon typ [] =
    (if typ = BaseT DecimalT then INL $ DecimalV 1
     else INR (TypeError "Epsilon: not decimal")) ∧
  evaluate_type_builtin cx Extract32 (BaseT bt) [BytesV bs; IntV i] =
    evaluate_extract32 bs (Num i) bt ∧
  evaluate_type_builtin cx (AbiDecode unwrap) typ [BytesV bs] =
    (let tenv = get_tenv cx in
     if unwrap ∧ needs_external_call_wrap typ then
       case evaluate_abi_decode tenv (TupleT [typ]) bs of
         INL (ArrayV (TupleV [v])) => INL v
       | INL _ => INR (RuntimeError "abi_decode conversion")
       | INR str => INR (RuntimeError str)
     else
       case evaluate_abi_decode tenv typ bs of
         INL v => INL v
       | INR str => INR (RuntimeError str)) ∧
  evaluate_type_builtin _ (AbiDecode _) _ _ =
    INR (TypeError "abi_decode args") ∧
  evaluate_type_builtin cx (AbiEncode ensure) typ vs =
    (let tenv = get_tenv cx in
     let unwrap = (¬ensure ∧ needs_external_call_wrap typ) in
     (case (if unwrap then
              (case (typ, vs) of
                 (TupleT [t], [v]) => evaluate_abi_encode tenv t v
               | _ => INR "abi_encode unwrap")
            else evaluate_abi_encode tenv typ (ArrayV (TupleV vs))) of
        INL v => INL v | INR str => INR (RuntimeError str))) ∧
  evaluate_type_builtin _ _ _ _ =
    INR (TypeError "evaluate_type_builtin")
End

val () = cv_auto_trans evaluate_type_builtin_def;

Definition ecrecover_arg_to_num_def:
(* Convert an ecrecover argument to a natural number.
   Accepts both IntV (uint) and BytesV (bytes32). *)
  ecrecover_arg_to_num (IntV i) = SOME (Num i) ∧
  ecrecover_arg_to_num (BytesV bs) =
    SOME (w2n (word_of_bytes_be (PAD_LEFT 0w 32 bs) : bytes32)) ∧
  ecrecover_arg_to_num _ = NONE
End

val () = cv_auto_trans ecrecover_arg_to_num_def;

Definition evaluate_ecrecover_def:
  evaluate_ecrecover [BytesV hash_bytes; v_arg; r_arg; s_arg] =
    (case (ecrecover_arg_to_num v_arg,
           ecrecover_arg_to_num r_arg,
           ecrecover_arg_to_num s_arg) of
       (SOME v, SOME r, SOME s) =>
         if LENGTH hash_bytes = 32
         then let hash:bytes32 = word_of_bytes_be hash_bytes
         in case vfmExecution$ecrecover hash v r s of
              NONE => INL $ AddressV 0w
            | SOME addr => INL $ AddressV addr
         else INR (TypeError "ECRecover type")
     | _ => INR (TypeError "ECRecover type")) ∧
  evaluate_ecrecover _ = INR (TypeError "ECRecover args")
End

val () = cv_auto_trans evaluate_ecrecover_def;

(* Extract (x, y) uint256 pair from a uint256[2] static array value. *)
Definition extract_ec_point_def:
  extract_ec_point (ArrayV av) =
    (let tv = ArrayTV (BaseTV (UintT 256)) (Fixed 2) in
     case (array_index tv av 0, array_index tv av 1) of
       (SOME (IntV x), SOME (IntV y)) => SOME (x, y)
     | _ => NONE) ∧
  extract_ec_point _ = NONE
End

val () = cv_auto_trans extract_ec_point_def;

Definition mk_ec_result_def:
  mk_ec_result (rx, ry) =
    ArrayV $ make_array_value (BaseTV (UintT 256)) (Fixed 2)
      [IntV (&rx); IntV (&ry)]
End

val () = cv_auto_trans mk_ec_result_def;

Definition evaluate_ecadd_def:
  evaluate_ecadd [p1v; p2v] =
    (case (extract_ec_point p1v, extract_ec_point p2v) of
       (SOME (x1, y1), SOME (x2, y2)) => (
         let p1 = (Num x1, Num y1);
             p2 = (Num x2, Num y2)
         in case vfmExecution$ecadd p1 p2 of
              NONE => INL $ mk_ec_result (0, 0)
            | SOME r => INL $ mk_ec_result r )
     | _ => INR (TypeError "ECAdd type")) ∧
  evaluate_ecadd _ = INR (TypeError "ECAdd args")
End

val () = cv_auto_trans evaluate_ecadd_def;

Definition evaluate_ecmul_def:
  evaluate_ecmul [pv; IntV scalar] =
    (case extract_ec_point pv of
       SOME (x, y) =>
         let
           p = (Num x, Num y);
           n = Num scalar
         in (case vfmExecution$ecmul p n of
               NONE => INL $ mk_ec_result (0, 0)
             | SOME r => INL $ mk_ec_result r)
     | NONE => INR (TypeError "ECMul type")) ∧
  evaluate_ecmul _ = INR (TypeError "ECMul args")
End

val () = cv_auto_trans evaluate_ecmul_def;

Definition evaluate_builtin_def:
  evaluate_builtin cx _ ty Not [BoolV b] = INL (BoolV (¬b)) ∧
  evaluate_builtin cx _ ty Not [IntV i] =
    (case type_to_int_bound ty of
       SOME u =>
         if is_Unsigned u ∧ 0 ≤ i then
           INL (IntV (&(2 ** int_bound_bits u) - 1 - i))
         else INR (TypeError "signed Not")
     | NONE => INR (TypeError "Not type")) ∧
  evaluate_builtin cx _ ty Not [FlagV n] =
    (case evaluate_type (get_tenv cx) ty of
       SOME (FlagTV m) => INL $ FlagV $
         w2n $ (~((n2w n):bytes32)) && ~(~(0w:bytes32) << m)
     | _ => INR (TypeError "Not flag type")) ∧
  evaluate_builtin cx _ ty Neg [IntV i] =
    (case type_to_int_bound ty
     of SOME u => bounded_int_op u (-i)
      | NONE => INR (TypeError "Neg type")) ∧
  evaluate_builtin cx _ _ Neg [DecimalV i] = bounded_decimal_op (-i) ∧
  evaluate_builtin cx _ _ Keccak256 [BytesV ls] = INL $ BytesV $
    Keccak_256_w64 ls ∧
  evaluate_builtin cx _ _ Keccak256 [StringV s] = INL $ BytesV $
    Keccak_256_w64 (MAP (n2w o ORD) s) ∧
  (* TODO: reject BytesV with invalid bounds for Keccak256 *)
  evaluate_builtin cx _ _ Sha256 [BytesV ls] = INL $ BytesV $
    word_to_bytes (SHA_256_bytes ls : bytes32) T ∧
  evaluate_builtin cx _ _ Sha256 [StringV s] = INL $ BytesV $
    word_to_bytes (SHA_256_bytes (MAP (n2w o ORD) s) : bytes32) T ∧
  evaluate_builtin cx _ _ (Uint2Str n) [IntV i] =
    INL $ StringV (num_to_dec_string (Num i)) ∧
  evaluate_builtin cx _ _ (AsWeiValue dn) [v] = evaluate_as_wei_value dn v ∧
  evaluate_builtin cx _ _ AddMod [IntV i1; IntV i2; IntV i3] =
    (if i3 = 0 then INR (RuntimeError "AddMod division by zero")
     else INL $ IntV $ &((Num i1 + Num i2) MOD Num i3)) ∧
  evaluate_builtin cx _ _ MulMod [IntV i1; IntV i2; IntV i3] =
    (if i3 = 0 then INR (RuntimeError "MulMod division by zero")
     else INL $ IntV $ &((Num i1 * Num i2) MOD Num i3)) ∧
  evaluate_builtin cx _ _ PowMod256 [IntV base; IntV exp] =
    INL $ IntV $ &(vfmExecution$modexp (Num base) (Num exp) (2 ** 256) 1) ∧
  evaluate_builtin cx _ _ Floor [DecimalV i] =
    INL $ IntV (i / 10000000000) ∧
  evaluate_builtin cx _ _ Ceil [DecimalV i] =
    INL $ IntV ((i + 9999999999) / 10000000000) ∧
  evaluate_builtin cx _ ty (Bop bop) [v1; v2] =
    (let u = case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0 in
     let tv = case evaluate_type (get_tenv cx) ty of SOME tv => tv | NONE => NoneTV in
       evaluate_binop u tv bop v1 v2) ∧
  evaluate_builtin cx _ _ (Env Sender) [] = INL $ AddressV cx.txn.sender ∧
  evaluate_builtin cx _ _ (Env SelfAddr) [] = INL $ AddressV cx.txn.target ∧
  evaluate_builtin cx _ _ (Env ValueSent) [] = INL $ IntV &cx.txn.value ∧
  evaluate_builtin cx _ _ (Env TimeStamp) [] = INL $ IntV &cx.txn.time_stamp ∧
  evaluate_builtin cx _ _ (Env BlockNumber) [] = INL $ IntV &cx.txn.block_number ∧
  evaluate_builtin cx _ _ (Env BlobBaseFee) [] = INL $ IntV &cx.txn.blob_base_fee ∧
  evaluate_builtin cx _ _ (Env GasPrice) [] = INL $ IntV &cx.txn.gas_price ∧
  evaluate_builtin cx _ _ (Env ChainId) [] = INL $ IntV &cx.txn.chain_id ∧
  evaluate_builtin cx _ _ (Env Coinbase) [] = INL $ AddressV cx.txn.coinbase ∧
  evaluate_builtin cx _ _ (Env GasLimit) [] = INL $ IntV &cx.txn.gas_limit ∧
  evaluate_builtin cx _ _ (Env BaseFee) [] = INL $ IntV &cx.txn.base_fee ∧
  evaluate_builtin cx _ _ (Env PrevRandao) [] = INL $ IntV &cx.txn.prev_randao ∧
  evaluate_builtin cx _ _ (Env TxOrigin) [] = INL $ AddressV cx.txn.origin ∧
  evaluate_builtin cx _ _ (Env PrevHash) [] = evaluate_block_hash cx.txn (cx.txn.block_number - 1) ∧
  evaluate_builtin cx _ _ BlockHash [IntV i] =
    evaluate_block_hash cx.txn (Num i) ∧
  evaluate_builtin cx _ _ BlobHash [IntV i] =
    INL $ evaluate_blob_hash cx.txn (Num i) ∧
  evaluate_builtin cx _ _ (Concat n) vs = evaluate_concat n vs ∧
  evaluate_builtin cx _ _ (Slice n) [v1; v2; v3] = evaluate_slice v1 v2 v3 n ∧
  evaluate_builtin cx _ _ (MakeArray to bd) vs =
    (case to
     of NONE => INL $ ArrayV $ TupleV vs
      | SOME t =>
        (case evaluate_type (get_tenv cx) t
         of NONE => INR (TypeError "MakeArray type")
          | SOME tv => INL $ ArrayV $ make_array_value tv bd vs)) ∧
  evaluate_builtin cx acc _ (Acc aop) [BytesV bs] =
    (let a = lookup_account (word_of_bytes_be bs) acc in
      INL $ evaluate_account_op aop bs a) ∧
  evaluate_builtin cx _ _ Isqrt [IntV i] =
    (if 0 ≤ i then INL $ IntV &(num_sqrt (Num i))
     else INR (TypeError "Isqrt type")) ∧
  (* method_id: compute keccak256(signature)[:4] - returns 4-byte function selector *)
  evaluate_builtin cx _ _ MethodId [StringV sig] =
    INL $ BytesV (TAKE 4 (Keccak_256_w64 (MAP (n2w o ORD) sig))) ∧
  (* Also support Bytes input for method_id *)
  evaluate_builtin cx _ _ MethodId [BytesV bs] =
    INL $ BytesV (TAKE 4 (Keccak_256_w64 bs)) ∧
  evaluate_builtin cx _ _ ECRecover vs = evaluate_ecrecover vs ∧
  evaluate_builtin cx _ _ ECAdd vs = evaluate_ecadd vs ∧
  evaluate_builtin cx _ _ ECMul vs = evaluate_ecmul vs ∧
  evaluate_builtin _ _ _ _ _ = INR (TypeError "builtin")
End

val evaluate_builtin_pre_def = cv_auto_trans_pre "evaluate_builtin_pre" evaluate_builtin_def;

Theorem evaluate_builtin_pre[cv_pre]:
  evaluate_builtin_pre a b c d e
Proof
  rw[evaluate_builtin_pre_def]
QED

Definition type_builtin_args_length_ok_def:
  type_builtin_args_length_ok Empty n = (n = 0n) ∧
  type_builtin_args_length_ok MaxValue n = (n = 0) ∧
  type_builtin_args_length_ok MinValue n = (n = 0) ∧
  type_builtin_args_length_ok Epsilon n = (n = 0) ∧
  type_builtin_args_length_ok Extract32 n = (n = 2) ∧
  type_builtin_args_length_ok Convert n = (n = 1) ∧
  type_builtin_args_length_ok (AbiDecode _) n = (n = 1) ∧
  type_builtin_args_length_ok (AbiEncode _) n = (n >= 1)
End

val () = cv_auto_trans type_builtin_args_length_ok_def;

Definition builtin_args_length_ok_def:
  builtin_args_length_ok Len n = (n = 1n) ∧
  builtin_args_length_ok Not n = (n = 1) ∧
  builtin_args_length_ok Neg n = (n = 1) ∧
  builtin_args_length_ok Abs n = (n = 1) ∧
  builtin_args_length_ok Keccak256 n = (n = 1) ∧
  builtin_args_length_ok Sha256 n = (n = 1) ∧
  builtin_args_length_ok (Uint2Str _) n = (n = 1) ∧
  builtin_args_length_ok (AsWeiValue _) n = (n = 1) ∧
  builtin_args_length_ok (Concat _) n = (2 ≤ n) ∧
  builtin_args_length_ok (Slice _) n = (n = 3) ∧
  builtin_args_length_ok (MakeArray _ b) n = compatible_bound b n ∧
  builtin_args_length_ok Floor n = (n = 1) ∧
  builtin_args_length_ok Ceil n = (n = 1) ∧
  builtin_args_length_ok AddMod n = (n = 3) ∧
  builtin_args_length_ok MulMod n = (n = 3) ∧
  builtin_args_length_ok (Bop _) n = (n = 2) ∧
  builtin_args_length_ok (Env _) n = (n = 0) ∧
  builtin_args_length_ok BlockHash n = (n = 1) ∧
  builtin_args_length_ok BlobHash n = (n = 1) ∧
  builtin_args_length_ok (Acc _) n = (n = 1) ∧
  builtin_args_length_ok Isqrt n = (n = 1) ∧
  builtin_args_length_ok MethodId n = (n = 1) ∧
  builtin_args_length_ok ECRecover n = (n = 4) ∧
  builtin_args_length_ok ECAdd n = (n = 2) ∧
  builtin_args_length_ok ECMul n = (n = 2) ∧
  builtin_args_length_ok PowMod256 n = (n = 2)
End

val () = cv_auto_trans builtin_args_length_ok_def;
