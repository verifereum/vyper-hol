Theory vyperInterpreter
Ancestors
  arithmetic alist combin option list finite_map integer[qualified] pair
  rich_list cv cv_std vfmState vfmContext vfmCompute[ignore_grammar]
  vfmExecution[ignore_grammar] vyperAST vyperABI
  vyperMisc vyperValue vyperValueOperation vyperStorage
Libs
  cv_transLib wordsLib monadsyntax intSimps[qualified]

(* `subscript`s are the possible kinds of keys into HashMaps *)

Datatype:
  subscript
  = IntSubscript int
  | StrSubscript string
  | BytesSubscript (word8 list)
  | AttrSubscript identifier
End

(* since HashMaps and storage arrays can only appear at the top level, they are
* not mutually recursive with other `value`s, and we have `toplevel_value`: *)
(* HashMapRef stores a base slot, key type, and value_type for lazy storage access.
   When subscripted:
   - If value_type is HashMapT kt vt, returns HashMapRef with new slot and kt
   - If value_type is Type t, reads from storage at the computed slot
   ArrayRef stores a base slot, element type_value, and bound for lazy storage
   access. When subscripted, computes the element slot offset instead of
   materializing the entire array. *)

Datatype:
  toplevel_value = Value value
                 | HashMapRef bool bytes32 type value_type
                 | ArrayRef bool bytes32 type_value bound
End

Theorem toplevel_value_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperInterpreter",Tyop="toplevel_value"}));

Definition is_Value_def[simp]:
  (is_Value (Value _) ⇔ T) ∧
  (is_Value _ ⇔ F)
End

val () = cv_auto_trans is_Value_def;

Definition is_HashMapRef_def[simp]:
  (is_HashMapRef (HashMapRef _ _ _ _) ⇔ T) ∧
  (is_HashMapRef _ ⇔ F)
End

val () = cv_auto_trans is_HashMapRef_def;

(* exception type for interpreter control flow *)
Datatype:
  exception
  = Error error
  | AssertException string
  | BreakException
  | ContinueException
  | ReturnException value
End


Definition value_to_key_def:
  value_to_key (IntV _ i) = SOME $ IntSubscript i ∧
  value_to_key (StringV _ s) = SOME $ StrSubscript s ∧
  value_to_key (BytesV _ bs) = SOME $ BytesSubscript bs ∧
  value_to_key (FlagV _ n) = SOME $ IntSubscript $ &n ∧
  value_to_key _ = NONE
End

val () = cv_auto_trans value_to_key_def;

Definition evaluate_subscript_def:
  evaluate_subscript tenv (Value (ArrayV av)) (IntV _ i) =
  (case array_index av i
   of SOME v => INL $ INL $ Value v
    | _ => INR (RuntimeError "subscript array_index")) ∧
  evaluate_subscript tenv (HashMapRef is_transient slot kt vt) kv =
  (let new_slot = hashmap_slot slot $ encode_hashmap_key kt kv in
   case vt
   of HashMapT kt' vt' => INL $ INL $ HashMapRef is_transient new_slot kt' vt'
    | Type t =>
        (case evaluate_type tenv t of
         | SOME tv => INL $ INR (is_transient, new_slot, tv)
         | NONE => INR (TypeError "evaluate_subscript evaluate_type"))) ∧
  evaluate_subscript tenv (ArrayRef is_transient base_slot elem_tv bd) (IntV _ i) =
  (if 0 ≤ i ∧ Num i < bound_length bd then
    let elem_offset = (case bd of Fixed _ => 0 | Dynamic _ => 1) in
    let slot = base_slot + n2w (elem_offset + Num i * type_slot_size elem_tv) in
    case elem_tv of
    | ArrayTV inner_tv inner_bd =>
        INL $ INL $ ArrayRef is_transient slot inner_tv inner_bd
    | _ => INL $ INR (is_transient, slot, elem_tv)
   else INR (RuntimeError "subscript array out of bounds")) ∧
  evaluate_subscript _ _ _ = INR (TypeError "evaluate_subscript")
End

val () = cv_auto_trans evaluate_subscript_def;

Definition evaluate_subscripts_def:
  evaluate_subscripts a [] = INL a ∧
  evaluate_subscripts a ((IntSubscript i)::is) =
  (case a of ArrayV av =>
   (case array_index av i of SOME v =>
    (case evaluate_subscripts v is of INL vj => INL vj
     | INR err => INR err)
    | _ => INR (RuntimeError "evaluate_subscripts array_index"))
   | _ => INR (TypeError "evaluate_subscripts type")) ∧
  evaluate_subscripts (StructV al) ((AttrSubscript id)::is) =
  (case ALOOKUP al id of SOME v =>
    (case evaluate_subscripts v is of INL v' => INL v'
     | INR err => INR err)
   | _ => INR (TypeError "evaluate_subscripts AttrSubscript")) ∧
  evaluate_subscripts _ _ = INR (TypeError "evaluate_subscripts")
End

val evaluate_subscripts_pre_def =
  cv_auto_trans_pre "evaluate_subscripts_pre" evaluate_subscripts_def;

Theorem evaluate_subscripts_pre[cv_pre]:
  !a b. evaluate_subscripts_pre a b
Proof
  ho_match_mp_tac evaluate_subscripts_ind
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ gvs[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED


(* mutating inside arrays, structs, hashmaps *)

Datatype:
  assign_operation
  = Replace value
  | Update binop value
  | AppendOp value
  | PopOp
End

Theorem assign_operation_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperInterpreter",Tyop="assign_operation"}));

Definition assign_subscripts_def:
  assign_subscripts a [] (Replace v) = INL v (* TODO: cast to type of a *) ∧
  assign_subscripts a [] (Update bop v) = evaluate_binop bop a v ∧
  assign_subscripts a [] (AppendOp v) = append_element a v ∧
  assign_subscripts a [] PopOp = pop_element a ∧
  assign_subscripts a ((IntSubscript i)::is) ao =
  (case a of ArrayV av =>
   (case array_index av i of SOME v =>
    (case assign_subscripts v is ao of INL vj =>
       array_set_index av i vj
     | INR err => INR err)
    | _ => INR (RuntimeError "assign_subscripts array_index"))
   | _ => INR (TypeError "assign_subscripts type")) ∧
  assign_subscripts (StructV al) ((AttrSubscript id)::is) ao =
  (case ALOOKUP al id of SOME v =>
    (case assign_subscripts v is ao of INL v' =>
      INL $ StructV $ AFUPDKEY id (K v') al
     | INR err => INR err)
   | _ => INR (TypeError "assign_subscripts AttrSubscript")) ∧
  assign_subscripts _ _ _ = INR (TypeError "assign_subscripts")
End

val assign_subscripts_pre_def =
  cv_auto_trans_pre "assign_subscripts_pre" assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c. assign_subscripts_pre a b c
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[Once assign_subscripts_pre_def]
  \\ rw[Once assign_subscripts_pre_def]
  \\ gvs[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED



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
    is_creation := F
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
  evaluate_account_op Address bs _ = BytesV (Fixed 20) bs ∧
  evaluate_account_op Balance _ a = IntV (Unsigned 256) &a.balance ∧
  evaluate_account_op Codehash _ a = BytesV (Fixed 32) (Keccak_256_w64 a.code) ∧
  evaluate_account_op Codesize _ a = IntV (Unsigned 256) $ &LENGTH a.code ∧
  evaluate_account_op IsContract _ a = BoolV (a.code ≠ []) ∧
  evaluate_account_op Code _ a = BytesV (Dynamic (LENGTH a.code)) a.code
End

val () = cv_auto_trans evaluate_account_op_def;

Definition evaluate_block_hash_def:
  evaluate_block_hash t n =
  let pbn = t.block_number - 1 in
  if t.block_number ≤ n ∨
     LENGTH t.block_hashes ≤ pbn - n
  then INR (RuntimeError "evaluate_block_hash")
  else INL $ BytesV (Fixed 32)
    (word_to_bytes (EL (pbn - n) t.block_hashes) T)
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
    BytesV (Fixed 32) $
      word_to_bytes (if n < LENGTH t.blob_hashes
                     then EL n t.blob_hashes
                     else 0w) T
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
            INL $ BytesV (Fixed m) (TAKE m bs)
          else INR (RuntimeError "evaluate_extract32 bytesM")
      | UintT m =>
          evaluate_convert (BytesV (Dynamic 32) (TAKE 32 bs)) (BaseT (UintT m))
      | IntT m =>
          evaluate_convert (BytesV (Dynamic 32) (TAKE 32 bs)) (BaseT (IntT m))
      | AddressT =>
          if 20 ≤ LENGTH bs then
            INL $ BytesV (Fixed 20) (TAKE 20 bs)
          else INR (RuntimeError "evaluate_extract32 address")
      | _ => INR (TypeError "evaluate_extract32 type")
  else INR (RuntimeError "evaluate_extract32 start")
End

val () = cv_trans evaluate_extract32_def;

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
    evaluate_convert v typ ∧
  evaluate_type_builtin cx Epsilon typ [] =
    (if typ = BaseT DecimalT then INL $ DecimalV 1
     else INR (TypeError "Epsilon: not decimal")) ∧
  evaluate_type_builtin cx Extract32 (BaseT bt) [BytesV _ bs; IntV u i] =
    (if u = Unsigned 256 then evaluate_extract32 bs (Num i) bt
     else INR (TypeError "Extract32 type")) ∧
  evaluate_type_builtin cx AbiDecode typ [BytesV _ bs] =
    (case evaluate_abi_decode (get_tenv cx) typ bs of
       INL v => INL v | INR str => INR (RuntimeError str)) ∧
  evaluate_type_builtin _ AbiDecode _ _ =
    INR (TypeError "abi_decode args") ∧
  evaluate_type_builtin cx AbiEncode typ vs =
    (case evaluate_abi_encode (get_tenv cx) typ (ArrayV (TupleV vs)) of
       INL v => INL v | INR str => INR (RuntimeError str)) ∧
  evaluate_type_builtin _ _ _ _ =
    INR (TypeError "evaluate_type_builtin")
End

val () = cv_auto_trans evaluate_type_builtin_def;

Definition evaluate_ecrecover_def:
  evaluate_ecrecover [BytesV _ hash_bytes; IntV u1 v_int; IntV u2 r_int; IntV u3 s_int] =
    (if u1 = Unsigned 256 ∧ u2 = Unsigned 256 ∧ u3 = Unsigned 256 ∧
        LENGTH hash_bytes = 32
     then let
       hash = word_of_bytes T (0w:bytes32) hash_bytes;
       v = Num v_int;
       r = Num r_int;
       s = Num s_int
     in case vfmExecution$ecrecover hash v r s of
          NONE => INL $ AddressV 0w
        | SOME addr => INL $ AddressV addr
     else INR (TypeError "ECRecover type")) ∧
  evaluate_ecrecover _ = INR (TypeError "ECRecover args")
End

val () = cv_auto_trans evaluate_ecrecover_def;

Definition evaluate_ecadd_def:
  evaluate_ecadd [ArrayV (TupleV [IntV u1 x1; IntV u2 y1]);
                  ArrayV (TupleV [IntV u3 x2; IntV u4 y2])] =
    (if u1 = Unsigned 256 ∧ u2 = Unsigned 256 ∧
        u3 = Unsigned 256 ∧ u4 = Unsigned 256
     then let
       p1 = (Num x1, Num y1);
       p2 = (Num x2, Num y2)
     in case vfmExecution$ecadd p1 p2 of
          NONE => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) 0; IntV (Unsigned 256) 0]
        | SOME (rx, ry) => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) (&rx); IntV (Unsigned 256) (&ry)]
     else INR (TypeError "ECAdd type")) ∧
  evaluate_ecadd _ = INR (TypeError "ECAdd args")
End

val () = cv_auto_trans evaluate_ecadd_def;

Definition evaluate_ecmul_def:
  evaluate_ecmul [ArrayV (TupleV [IntV u1 x; IntV u2 y]); IntV u3 scalar] =
    (if u1 = Unsigned 256 ∧ u2 = Unsigned 256 ∧ u3 = Unsigned 256
     then let
       p = (Num x, Num y);
       n = Num scalar
     in case vfmExecution$ecmul p n of
          NONE => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) 0; IntV (Unsigned 256) 0]
        | SOME (rx, ry) => INL $ ArrayV $ TupleV
            [IntV (Unsigned 256) (&rx); IntV (Unsigned 256) (&ry)]
     else INR (TypeError "ECMul type")) ∧
  evaluate_ecmul _ = INR (TypeError "ECMul args")
End

val () = cv_auto_trans evaluate_ecmul_def;

Definition evaluate_builtin_def:
  evaluate_builtin cx _ Len [BytesV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [StringV _ ls] = INL (IntV (Unsigned 256) &(LENGTH ls)) ∧
  evaluate_builtin cx _ Len [ArrayV av] = INL (IntV (Unsigned 256) &(array_length av)) ∧
  evaluate_builtin cx _ Not [BoolV b] = INL (BoolV (¬b)) ∧
  evaluate_builtin cx _ Not [IntV u i] =
    (if is_Unsigned u ∧ 0 ≤ i then INL (IntV u (int_not i)) else INR (TypeError "signed Not")) ∧
  evaluate_builtin cx _ Not [FlagV m n] = INL $ FlagV m $
    w2n $ (~((n2w n):bytes32)) && ~(~(0w:bytes32) << m) ∧
  evaluate_builtin cx _ Neg [IntV u i] = bounded_int_op u u (-i) ∧
  evaluate_builtin cx _ Neg [DecimalV i] = bounded_decimal_op (-i) ∧
  evaluate_builtin cx _ Keccak256 [BytesV _ ls] = INL $ BytesV (Fixed 32) $
    Keccak_256_w64 ls ∧
  evaluate_builtin cx _ Keccak256 [StringV _ s] = INL $ BytesV (Fixed 32) $
    Keccak_256_w64 (MAP (n2w o ORD) s) ∧
  (* TODO: reject BytesV with invalid bounds for Keccak256 *)
  evaluate_builtin cx _ (Uint2Str n) [IntV u i] =
    (if is_Unsigned u then INL $ StringV n (num_to_dec_string (Num i))
     else INR (TypeError "Uint2Str")) ∧
  evaluate_builtin cx _ (AsWeiValue dn) [v] = evaluate_as_wei_value dn v ∧
  evaluate_builtin cx _ AddMod [IntV u1 i1; IntV u2 i2; IntV u3 i3] =
    (if u1 = Unsigned 256 ∧ u2 = u1 ∧ u3 = u1
     then INL $ IntV u1 $ &((Num i1 + Num i2) MOD Num i3)
     else INR (TypeError "AddMod type")) ∧
  evaluate_builtin cx _ MulMod [IntV u1 i1; IntV u2 i2; IntV u3 i3] =
    (if u1 = Unsigned 256 ∧ u2 = u1 ∧ u3 = u1
     then INL $ IntV u1 $ &((Num i1 * Num i2) MOD Num i3)
     else INR (TypeError "MulMod type")) ∧
  evaluate_builtin cx _ PowMod256 [IntV u1 base; IntV u2 exp] =
    (if u1 = Unsigned 256 ∧ u2 = u1
     then INL $ IntV u1 $ &(vfmExecution$modexp (Num base) (Num exp) (2 ** 256) 1)
     else INR (TypeError "PowMod256 type")) ∧
  evaluate_builtin cx _ Floor [DecimalV i] =
    INL $ IntV (Signed 256) (i / 10000000000) ∧
  evaluate_builtin cx _ Ceil [DecimalV i] =
    INL $ IntV (Signed 256) ((i + 9999999999) / 10000000000) ∧
  evaluate_builtin cx _ (Bop bop) [v1; v2] = evaluate_binop bop v1 v2 ∧
  evaluate_builtin cx _ (Env Sender) [] = INL $ AddressV cx.txn.sender ∧
  evaluate_builtin cx _ (Env SelfAddr) [] = INL $ AddressV cx.txn.target ∧
  evaluate_builtin cx _ (Env ValueSent) [] = INL $ IntV (Unsigned 256) &cx.txn.value ∧
  evaluate_builtin cx _ (Env TimeStamp) [] = INL $ IntV (Unsigned 256) &cx.txn.time_stamp ∧
  evaluate_builtin cx _ (Env BlockNumber) [] = INL $ IntV (Unsigned 256) &cx.txn.block_number ∧
  evaluate_builtin cx _ (Env BlobBaseFee) [] = INL $ IntV (Unsigned 256) &cx.txn.blob_base_fee ∧
  evaluate_builtin cx _ (Env GasPrice) [] = INL $ IntV (Unsigned 256) &cx.txn.gas_price ∧
  evaluate_builtin cx _ (Env ChainId) [] = INL $ IntV (Unsigned 256) &cx.txn.chain_id ∧
  evaluate_builtin cx _ (Env PrevHash) [] = evaluate_block_hash cx.txn (cx.txn.block_number - 1) ∧
  evaluate_builtin cx _ BlockHash [IntV u i] =
    (if u = Unsigned 256 then evaluate_block_hash cx.txn (Num i)
     else INR (TypeError "BlockHash type")) ∧
  evaluate_builtin cx _ BlobHash [IntV u i] =
    (if u = Unsigned 256 then INL $ evaluate_blob_hash cx.txn (Num i)
     else INR (TypeError "BlobHash type")) ∧
  evaluate_builtin cx _ (Concat n) vs = evaluate_concat n vs ∧
  evaluate_builtin cx _ (Slice n) [v1; v2; v3] = evaluate_slice v1 v2 v3 n ∧
  evaluate_builtin cx _ (MakeArray to bd) vs =
    (case to
     of NONE => INL $ ArrayV $ TupleV vs
      | SOME t =>
        (case evaluate_type (get_tenv cx) t
         of NONE => INR (TypeError "MakeArray type")
          | SOME tv => INL $ ArrayV $ make_array_value tv bd vs)) ∧
  evaluate_builtin cx acc (Acc aop) [BytesV _ bs] =
    (let a = lookup_account (word_of_bytes T (0w:address) bs) acc in
      INL $ evaluate_account_op aop bs a) ∧
  evaluate_builtin cx _ Isqrt [IntV u i] =
    (if is_Unsigned u ∧ 0 ≤ i then INL $ IntV u &(num_sqrt (Num i))
     else INR (TypeError "Isqrt type")) ∧
  (* method_id: compute keccak256(signature)[:4] - returns 4-byte function selector *)
  evaluate_builtin cx _ MethodId [StringV _ sig] =
    INL $ BytesV (Fixed 4) (TAKE 4 (Keccak_256_w64 (MAP (n2w o ORD) sig))) ∧
  (* Also support Bytes input for method_id *)
  evaluate_builtin cx _ MethodId [BytesV _ bs] =
    INL $ BytesV (Fixed 4) (TAKE 4 (Keccak_256_w64 bs)) ∧
  evaluate_builtin cx _ ECRecover vs = evaluate_ecrecover vs ∧
  evaluate_builtin cx _ ECAdd vs = evaluate_ecadd vs ∧
  evaluate_builtin cx _ ECMul vs = evaluate_ecmul vs ∧
  evaluate_builtin _ _ _ _ = INR (TypeError "builtin")
End

val evaluate_builtin_pre_def = cv_auto_trans_pre "evaluate_builtin_pre" evaluate_builtin_def;

Theorem evaluate_builtin_pre[cv_pre]:
  evaluate_builtin_pre a b c d
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
  type_builtin_args_length_ok AbiDecode n = (n = 1) ∧
  type_builtin_args_length_ok AbiEncode n = (n >= 1)
End

val () = cv_auto_trans type_builtin_args_length_ok_def;

Definition builtin_args_length_ok_def:
  builtin_args_length_ok Len n = (n = 1n) ∧
  builtin_args_length_ok Not n = (n = 1) ∧
  builtin_args_length_ok Neg n = (n = 1) ∧
  builtin_args_length_ok Keccak256 n = (n = 1) ∧
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

(* Machinery for managing variables (local, top-level, mutable, immutable), and
* other stateful data during execution (e.g., EVM account states, logs)*)

(*
We don't use identifiers directly because cv compute prefers num keys
Type scope = “:identifier |-> value”;
*)
Type scope = “:num |-> value”;

(* find a variable in a list of nested scopes *)
Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME v => SOME v
End

(* find the location of a variable in a list of nested scopes (as well as its
* value): this is used when assigning to that variable *)
Definition find_containing_scope_def:
  find_containing_scope id ([]:scope list) = NONE ∧
  find_containing_scope id (env::rest) =
  case FLOOKUP env id of NONE =>
    OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
  | SOME v => SOME ([], env, v, rest)
End

val () = cv_auto_trans find_containing_scope_def;

Type log = “:nsid # (value list)”;

(* Module-aware immutables: keyed by source_id *)
(* NONE = main contract, SOME n = module with source_id n *)
Type module_immutables = “:(num option, num |-> value) alist”

Definition empty_immutables_def:
  empty_immutables : module_immutables = []
End

val () = cv_auto_trans empty_immutables_def;

Datatype:
  evaluation_state = <|
    immutables: (address, module_immutables) alist
  ; logs: log list
  ; scopes: scope list
  ; accounts: evm_accounts
  ; tStorage: transient_storage
  |>
End

Definition empty_state_def:
  empty_state : evaluation_state = <|
    accounts := empty_accounts;
    immutables := [];
    logs := [];
    scopes := [];
    tStorage := empty_transient_storage
  |>
End

val () = cv_trans empty_state_def;

(* state-exception monad used for the main interpreter *)

Type evaluation_result = “:(α + exception) # evaluation_state”

Definition return_def:
  return x s = (INL x, s) : α evaluation_result
End

val () = cv_auto_trans return_def;

Definition raise_def:
  raise e s = (INR e, s) : α evaluation_result
End

val () = cv_auto_trans raise_def;

Definition bind_def:
  bind f g (s: evaluation_state) : α evaluation_result =
  case f s of (INL x, s) => g x s | (INR e, s) => (INR e, s)
End

Definition ignore_bind_def:
  ignore_bind f g = bind f (λx. g)
End

Definition assert_def:
  assert b e s = ((if b then INL () else INR e), s) : unit evaluation_result
End

val () = cv_auto_trans assert_def;

Definition check_def:
  check b str = assert b (Error (RuntimeError str))
End

val () = cv_auto_trans check_def;

Definition type_check_def:
  type_check b str = assert b (Error (TypeError str))
End

val () = cv_auto_trans type_check_def;

val () = declare_monad ("vyper_evaluation",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “raise”, guard = SOME “assert”
  });
val () = enable_monad "vyper_evaluation";
val () = enable_monadsyntax();

Definition try_def:
  try f h s : α evaluation_result =
  case f s of (INR e, s) => h e s | x => x
End

Definition finally_def:
  finally f g s : α evaluation_result =
  case f s of (INL x, s) => ignore_bind g (return x) s
     | (INR e, s) => ignore_bind g (raise e) s
End

(* TODO: move these? *)
Theorem option_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="option",Tyop="option"}));

Theorem sum_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="sum",Tyop="sum"}));

Theorem list_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="list",Tyop="list"}));

Theorem prod_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="pair",Tyop="prod"}));

Theorem value_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperValue",Tyop="value"}));

Theorem type_value_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperValue",Tyop="type_value"}));

Theorem bound_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperAST",Tyop="bound"}));

Definition lift_option_def:
  lift_option x str =
    case x of SOME v => return v | NONE => raise $ Error (RuntimeError str)
End

val () = lift_option_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_def:
  lift_sum x =
    case x of INL v => return v | INR e => raise $ Error e
End

val () = lift_sum_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_runtime_def:
  lift_sum_runtime x =
    case x of INL v => return v | INR str => raise $ Error (RuntimeError str)
End

val () = lift_sum_runtime_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

Definition lift_option_type_def:
  lift_option_type x str =
    case x of SOME v => return v | NONE => raise $ Error (TypeError str)
End

val () = lift_option_type_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

(* reading from the state *)

Definition get_address_immutables_def:
  get_address_immutables cx st =
    lift_option (ALOOKUP st.immutables cx.txn.target) "get_address_immutables" st
End

val () = get_address_immutables_def
  |> SRULE [lift_option_def, option_CASE_rator]
  |> cv_auto_trans;

(* Helper: get immutables for a source_id, or empty if not present *)
Definition get_source_immutables_def:
  get_source_immutables src_id_opt (imms: module_immutables) =
    case ALOOKUP imms src_id_opt of
      NONE => FEMPTY
    | SOME imm => imm
End

val () = cv_auto_trans get_source_immutables_def;

(* Helper: set immutables for a source_id *)
Definition set_source_immutables_def:
  set_source_immutables src_id_opt imm (imms: module_immutables) =
    (src_id_opt, imm) :: ADELKEY src_id_opt imms
End

val () = cv_auto_trans set_source_immutables_def;

(* Find a storage variable or hashmap declaration in toplevels *)
Datatype:
  var_decl_info
  = StorageVarDecl bool type            (* is_transient, type *)
  | HashMapVarDecl bool type value_type (* is_transient, key type, value type *)
End

Theorem var_decl_info_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperInterpreter",Tyop="var_decl_info"}));

(* Look up variable slot from storage_layout *)
Definition lookup_var_slot_from_layout_def:
  lookup_var_slot_from_layout cx is_transient src_id_opt var_name =
    case ALOOKUP cx.layouts cx.txn.target of
    | NONE => NONE
    | SOME (storage_lay, transient_lay) =>
        ALOOKUP (if is_transient then transient_lay else storage_lay) (src_id_opt, var_name)
End

val () = cv_auto_trans lookup_var_slot_from_layout_def;

(* Find var decl by num key (comparing string_to_num of each id) *)
Definition find_var_decl_by_num_def:
  find_var_decl_by_num n [] = NONE ∧
  find_var_decl_by_num n (VariableDecl _ mut vid typ :: ts) =
    (if (mut = Storage ∨ mut = Transient) ∧ string_to_num vid = n
     then SOME (StorageVarDecl (mut = Transient) typ, vid)
     else find_var_decl_by_num n ts) ∧
  find_var_decl_by_num n (HashMapDecl _ is_transient vid kt vt :: ts) =
    (if string_to_num vid = n then SOME (HashMapVarDecl is_transient kt vt, vid)
     else find_var_decl_by_num n ts) ∧
  find_var_decl_by_num n (_ :: ts) = find_var_decl_by_num n ts
End

val () = cv_auto_trans find_var_decl_by_num_def;

Definition get_accounts_def:
  get_accounts st = return st.accounts st
End

val () = cv_auto_trans get_accounts_def;

Definition update_accounts_def:
  update_accounts f st = return () (st with accounts updated_by f)
End

Definition get_transient_storage_def:
  get_transient_storage st = return st.tStorage st
End

val () = cv_auto_trans get_transient_storage_def;

Definition update_transient_def:
  update_transient f st = return () (st with tStorage updated_by f)
End

Definition get_storage_backend_def:
  get_storage_backend cx T = do
    tStore <- get_transient_storage;
    return $ vfmExecution$lookup_transient_storage cx.txn.target tStore
  od ∧
  get_storage_backend cx F = do
    accts <- get_accounts;
    return $ (lookup_account cx.txn.target accts).storage
  od
End

val () = get_storage_backend_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition set_storage_backend_def:
  set_storage_backend cx T storage' =
    update_transient (vfmExecution$update_transient_storage cx.txn.target storage') ∧
  set_storage_backend cx F storage' = do
    accts <- get_accounts;
    acc <<- lookup_account cx.txn.target accts;
    update_accounts (update_account cx.txn.target (acc with storage := storage'))
  od
End

val () = set_storage_backend_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, update_transient_def, update_accounts_def]
  |> cv_auto_trans;

(* Read a value from storage at a slot *)
Definition read_storage_slot_def:
  read_storage_slot cx is_transient (slot : bytes32) tv = do
    storage <- get_storage_backend cx is_transient;
    lift_option (decode_value storage (w2n slot) tv)
      "read_storage_slot decode"
  od
End

val () = read_storage_slot_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

(* Write a value to storage at a slot *)
Definition write_storage_slot_def:
  write_storage_slot cx is_transient slot tv v = do
    storage <- get_storage_backend cx is_transient;
    writes <- lift_option (encode_value tv v) "write_storage_slot encode";
    storage' <<- apply_writes slot writes storage;
    set_storage_backend cx is_transient storage'
  od
End

val () = write_storage_slot_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, set_storage_backend_def,
            update_transient_def, update_accounts_def]
  |> cv_auto_trans;

(* Module-aware immutables lookup *)
Definition get_immutables_def:
  get_immutables cx src_id_opt = do
    imms <- get_address_immutables cx;
    return (get_source_immutables src_id_opt imms)
  od
End

val () = get_immutables_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

(* Module-aware global lookup: look up variable n in module src_id_opt *)
Definition lookup_global_def:
  lookup_global cx src_id_opt n = do
    ts <- lift_option_type (get_module_code cx src_id_opt) "lookup_global get_module_code";
    tenv <<- get_tenv cx;
    case find_var_decl_by_num n ts of
    | NONE => do
        (* Not a storage/hashmap var — check immutables *)
        imms <- get_immutables cx src_id_opt;
        case FLOOKUP imms n of
        | SOME v => return (Value v)
        | NONE => raise $ Error (TypeError "lookup_global: var not found")
      od
    | SOME (StorageVarDecl is_transient typ, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "lookup_global var_slot";
        tv <- lift_option_type (evaluate_type tenv typ) "lookup_global evaluate_type";
        case tv of
        | ArrayTV elem_tv bd => return (ArrayRef is_transient (n2w var_slot) elem_tv bd)
        | _ => do
            v <- read_storage_slot cx is_transient (n2w var_slot) tv;
            return (Value v)
          od
      od
    | SOME (HashMapVarDecl is_transient kt vt, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "lookup_global hashmap var_slot";
        return (HashMapRef is_transient (n2w var_slot) kt vt)
      od
  od
End

val () = lookup_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator,
            prod_CASE_rator, var_decl_info_CASE_rator,
            type_value_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition update_immutable_def:
  update_immutable src_id key v (imms: module_immutables) =
    let imm = get_source_immutables src_id imms in
    set_source_immutables src_id (imm |+ (key, v)) imms
End

val () = cv_auto_trans update_immutable_def;

(* Convert subscript back to a value for hashmap key encoding *)
Definition subscript_to_value_def:
  subscript_to_value (IntSubscript i) = SOME (IntV (Signed 256) i) ∧
  subscript_to_value (StrSubscript s) = SOME (StringV (LENGTH s) s) ∧
  subscript_to_value (BytesSubscript bs) = SOME (BytesV (Fixed (LENGTH bs)) bs) ∧
  subscript_to_value (AttrSubscript _) = NONE  (* Attributes are not valid hashmap keys *)
End

val () = cv_auto_trans subscript_to_value_def;

(* Compute final slot from base slot, key types, and list of subscripts *)
Definition compute_hashmap_slot_def:
  compute_hashmap_slot slot [] [] = SOME slot ∧
  compute_hashmap_slot slot (kt::kts) (k::ks) =
    (case subscript_to_value k of
     | NONE => NONE
     | SOME v =>
       let slot = hashmap_slot slot $ encode_hashmap_key kt v in
         compute_hashmap_slot slot kts ks) ∧
  compute_hashmap_slot _ _ _ = NONE
End

val compute_hashmap_slot_pre_def = cv_auto_trans_pre
  "compute_hashmap_slot_pre" compute_hashmap_slot_def;

Theorem compute_hashmap_slot_pre[cv_pre]:
  ∀x y z. compute_hashmap_slot_pre x y z
Proof
  ho_match_mp_tac compute_hashmap_slot_ind
  \\ rw[] \\ rw[Once compute_hashmap_slot_pre_def]
QED

(* Get the final value type after traversing hashmap keys.
   Returns (final_type, key_types, remaining_subs) for nested access within the value. *)
Definition split_hashmap_subscripts_def:
  split_hashmap_subscripts (Type t) subs = SOME (t, [], subs) ∧
  split_hashmap_subscripts (HashMapT kt vt) [] = NONE ∧  (* Not enough subscripts *)
  split_hashmap_subscripts (HashMapT kt vt) (_::ks) =
    (case split_hashmap_subscripts vt ks of
     | SOME (t, kts, remaining) => SOME (t, kt::kts, remaining)
     | NONE => NONE)
End

val () = cv_auto_trans split_hashmap_subscripts_def;

Definition get_scopes_def:
  get_scopes st = return st.scopes st
End

val () = cv_auto_trans get_scopes_def;

Definition lookup_flag_def:
  lookup_flag fid [] = NONE ∧
  lookup_flag fid (FlagDecl id ls :: ts) =
    (if fid = id then SOME ls else lookup_flag fid ts) ∧
  lookup_flag fid (t :: ts) = lookup_flag fid ts
End

val () = cv_auto_trans lookup_flag_def;

Definition lookup_flag_mem_def:
  lookup_flag_mem cx (src_id_opt, fid) mid =
  case get_module_code cx src_id_opt
    of NONE => raise $ Error (TypeError "lookup_flag_mem code")
     | SOME ts =>
  case lookup_flag fid ts
    of NONE => raise $ Error (TypeError "lookup_flag")
     | SOME ls =>
  case INDEX_OF mid ls
    of NONE => raise $ Error (TypeError "lookup_flag_mem index")
     | SOME i => return $ Value $ FlagV (LENGTH ls) (2 ** i)
End

val () = lookup_flag_mem_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

(* writing to the state *)

Definition set_address_immutables_def:
  set_address_immutables cx imms st =
  let addr = cx.txn.target in
    return () $ st with immutables updated_by
      (λal. (addr, imms) :: (ADELKEY addr al))
End

val () = cv_auto_trans set_address_immutables_def;

(* Module-aware global set: write a value to EVM storage *)
Definition set_global_def:
  set_global cx src_id_opt n v = do
    ts <- lift_option_type (get_module_code cx src_id_opt) "set_global get_module_code";
    tenv <<- get_tenv cx;
    case find_var_decl_by_num n ts of
    | NONE => raise $ Error (TypeError "set_global: var not found")
    | SOME (StorageVarDecl is_transient typ, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "set_global var_slot";
        tv <- lift_option_type (evaluate_type tenv typ) "set_global evaluate_type";
        write_storage_slot cx is_transient (n2w var_slot) tv v
      od
    | SOME (HashMapVarDecl _ kt vt, id) =>
        raise $ Error (TypeError "set_global: cannot set hashmap directly")
  od
End

val () = set_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator,
            prod_CASE_rator, var_decl_info_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition set_immutable_def:
  set_immutable cx src_id_opt n v = do
    imms <- get_address_immutables cx;
    let imm = get_source_immutables src_id_opt imms in
    set_address_immutables cx $ set_source_immutables src_id_opt (imm |+ (n, v)) imms
  od
End

val () = set_immutable_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition set_scopes_def:
  set_scopes env st = return () $ st with scopes := env
End

val () = cv_auto_trans set_scopes_def;

Definition push_scope_def:
  push_scope st = return () $ st with scopes updated_by CONS FEMPTY
End

val () = cv_auto_trans push_scope_def;

Definition push_scope_with_var_def:
  push_scope_with_var nm v st =
    return () $  st with scopes updated_by CONS (FEMPTY |+ (nm, v))
End

val () = cv_auto_trans push_scope_with_var_def;

Definition pop_scope_def:
  pop_scope st =
    case st.scopes
    of [] => raise (Error (TypeError "pop_scope")) st
       | _::tl => return () (st with scopes := tl)
End

val () = cv_auto_trans pop_scope_def;

(* writing variables *)

Definition new_variable_def:
  new_variable id v = do
    n <<- string_to_num id;
    env <- get_scopes;
    type_check (IS_NONE (lookup_scopes n env)) "new_variable bound";
    case env of [] => raise $ Error (TypeError "new_variable null")
    | e::es => set_scopes ((e |+ (n, v))::es)
  od
End

val () = new_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, list_CASE_rator]
  |> cv_auto_trans;

Definition set_variable_def:
  set_variable id v = do
    n <<- string_to_num id;
    sc <- get_scopes;
    (pre, env, _, rest) <-
      lift_option_type (find_containing_scope n sc) "set_variable not found";
    set_scopes (pre ++ (env |+ (n, v))::rest)
  od
End

val () = set_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, lift_option_def,
            LET_RATOR, UNCURRY, option_CASE_rator]
  |> cv_auto_trans;

(* assignment to existing locations *)

Definition get_Value_def[simp]:
  get_Value (Value v) = return v ∧
  get_Value _ = raise $ Error (TypeError "not Value")
End

val () = get_Value_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> cv_auto_trans;

Definition materialise_def:
  materialise cx (ArrayRef is_transient base_slot elem_tv bd) = do
    v <- read_storage_slot cx is_transient base_slot (ArrayTV elem_tv bd);
    return v
  od ∧
  materialise cx (Value v) = return v ∧
  materialise _ _ = raise $ Error (TypeError "materialise")
End

val () = materialise_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, toplevel_value_CASE_rator]
  |> cv_auto_trans;

Definition toplevel_array_length_def:
  toplevel_array_length cx (ArrayRef is_transient base_slot _ (Fixed n)) =
    return $ (&n : num) ∧
  toplevel_array_length cx (ArrayRef is_transient base_slot _ (Dynamic _)) = do
    storage <- get_storage_backend cx is_transient;
    return $ &(w2n (lookup_storage base_slot storage))
  od ∧
  toplevel_array_length cx (Value (ArrayV av)) =
    return $ &(array_length av) ∧
  toplevel_array_length cx (Value (BytesV _ ls)) =
    return $ &(LENGTH ls) ∧
  toplevel_array_length cx (Value (StringV _ ls)) =
    return $ &(LENGTH ls) ∧
  toplevel_array_length _ _ = raise $ Error (TypeError "toplevel_array_length")
End

val () = toplevel_array_length_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, toplevel_value_CASE_rator]
  |> cv_auto_trans;

Datatype:
  location
  = ScopedVar identifier
  | ImmutableVar identifier
  | TopLevelVar (num option) identifier  (* source_id (NONE=self), var_name *)
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Type base_target_value = “:location # subscript list”;

(* Walk through nested array subscripts computing the final element slot *)
Definition resolve_array_element_def:
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) ((IntSubscript idx)::rest) = do
    elem_offset <- (case bd of
     | Fixed n => do
         check (0 ≤ idx ∧ Num idx < n) "array fixed oob";
         return 0
       od
     | Dynamic n => do
         check (0 ≤ idx ∧ Num idx < n) "array dynamic capacity oob";
         storage <- get_storage_backend cx is_transient;
         stored_len <<- w2n (lookup_storage base_slot storage);
         check (Num idx < stored_len) "array dynamic length oob";
         return 1
       od);
    elem_slot <<- base_slot + n2w (elem_offset + Num idx * type_slot_size elem_tv);
    resolve_array_element cx is_transient elem_slot elem_tv rest
  od ∧
  resolve_array_element _ _ _ (ArrayTV _ _) (_::_) =
    raise (Error (TypeError "resolve_array_element: array needs int subscript")) ∧
  resolve_array_element _ _ base_slot tv rest = return (base_slot, tv, rest)
End

val resolve_array_element_pre_def = resolve_array_element_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, check_def,
            ignore_bind_def, bound_CASE_rator]
  |> cv_auto_trans_pre "resolve_array_element_pre";

Theorem resolve_array_element_pre[cv_pre]:
  ∀a b c d e f. resolve_array_element_pre a b c d e f
Proof
  ho_match_mp_tac resolve_array_element_ind \\ rw[]
  \\ rw[Once resolve_array_element_pre_def]
QED

Definition assign_result_def:
  assign_result PopOp old_val subs = do
    arr <- lift_sum $ evaluate_subscripts old_val subs;
    p <- lift_sum $ popped_value arr;
    return $ SOME p
  od ∧
  assign_result _ _ _ = return NONE
End

val () = assign_result_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition assign_target_def:
  assign_target cx (BaseTargetV (ScopedVar id) is) ao = do
    ni <<- string_to_num id;
    sc <- get_scopes;
    (pre, env, a, rest) <- lift_option (find_containing_scope ni sc) "assign_target lookup";
    a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
    set_scopes $ pre ++ env |+ (ni, a') :: rest;
    assign_result ao a (REVERSE is)
  od ∧
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao = do
    ni <<- string_to_num id;
    tv <- lookup_global cx src_id_opt ni;
    ts <- lift_option_type (get_module_code cx src_id_opt) "assign_target get_module_code";
    tenv <<- get_tenv cx;
    case tv of
    | Value v => do
        v' <- lift_sum $ assign_subscripts v (REVERSE is) ao;
        set_global cx src_id_opt ni v';
        assign_result ao v (REVERSE is)
      od
    | HashMapRef is_transient base_slot kt vt => do
        (first_sub, rest_subs) <- lift_option_type
          (case REVERSE is of x::xs => SOME (x, xs) | [] => NONE)
          "assign_target hashmap needs subscript";
        (final_type, key_types, remaining_subs) <- lift_option_type
          (split_hashmap_subscripts vt rest_subs)
          "assign_target split_hashmap_subscripts";
        hashmap_subs <<- first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining_subs) rest_subs;
        all_key_types <<- kt :: key_types;
        final_slot <- lift_option_type
          (compute_hashmap_slot base_slot all_key_types hashmap_subs)
          "assign_target compute_hashmap_slot";
        final_tv <- lift_option_type (evaluate_type tenv final_type) "assign_target evaluate_type";
        current_val <- read_storage_slot cx is_transient final_slot final_tv;
        new_val <- lift_sum $ assign_subscripts current_val remaining_subs ao;
        write_storage_slot cx is_transient final_slot final_tv new_val;
        assign_result ao current_val remaining_subs
      od
    | ArrayRef is_transient base_slot elem_tv bd => do
        (elem_slot, final_tv, remaining_subs) <-
          resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE is);
        case (ao, final_tv) of
        | (PopOp, ArrayTV pop_elem_tv (Dynamic _)) => do
            storage <- get_storage_backend cx is_transient;
            stored_len <<- w2n (lookup_storage elem_slot storage);
            check (stored_len > 0) "pop empty storage array";
            last_idx <<- stored_len - 1;
            last_slot <<- elem_slot + n2w (1 + last_idx * type_slot_size pop_elem_tv);
            popped <- read_storage_slot cx is_transient last_slot pop_elem_tv;
            write_storage_slot cx is_transient last_slot pop_elem_tv (default_value pop_elem_tv);
            write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
              (IntV (Unsigned 256) &last_idx);
            return $ SOME popped
          od
        | (AppendOp v, ArrayTV app_elem_tv (Dynamic n)) => do
            storage <- get_storage_backend cx is_transient;
            stored_len <<- w2n (lookup_storage elem_slot storage);
            check (stored_len < n) "append full storage array";
            new_slot <<- elem_slot + n2w (1 + stored_len * type_slot_size app_elem_tv);
            write_storage_slot cx is_transient new_slot app_elem_tv v;
            write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
              (IntV (Unsigned 256) &(stored_len + 1));
            return NONE
          od
        | _ => do
            current_val <- read_storage_slot cx is_transient elem_slot final_tv;
            new_val <- lift_sum $ assign_subscripts current_val remaining_subs ao;
            write_storage_slot cx is_transient elem_slot final_tv new_val;
            assign_result ao current_val remaining_subs
          od
      od
  od ∧
  assign_target cx (BaseTargetV (ImmutableVar id) is) ao = do
    ni <<- string_to_num id;
    src <<- current_module cx;
    imms <- get_immutables cx src;
    a <- lift_option_type (FLOOKUP imms ni) "assign_target ImmutableVar";
    a' <- lift_sum $ assign_subscripts a (REVERSE is) ao;
    set_immutable cx src ni a';
    assign_result ao a (REVERSE is)
  od ∧
  assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) = do
    type_check (LENGTH gvs = LENGTH vs) "TupleTargetV length";
    assign_targets cx gvs vs;
    return NONE
  od ∧
  assign_target _ _ _ = raise (Error (TypeError "assign_target")) ∧
  assign_targets cx [] [] = return () ∧
  assign_targets cx (gv::gvs) (v::vs) = do
    assign_target cx gv (Replace v);
    assign_targets cx gvs vs
  od ∧
  assign_targets _ _ _ = raise (Error (TypeError "assign_targets"))
End

val assign_target_pre_def = assign_target_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_RATOR, ignore_bind_def,
            UNCURRY, prod_CASE_rator, option_CASE_rator,
            toplevel_value_CASE_rator, lift_option_def,
            type_value_CASE_rator, bound_CASE_rator,
            assign_operation_CASE_rator]
  |> cv_auto_trans_pre "assign_target_pre assign_targets_pre";

Theorem assign_target_pre[cv_pre]:
  (∀w x y z. assign_target_pre w x y z) ∧
  (∀w x y z. assign_targets_pre w x y z)
Proof
  ho_match_mp_tac assign_target_ind \\ rw[]
  \\ rw[Once assign_target_pre_def]
QED

(* writing logs *)

Definition push_log_def:
  push_log log st = return () $ st with logs updated_by CONS log
End

val () = cv_auto_trans push_log_def;

(* manipulating (internal call) function stack *)

Definition push_function_def:
  push_function src_fn sc cx st =
  return (cx with stk updated_by CONS src_fn)
    $ st with scopes := [sc]
End

val () = cv_auto_trans push_function_def;

Definition pop_function_def:
  pop_function prev = set_scopes prev
End

val () = cv_auto_trans pop_function_def;

(* helper for sending ether between accounts *)

Definition transfer_value_def:
  transfer_value fromAddr toAddr amount = do
    acc <- get_accounts;
    sender <<- lookup_account fromAddr acc;
    check (amount <= sender.balance) "transfer_value amount";
    recipient <<- lookup_account toAddr acc;
    update_accounts (
      update_account fromAddr (sender with balance updated_by (flip $- amount)) o
      update_account toAddr (recipient with balance updated_by ($+ amount)));
  od
End

val () = transfer_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, update_accounts_def, o_DEF, C_DEF]
  |> cv_auto_trans;

(* machinery for calls to functions in a Vyper contract, and for internal calls
* within a contract, including implicit functions associated with public
* variables *)

Definition build_getter_def:
  build_getter e kt (Type vt) n =
    (let vn = num_to_dec_string n in
      if is_ArrayT vt then
        (let (args, ret, exp) =
           build_getter (Subscript e (Name vn))
             (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n) in
           ((vn, kt)::args, ret, exp))
      else ([(vn, kt)], vt, Subscript e (Name vn))) ∧
  build_getter e kt (HashMapT typ vtyp) n =
    (let vn = num_to_dec_string n in
     let (args, ret, exp) =
       build_getter (Subscript e (Name vn)) typ vtyp (SUC n) in
     ((vn, kt)::args, ret, exp))
Termination
  WF_REL_TAC ‘measure (value_type_size o FST o SND o SND)’
  \\ Cases \\ rw[type_size_def]
End

val () = cv_auto_trans_rec build_getter_def (
  WF_REL_TAC ‘measure (cv_size o FST o SND o SND)’
  \\ conj_tac \\ Cases \\ rw[]
  >- (
    qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ rw[] )
  \\ qmatch_asmsub_rename_tac`cv_is_ArrayT a`
  \\ Cases_on `a` \\ gvs[cv_is_ArrayT_def, cv_ArrayT_type_def]
  \\ rw[] \\ gvs[]
  \\ qmatch_goalsub_rename_tac`cv_fst p`
  \\ Cases_on `p` \\ gvs[]
);

Definition getter_def:
  getter ne kt vt =
  let (args, ret, exp) =
    build_getter ne kt vt 0
  in
    (View, args, [], ret, [Return $ SOME exp])
End

val () = cv_auto_trans getter_def;

Definition lookup_function_def:
  lookup_function src_id_opt name Deploy [] = SOME (Payable, [], [], NoneT, []) ∧
  lookup_function src_id_opt name vis [] = NONE ∧
  lookup_function src_id_opt name vis (FunctionDecl fv fm id args dflts ret body :: ts) =
  (if id = name ∧ vis = fv then SOME (fm, args, dflts, ret, body)
   else lookup_function src_id_opt name vis ts) ∧
  lookup_function src_id_opt name External (VariableDecl Public mut id typ :: ts) =
  (if id = name then
    let ne = TopLevelName (src_id_opt, id) in
    if ¬is_ArrayT typ
    then SOME (View, [], [], typ, [Return (SOME ne)])
    else SOME $ getter ne (BaseT (UintT 256)) (Type (ArrayT_type typ))
   else lookup_function src_id_opt name External ts) ∧
  lookup_function src_id_opt name External (HashMapDecl Public _ id kt vt :: ts) =
  (if id = name then SOME $ getter (TopLevelName (src_id_opt, id)) kt vt
   else lookup_function src_id_opt name External ts) ∧
  lookup_function src_id_opt name vis (_ :: ts) =
    lookup_function src_id_opt name vis ts
End

val () = cv_auto_trans lookup_function_def;

(* Lookup function callable via IntCall: Internal always, Deploy only during deployment *)
Definition lookup_callable_function_def:
  lookup_callable_function in_deploy name ts =
    case lookup_function NONE name Internal ts of
    | SOME x => SOME x
    | NONE => if in_deploy then lookup_function NONE name Deploy ts else NONE
End

val () = cv_auto_trans lookup_callable_function_def;

Definition bind_arguments_def:
  bind_arguments tenv ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments tenv ((id, typ)::params) (v::vs) =
    (case evaluate_type tenv typ of NONE => NONE | SOME tv =>
     case safe_cast tv v of NONE => NONE | SOME v =>
      OPTION_MAP (λm. m |+ (string_to_num id, v))
        (bind_arguments tenv params vs)) ∧
  bind_arguments _ _ _ = NONE
End

val bind_arguments_pre_def = cv_auto_trans_pre "bind_arguments_pre" bind_arguments_def;

Theorem bind_arguments_pre[cv_pre]:
  ∀x y z. bind_arguments_pre x y z
Proof
  ho_match_mp_tac bind_arguments_ind \\ rw[]
  \\ rw[Once bind_arguments_pre_def]
QED

Definition handle_function_def:
  handle_function (ReturnException v) = return v ∧
  handle_function (Error e) = raise $ Error e ∧
  handle_function (AssertException str) = raise $ AssertException str ∧
  handle_function _ = raise $ Error (TypeError "handle_function")
End

val () = handle_function_def
  |> SRULE [FUN_EQ_THM]
  |> cv_auto_trans;

(* helpers for the termination argument for the main interpreter definition
* (evaulate_def below) *)

Theorem expr1_size_map:
  expr1_size ls = LENGTH ls + SUM (MAP expr2_size ls)
Proof
  Induct_on`ls` \\ rw[expr_size_def]
QED

Theorem expr2_size_map:
  expr2_size x = 1 + list_size char_size (FST x) + expr_size (SND x)
Proof
  Cases_on`x` \\ rw[expr_size_def]
QED

Theorem SUM_MAP_expr2_size:
  SUM (MAP expr2_size ls) =
  LENGTH ls +
  SUM (MAP (list_size char_size o FST) ls) +
  SUM (MAP (expr_size o SND) ls)
Proof
  Induct_on`ls` \\ rw[expr2_size_map]
QED

(* recursion bound for the termination measure *)
Definition bound_def:
  stmt_bound ts Pass = 0n ∧
  stmt_bound ts Continue = 0 ∧
  stmt_bound ts Break = 0 ∧
  stmt_bound ts (Return NONE) = 0 ∧
  stmt_bound ts (Return (SOME e)) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Raise e) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Assert e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  stmt_bound ts (Log _ es) =
    1 + exprs_bound ts es ∧
  stmt_bound ts (AnnAssign _ _ e) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Append bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (Assign g e) =
    1 + target_bound ts g
      + expr_bound ts e ∧
  stmt_bound ts (AugAssign bt _ e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (If e ss1 ss2) =
    1 + expr_bound ts e +
     MAX (stmts_bound ts ss1)
         (stmts_bound ts ss2) ∧
  stmt_bound ts (For _ _ it n ss) =
    1 + iterator_bound ts it +
    1 + n + n * (stmts_bound ts ss) ∧
  stmt_bound ts (Expr e) =
    1 + expr_bound ts e ∧
  stmts_bound ts [] = 0 ∧
  stmts_bound ts (s::ss) =
    1 + stmt_bound ts s
      + stmts_bound ts ss ∧
  iterator_bound ts (Array e) =
    1 + expr_bound ts e ∧
  iterator_bound ts (Range e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  target_bound ts (BaseTarget bt) =
    1 + base_target_bound ts bt ∧
  target_bound ts (TupleTarget gs) =
    1 + targets_bound ts gs ∧
  targets_bound ts [] = 0 ∧
  targets_bound ts (g::gs) =
    1 + target_bound ts g
      + targets_bound ts gs ∧
  base_target_bound ts (NameTarget _) = 0 ∧
  base_target_bound ts (TopLevelNameTarget _) = 0 ∧
  base_target_bound ts (AttributeTarget bt _) =
    1 + base_target_bound ts bt ∧
  base_target_bound ts (SubscriptTarget bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  expr_bound ts (Name _) = 0 ∧
  expr_bound ts (TopLevelName _) = 0 ∧
  expr_bound ts (FlagMember _ _) = 0 ∧
  expr_bound ts (IfExp e1 e2 e3) =
    1 + expr_bound ts e1
      + MAX (expr_bound ts e2)
            (expr_bound ts e3) ∧
  expr_bound ts (Subscript e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  expr_bound ts (Attribute e _) =
    1 + expr_bound ts e ∧
  expr_bound ts (Literal _) = 0 ∧
  expr_bound ts (StructLit _ kes) =
    1 + exprs_bound ts (MAP SND kes) ∧
  expr_bound ts (Builtin _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Pop bt) =
    1 + base_target_bound ts bt ∧
  expr_bound ts (TypeBuiltin _ _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Call (IntCall (src_id_opt, fn)) es drv) =
    1 + exprs_bound ts es
      + (case drv of NONE => 0 | SOME e => expr_bound ts e)
      + (case ALOOKUP ts (src_id_opt, fn) of
         | SOME (dflts, ss) => exprs_bound (ADELKEY (src_id_opt, fn) ts) dflts
                             + stmts_bound (ADELKEY (src_id_opt, fn) ts) ss
         | NONE => 0) ∧
  expr_bound ts (Call t es drv) =
    1 + exprs_bound ts es
      + (case drv of NONE => 0 | SOME e => expr_bound ts e) ∧
  exprs_bound ts [] = 0 ∧
  exprs_bound ts (e::es) =
    1 + expr_bound ts e
      + exprs_bound ts es
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (INR (INR (ts, es))))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      list_size expr_size es
  | INR (INR (INR (INR (INR (INR (INL (ts, e))))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      expr_size e
  | INR (INR (INR (INR (INR (INL (ts, bt)))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      base_assignment_target_size bt
  | INR (INR (INR (INR (INL (ts, gs))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      list_size assignment_target_size gs
  | INR (INR (INR (INL (ts, g)))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      assignment_target_size g
  | INR (INR (INL (ts, it))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      iterator_size it
  | INR (INL (ts, ss)) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      list_size stmt_size ss
  | INL (ts, s) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      stmt_size s)’
  \\ rw[expr1_size_map, expr2_size_map, SUM_MAP_expr2_size,
        MAP_MAP_o, list_size_pair_size_map]
  \\ drule ALOOKUP_MEM
  \\ rw[ADELKEY_def]
  \\ qmatch_goalsub_abbrev_tac`MAP f (FILTER P ts)`
  \\ drule_then(qspecl_then[`f`,`P`]mp_tac) SUM_MAP_FILTER_MEM_LE
  \\ simp[Abbr`P`, Abbr`f`]
End

Theorem exprs_bound_DROP:
  ∀ts n es. exprs_bound ts (DROP n es) ≤ exprs_bound ts es
Proof
  Induct_on `es` \\ rw[bound_def, DROP_def]
  \\ Cases_on`n` \\ gvs[]
  \\ qmatch_goalsub_rename_tac`DROP n es`
  \\ first_x_assum(qspecl_then[`ts`,`n`]mp_tac)
  \\ simp[]
QED

(* Extract callable functions - for termination proof *)
(* Internal and Deploy are separate so we can order Internal before Deploy *)
Definition dest_Internal_Fn_def:
  dest_Internal_Fn (FunctionDecl Internal _ fn _ dflts _ ss) = [(fn, (dflts, ss))] ∧
  dest_Internal_Fn _ = []
End

Definition dest_Deploy_Fn_def:
  dest_Deploy_Fn (FunctionDecl Deploy _ fn _ dflts _ ss) = [(fn, (dflts, ss))] ∧
  dest_Deploy_Fn _ = []
End

(* For a single module, get its callable function definitions tagged with source_id *)
(* Keys are (source_id, fn). Internal entries come before Deploy entries. *)
(* This matches lookup_callable_function which tries Internal first. *)
Definition module_fns_def:
  module_fns src_id ts =
    MAP (λ(fn, ss). ((src_id, fn), ss))
        (FLAT (MAP dest_Internal_Fn ts) ++ FLAT (MAP dest_Deploy_Fn ts))
End

(* Get all callable function definitions from all modules, keyed by (source_id, fn) *)
Definition remcode_def:
  remcode cx =
  case ALOOKUP cx.sources cx.txn.target of
    NONE => []
  | SOME mods =>
      FILTER (λ((src_id, fn), ss). ¬MEM (src_id, fn) cx.stk)
        (FLAT (MAP (λ(src_id, ts). module_fns src_id ts) mods))
End

(* these helpers are also for termination, to enable HOL4's definition machinery
* to "see through" the state-exception monad when constructing the termination
* conditions *)

Theorem bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED

Theorem ignore_bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ⇒ g t = g' t)
  ⇒
  ignore_bind f g = ignore_bind f' g'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong_implicit
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

Theorem try_cong[defncong]:
  (f s = f' s') ∧
  (∀e t. f' s = (INR e, t) ⇒ h e t = h' e t) ∧
  (s = s')
  ⇒
  try f h s = try f' h' s'
Proof
  rw[try_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem try_cong_implicit[defncong]:
  (f = f') ∧
  (∀s e t. f' s = (INR e, t) ⇒ h e t = h' e t)
  ⇒
  try f h = try f' h'
Proof
  rw[FUN_EQ_THM]
  \\ irule try_cong \\ rw[]
  \\ first_x_assum irule
  \\ metis_tac[]
QED

Theorem bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (INL x, t) ==> g x t = g' x t) ∧
  (s = s')
  ⇒
  bind f g s = bind f' g' s'
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem ignore_bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (INL x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  ignore_bind f g s = ignore_bind f' g' s'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong
  \\ rw[]
QED

Theorem finally_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  finally f g s = finally f' g' s'
Proof
  rw[finally_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ irule ignore_bind_cong \\ gs[]
QED

(* lookup_function with Internal finds body via ALOOKUP on dest_Internal_Fn *)
Theorem lookup_function_Internal_imp_ALOOKUP:
  ∀src_id_opt fn vis ts v w x y z.
  lookup_function src_id_opt fn vis ts = SOME (v,w,x,y,z) ∧ vis = Internal ⇒
  (x, z) = ([], []) ∨ ALOOKUP (FLAT (MAP dest_Internal_Fn ts)) fn = SOME (x, z)
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_Fn_def]
  \\ gvs[dest_Internal_Fn_def]
  \\ rename1 `FunctionDecl fv _ _ _ _ _ _`
  \\ Cases_on `fv` \\ gvs[dest_Internal_Fn_def]
QED

(* lookup_function with Deploy finds body via ALOOKUP on dest_Deploy_Fn *)
Theorem lookup_function_Deploy_imp_ALOOKUP:
  ∀src_id_opt fn vis ts v w x y z.
  lookup_function src_id_opt fn vis ts = SOME (v,w,x,y,z) ∧ vis = Deploy ⇒
  (x, z) = ([], []) ∨ ALOOKUP (FLAT (MAP dest_Deploy_Fn ts)) fn = SOME (x, z)
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Deploy_Fn_def]
  \\ gvs[dest_Deploy_Fn_def]
  \\ rename1 `FunctionDecl fv _ _ _ _ _ _`
  \\ Cases_on `fv` \\ gvs[dest_Deploy_Fn_def]
QED

(* If Internal lookup fails, no Internal entry in the list *)
Theorem lookup_function_Internal_NONE_imp:
  ∀src_id_opt fn vis ts.
  lookup_function src_id_opt fn vis ts = NONE ∧ vis = Internal ⇒
  ALOOKUP (FLAT (MAP dest_Internal_Fn ts)) fn = NONE
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_Fn_def]
  \\ gvs[dest_Internal_Fn_def]
  \\ rename1 `FunctionDecl fv _ _ _ _ _ _`
  \\ Cases_on `fv` \\ gvs[dest_Internal_Fn_def]
QED

(* TODO: move? *)
Theorem ALOOKUP_MAP_KEY_INJ:
  (∀x y. f x = f y ⇒ x = y) ∧ fk = (f k) ⇒
  ALOOKUP (MAP (f ## I) ls) fk =
  ALOOKUP ls k
Proof
  map_every qid_spec_tac[`k`,`fk`]
  \\ Induct_on `ls` \\ simp[]
  \\ Cases \\ rw[]
  \\ metis_tac[]
QED

(* Key lemma: lookup_callable_function finds exactly what ALOOKUP on module_fns finds *)
(* This works because module_fns orders Internal entries before Deploy entries, *)
(* matching lookup_callable_function which tries Internal first. *)
Theorem lookup_callable_function_eq_ALOOKUP_module_fns:
  ∀in_deploy fn ts src_id v w x y z.
  lookup_callable_function in_deploy fn ts = SOME (v,w,x,y,z) ∧ (x, z) ≠ ([], []) ⇒
  ALOOKUP (module_fns src_id ts) (src_id, fn) = SOME (x, z)
Proof
  rpt gen_tac
  \\ simp[lookup_callable_function_def, module_fns_def]
  \\ gvs[CaseEq"option"]
  \\ reverse strip_tac
  (* Case 1: Internal found *)
  >- (
    drule lookup_function_Internal_imp_ALOOKUP \\ rw[]
    \\ simp[ALOOKUP_APPEND]
    \\ qmatch_goalsub_abbrev_tac`option_CASE alo`
    \\ `alo = SOME (x, z)` suffices_by simp[]
    \\ qunabbrev_tac `alo`
    \\ pop_assum $ SUBST1_TAC o SYM
    \\ qmatch_goalsub_abbrev_tac`MAP fi`
    \\ `fi = $, src_id ## I` by simp[Abbr`fi`, FUN_EQ_THM, FORALL_PROD]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule ALOOKUP_MAP_KEY_INJ
    \\ simp[]
  )
  (* Case 2: Internal NONE, Deploy found *)
  \\ drule lookup_function_Deploy_imp_ALOOKUP \\ rw[]
  \\ drule lookup_function_Internal_NONE_imp \\ rw[]
  \\ simp[ALOOKUP_APPEND]
  \\ qmatch_goalsub_abbrev_tac`option_CASE alo`
  \\ qmatch_goalsub_abbrev_tac`MAP fi`
  \\ `fi = $, src_id ## I` by simp[Abbr`fi`, FUN_EQ_THM, FORALL_PROD]
  \\ pop_assum SUBST_ALL_TAC
  \\ `alo = NONE`
  by (
    qpat_x_assum`_ = NONE` $ SUBST1_TAC o SYM
    \\ qunabbrev_tac`alo`
    \\ irule ALOOKUP_MAP_KEY_INJ
    \\ simp[] )
  \\ simp[]
  \\ qpat_x_assum`_ = SOME _` $ SUBST1_TAC o SYM
  \\ irule ALOOKUP_MAP_KEY_INJ
  \\ simp[]
QED

(* Helper: ALOOKUP in module_fns is NONE when src_id doesn't match *)
Theorem ALOOKUP_module_fns_diff_src:
  ∀ts sid1 sid2 fn.
    sid1 ≠ sid2 ⇒ ALOOKUP (module_fns sid1 ts) (sid2, fn) = NONE
Proof
  rw[module_fns_def, ALOOKUP_FAILS, MEM_MAP, MEM_APPEND, PULL_EXISTS, FORALL_PROD]
QED

(* Helper for ALOOKUP in FLAT of MAPs *)
Theorem ALOOKUP_FLAT_MAP_module_fns:
  ∀mods src_id ts fn body.
    ALOOKUP mods src_id = SOME ts ∧
    ALOOKUP (module_fns src_id ts) (src_id, fn) = SOME body ⇒
    ALOOKUP (FLAT (MAP (λ(sid, tl). module_fns sid tl) mods)) (src_id, fn) = SOME body
Proof
  Induct \\ rw[]
  \\ simp[ALOOKUP_APPEND]
  \\ PairCases_on`h`
  \\ gvs[ALOOKUP_module_fns_diff_src, AllCaseEqs()]
QED

(* a few more helper functions used in the main interpreter *)

Definition handle_loop_exception_def:
  handle_loop_exception e =
  if e = ContinueException then return F
  else if e = BreakException then return T
  else raise e
End

val () = handle_loop_exception_def
  |> SRULE [FUN_EQ_THM, COND_RATOR]
  |> cv_auto_trans;

Definition switch_BoolV_def:
  switch_BoolV v f g =
  if v = Value $ BoolV T then f
  else if v = Value $ BoolV F then g
  else raise $ Error (TypeError (if is_Value v then "not BoolV" else "not Value"))
End

Definition exactly_one_option_def:
  exactly_one_option NONE NONE = INR (TypeError "no option") ∧
  exactly_one_option (SOME _) (SOME _) = INR (TypeError "two options") ∧
  exactly_one_option (SOME x) _ = INL x ∧
  exactly_one_option _ (SOME y) = INL y
End

val () = cv_auto_trans exactly_one_option_def;

(* Check whether variable n is declared as Immutable (not Constant) in toplevels *)
Definition is_immutable_decl_def:
  is_immutable_decl n [] = F ∧
  is_immutable_decl n (VariableDecl _ Immutable vid _ :: ts) =
    (if string_to_num vid = n then T else is_immutable_decl n ts) ∧
  is_immutable_decl n (_ :: ts) = is_immutable_decl n ts
End

val () = cv_auto_trans is_immutable_decl_def;

Definition immutable_target_def:
  immutable_target (imms: num |-> value) id n =
  case FLOOKUP imms n of SOME _ => SOME $ ImmutableVar id
     | _ => NONE
End

val () = cv_auto_trans immutable_target_def;

Definition get_range_limits_def:
  get_range_limits (IntV u1 n1) (IntV u2 n2) =
  (if u1 = u2 then
     if n1 ≤ n2
     then INL (u1, n1, Num (n2 - n1))
     else INR (RuntimeError "no range")
   else INR (TypeError "range type")) ∧
  get_range_limits _ _ = INR (TypeError "range not IntV")
End

val () = cv_auto_trans get_range_limits_def;

(* ===== External Call Execution via Verifereum ===== *)

(* Build a transaction record for initial_context.
   Only the fields used by initial_msg_params matter:
   - from: becomes msg.sender (caller)
   - to: target address
   - value: becomes msg.value
   - data: becomes msg.data (calldata)
   - gasLimit: gas available for the call
   Other fields are unused placeholders. *)
Definition make_call_tx_def:
  make_call_tx caller callee value calldata gas_limit : transaction =
    <| from := caller
     ; to := SOME callee
     ; data := calldata
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

val () = cv_auto_trans make_call_tx_def;

(* Build transaction_parameters from Vyper call_txn.
   These are the transaction-level parameters that persist across calls.

   TODO: Some fields are not yet in call_txn and use defaults:
   - origin should be original tx.origin, currently using txn.sender
   - blockCoinBase, blockGasLimit, prevRandao, chainId need to be added *)
Definition vyper_to_tx_params_def:
  vyper_to_tx_params (txn: call_txn) : transaction_parameters =
    <| origin := txn.sender  (* TODO: track tx.origin separately *)
     ; gasPrice := txn.gas_price
     ; baseFeePerGas := 0
     ; baseFeePerBlobGas := txn.blob_base_fee
     ; blockNumber := txn.block_number
     ; blockTimeStamp := txn.time_stamp
     ; blockCoinBase := 0w   (* TODO: add to call_txn *)
     ; blockGasLimit := 0    (* TODO: add to call_txn *)
     ; prevRandao := 0w      (* TODO: add to call_txn *)
     ; prevHashes := txn.block_hashes
     ; blobHashes := txn.blob_hashes
     ; chainId := 0          (* TODO: add to call_txn *)
     ; authRefund := 0
     |>
End

val () = cv_auto_trans vyper_to_tx_params_def;

(* Default gas limit for external calls - effectively infinite.
   TODO: May need to be configurable or come from an oracle. *)
Definition default_call_gas_limit_def:
  default_call_gas_limit : num = 2 ** 64
End

val () = cv_auto_trans default_call_gas_limit_def;

(* Build execution_state for an external call *)
Definition make_ext_call_state_def:
  make_ext_call_state caller callee code calldata value_opt
                      accounts tStorage txParams =
    let gas_limit = default_call_gas_limit in
    let value = (case value_opt of NONE => 0 | SOME v => v) in
    let is_static = IS_NONE value_opt in
    let tx = make_call_tx caller callee value calldata gas_limit in
    let ctxt = initial_context callee code is_static empty_return_destination tx in
    (* Transfer value from caller to callee, mirroring EVM CALL behavior.
       The EVM does this in proceed_call before entering the sub-context. *)
    let accounts = vfmExecution$transfer_value caller callee value accounts in
    let accesses = <| addresses := fINSERT caller (fINSERT callee fEMPTY)
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

val () = cv_auto_trans make_ext_call_state_def;

(* Extract results from verifereum execution.
   On success: return updated accounts/tStorage.
   On revert: return original accounts/tStorage (changes are discarded).
   On other exception: return NONE. *)
Definition extract_call_result_def:
  extract_call_result orig_accounts orig_tStorage (result, final_state) =
    case final_state.contexts of
    | [(ctxt, _)] =>
        (case result of
         | INR NONE =>  (* success - no exception *)
             SOME (T, ctxt.returnData,
                   final_state.rollback.accounts,
                   final_state.rollback.tStorage)
         | INR (SOME Reverted) =>  (* revert - return original state *)
             SOME (F, ctxt.returnData, orig_accounts, orig_tStorage)
         | _ => NONE)  (* other exception or still running *)
    | _ => NONE  (* shouldn't happen for single-context call *)
End

val () = cv_auto_trans extract_call_result_def;

(* Run external call via verifereum.

   Parameters:
   - caller: address of the calling contract (becomes msg.sender)
   - callee: address being called
   - calldata: encoded function call (from build_ext_calldata)
   - value: ETH to send (becomes msg.value)
   - is_static: true for staticcall (read-only)
   - accounts: current account states
   - tStorage: current transient storage
   - txParams: transaction parameters (preserves tx.origin, block info)

   Returns SOME (success, returnData, accounts', tStorage') or NONE on error. *)
Definition run_ext_call_def:
  run_ext_call caller callee calldata value_opt
               accounts tStorage txParams =
    let code = (lookup_account callee accounts).code in
    let s0 = make_ext_call_state caller callee code calldata value_opt
                                 accounts tStorage txParams in
    case vfmExecution$run s0 of
    | SOME (result, final_state) =>
        extract_call_result accounts tStorage (result, final_state)
    | NONE => NONE
End

val () = cv_auto_trans run_ext_call_def;

(* Dynamic array bounds check: reads stored length from storage *)
Definition check_array_bounds_def:
  check_array_bounds cx (ArrayRef is_transient base_slot _ (Dynamic _)) (IntV _ i) = do
    storage <- get_storage_backend cx is_transient;
    stored_len <<- w2n (lookup_storage base_slot storage);
    check (0 ≤ i ∧ Num i < stored_len) "subscript dynamic array oob"
  od ∧
  check_array_bounds _ _ _ = return ()
End

val () = check_array_bounds_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, check_def,
            toplevel_value_CASE_rator]
  |> cv_auto_trans;

(* top-level definition of the Vyper interpreter *)

Definition evaluate_def:
  eval_stmt cx Pass = return () ∧
  eval_stmt cx Continue = raise ContinueException ∧
  eval_stmt cx Break = raise BreakException ∧
  eval_stmt cx (Return NONE) = raise $ ReturnException NoneV ∧
  eval_stmt cx (Return (SOME e)) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    raise $ ReturnException v
  od ∧
  eval_stmt cx (Raise e) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    s <- lift_option_type (dest_StringV v) "not StringV";
    raise $ AssertException s
  od ∧
  eval_stmt cx (Assert e se) = do
    tv <- eval_expr cx e;
    switch_BoolV tv
      (return ())
      (do
         stv <- eval_expr cx se;
         sv <- get_Value stv;
         s <- lift_option_type (dest_StringV sv) "not StringV";
         raise $ AssertException s
       od)
  od ∧
  eval_stmt cx (Log id es) = do
    (* TODO: check arguments length and types *)
    vs <- eval_exprs cx es;
    push_log (id, vs)
  od ∧
  eval_stmt cx (AnnAssign id typ e) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    (* TODO: check type *)
    new_variable id v
  od ∧
  eval_stmt cx (Append t e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    assign_target cx (BaseTargetV loc sbs) (AppendOp v);
    return ()
  od ∧
  eval_stmt cx (Assign g e) = do
    gv <- eval_target cx g;
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    assign_target cx gv (Replace v);
    return ()
  od ∧
  eval_stmt cx (AugAssign t bop e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx (BaseTargetV loc sbs) (Update bop v);
    return ()
  od ∧
  eval_stmt cx (If e ss1 ss2) = do
    tv <- eval_expr cx e;
    push_scope;
    finally (
      switch_BoolV tv
        (eval_stmts cx ss1)
        (eval_stmts cx ss2)
    ) pop_scope
  od ∧
  eval_stmt cx (For id typ it n body) = do
    (* TODO: check and cast to the type *)
    vs <- eval_iterator cx it;
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
    (* TODO: check id is not in scope already? *)
    eval_for cx (string_to_num id) body vs
  od ∧
  eval_stmt cx (Expr e) = do
    tv <- eval_expr cx e;
    type_check (¬is_HashMapRef tv) "Expr HashMapRef"
  od ∧
  eval_stmts cx [] = return () ∧
  eval_stmts cx (s::ss) = do
    eval_stmt cx s; eval_stmts cx ss
  od ∧
  eval_iterator cx (Array e) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    vs <- lift_option_type (extract_elements v) "For not ArrayV";
    return vs
  od ∧
  eval_iterator cx (Range e1 e2) = do
    tv1 <- eval_expr cx e1;
    v1 <- get_Value tv1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    rl <- lift_sum $ get_range_limits v1 v2;
    u <<- FST rl; ns <<- SND rl; n1 <<- FST ns; n2 <<- SND ns;
    return $ GENLIST (λn. IntV u (n1 + &n)) n2
  od ∧
  eval_target cx (BaseTarget t) = do
    (loc, sbs) <- eval_base_target cx t;
    return $ BaseTargetV loc sbs
  od ∧
  eval_target cx (TupleTarget gs) = do
    gvs <- eval_targets cx gs;
    return $ TupleTargetV gvs
  od ∧
  eval_targets cx [] = return [] ∧
  eval_targets cx (g::gs) = do
    gv <- eval_target cx g;
    gvs <- eval_targets cx gs;
    return $ gv::gvs
  od ∧
  eval_base_target cx (NameTarget id) = do
    sc <- get_scopes;
    n <<- string_to_num id;
    svo <<- if IS_SOME (lookup_scopes n sc)
            then SOME $ ScopedVar id
	    else NONE;
    ivo <- if cx.txn.is_creation
           then do imms <- get_immutables cx (current_module cx);
                   case immutable_target imms id n of
                   | NONE => return NONE
                   | SOME tgt => do
                       ts <- lift_option_type
                               (get_module_code cx (current_module cx))
                               "NameTarget get_module_code";
                       type_check (is_immutable_decl n ts) "assign to constant";
                       return (SOME tgt)
                     od
                od
           else return NONE;
    v <- lift_sum $ exactly_one_option svo ivo;
    return $ (v, [])
  od ∧
  eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) =
    return $ (TopLevelVar src_id_opt id, []) ∧
  eval_base_target cx (AttributeTarget t id) = do
    (loc, sbs) <- eval_base_target cx t;
    return $ (loc, AttrSubscript id :: sbs)
  od ∧
  eval_base_target cx (SubscriptTarget t e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    k <- lift_option_type (value_to_key v) "SubscriptTarget value_to_key";
    return $ (loc, k :: sbs)
  od ∧
  eval_for cx nm body [] = return () ∧
  eval_for cx nm body (v::vs) = do
    push_scope_with_var nm v;
    broke <- finally
      (try (do eval_stmts cx body; return F od) handle_loop_exception)
      pop_scope ;
    if broke then return () else eval_for cx nm body vs
  od ∧
  eval_expr cx (Name id) = do
    env <- get_scopes;
    imms <- get_immutables cx (current_module cx);
    n <<- string_to_num id;
    v <- lift_sum $ exactly_one_option
           (lookup_scopes n env) (FLOOKUP imms n);
    return $ Value v
  od ∧
  eval_expr cx (TopLevelName (src_id_opt, id)) =
    lookup_global cx src_id_opt (string_to_num id) ∧
  eval_expr cx (FlagMember nsid mid) = lookup_flag_mem cx nsid mid ∧
  eval_expr cx (IfExp e1 e2 e3) = do
    tv <- eval_expr cx e1;
    switch_BoolV tv
      (eval_expr cx e2)
      (eval_expr cx e3)
  od ∧
  eval_expr cx (Literal l) = return $ Value $ evaluate_literal l ∧
  eval_expr cx (StructLit (src_id_opt, id) kes) = do
    (* TODO: type checking - validate fields against struct definition from src_id_opt *)
    ks <<- MAP FST kes;
    vs <- eval_exprs cx (MAP SND kes);
    return $ Value $ StructV $ ZIP (ks, vs)
  od ∧
  eval_expr cx (Subscript e1 e2) = do
    tv1 <- eval_expr cx e1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    tenv <<- get_tenv cx;
    check_array_bounds cx tv1 v2;
    res <- lift_sum $ evaluate_subscript tenv tv1 v2;
    case res of INL v => return v | INR (is_transient, slot, tv) => do
      v <- read_storage_slot cx is_transient slot tv;
      return $ Value v
    od
  od ∧
  eval_expr cx (Attribute e id) = do
    tv <- eval_expr cx e;
    sv <- get_Value tv;
    v <- lift_sum $ evaluate_attribute sv id;
    return $ Value $ v
  od ∧
  eval_expr cx (Builtin bt es) = do
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args";
    v <- if bt = Len then do
      tv <- eval_expr cx (HD es);
      len <- toplevel_array_length cx tv;
      return $ IntV (Unsigned 256) (&len)
    od else do
      vs <- eval_exprs cx es;
      acc <- get_accounts;
      lift_sum $ evaluate_builtin cx acc bt vs
    od;
    return $ Value v
  od ∧
  eval_expr cx (Pop bt) = do
    (loc, sbs) <- eval_base_target cx bt;
    popped <- assign_target cx (BaseTargetV loc sbs) PopOp;
    v <- lift_option_type popped "Pop returned NONE";
    return $ Value v
  od ∧
  eval_expr cx (TypeBuiltin tb typ es) = do
    type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args";
    vs <- eval_exprs cx es;
    v <- lift_sum $ evaluate_type_builtin cx tb typ vs;
    return $ Value v
  od ∧
  eval_expr cx (Call Send es _) = do
    type_check (LENGTH es = 2) "Send args";
    vs <- eval_exprs cx es;
    toAddr <- lift_option_type (dest_AddressV $ EL 0 vs) "Send not AddressV";
    amount <- lift_option_type (dest_NumV $ EL 1 vs) "Send not NumV";
    transfer_value cx.txn.target toAddr amount;
    return $ Value $ NoneV
  od ∧
  eval_expr cx (Call (ExtCall is_static (func_name, arg_types, ret_type)) es drv) = do
    vs <- eval_exprs cx es;
    check (vs ≠ []) "ExtCall no target";
    target_addr <- lift_option_type (dest_AddressV (HD vs)) "ExtCall target not address";
    (* Convention: staticcall (T) args = [target; arg1; ...]
                   extcall (F) args = [target; value; arg1; ...] *)
    (value_opt, arg_vals) <- if is_static then
      return (NONE, TL vs)
    else do
      check (TL vs ≠ []) "ExtCall no value";
      v <- lift_option_type (dest_NumV (HD (TL vs))) "ExtCall value not int";
      return (SOME v, TL (TL vs))
    od;
    tenv <<- get_tenv cx;
    calldata <- lift_option (build_ext_calldata tenv func_name arg_types arg_vals)
                            "ExtCall build_calldata";
    accounts <- get_accounts;
    tStorage <- get_transient_storage;
    txParams <<- vyper_to_tx_params cx.txn;
    caller <<- cx.txn.target;
    result <- lift_option
      (run_ext_call caller target_addr calldata value_opt accounts tStorage txParams)
      "ExtCall run failed";
    (success, returnData, accounts', tStorage') <<- result;
    check success "ExtCall reverted";
    update_accounts (K accounts');
    update_transient (K tStorage');
    if returnData = [] ∧ IS_SOME drv then
      eval_expr cx (THE drv)
    else do
      ret_val <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type returnData);
      return $ Value ret_val
    od
  od ∧
  eval_expr cx (Call (IntCall (src_id_opt, fn)) es _) = do
    check (¬MEM (src_id_opt, fn) cx.stk) "recursion";
    ts <- lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code";
    tup <- lift_option_type (lookup_callable_function cx.in_deploy fn ts) "IntCall lookup_function";
    stup <<- SND tup; args <<- FST stup; sstup <<- SND stup;
    dflts <<- FST sstup; sstup2 <<- SND sstup;
    ret <<- FST $ sstup2; body <<- SND $ sstup2;
    type_check (LENGTH es ≤ LENGTH args ∧
           LENGTH args - LENGTH es ≤ LENGTH dflts) "IntCall args length";
    vs <- eval_exprs cx es;
    needed_dflts <<- DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts;
    cxd <<- cx with stk updated_by CONS (src_id_opt, fn);
    dflt_vs <- eval_exprs cxd needed_dflts;
    (* Use combined type env (may reference types from other modules) *)
    all_tenv <<- get_tenv cx;
    env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs)) "IntCall bind_arguments";
    prev <- get_scopes;
    rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
    cxf <- push_function (src_id_opt, fn) env cx;
    rv <- finally
      (try (do eval_stmts cxf body; return NoneV od) handle_function)
      (pop_function prev);
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return $ Value crv
  od ∧
  eval_exprs cx [] = return [] ∧
  eval_exprs cx (e::es) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    vs <- eval_exprs cx es;
    return $ v::vs
  od
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (INR (INR (INR (cx, es))))))))
    => exprs_bound (remcode cx) es
  | INR (INR (INR (INR (INR (INR (INR (INL (cx, e))))))))
    => expr_bound (remcode cx) e
  | INR (INR (INR (INR (INR (INR (INL (cx, nm, body, vs)))))))
    => 1 + LENGTH vs + (LENGTH vs) * (stmts_bound (remcode cx) body)
  | INR (INR (INR (INR (INR (INL (cx, t))))))
    => base_target_bound (remcode cx) t
  | INR (INR (INR (INR (INL (cx, gs)))))
    => targets_bound (remcode cx) gs
  | INR (INR (INR (INL (cx, g))))
    => target_bound (remcode cx) g
  | INR (INR (INL (cx, it)))
    => iterator_bound (remcode cx) it
  | INR (INL (cx, ss)) => stmts_bound (remcode cx) ss
  | INL (cx, s) => stmt_bound (remcode cx) s)’
  \\ reverse(rw[bound_def, MAX_DEF, MULT, IS_SOME_EXISTS]) \\ gvs[]
  >- (
    gvs[compatible_bound_def, check_def, type_check_def, assert_def]
    \\ qmatch_goalsub_abbrev_tac`(LENGTH vs) * x`
    \\ irule LESS_EQ_LESS_TRANS
    \\ qexists_tac`LENGTH vs + n * x + 1` \\ simp[]
    \\ PROVE_TAC[MULT_COMM, LESS_MONO_MULT])
  >- (
    gvs[check_def, type_check_def, assert_def]
    \\ gvs[push_function_def, return_def]
    \\ gvs[lift_option_def, lift_option_type_def, CaseEq"option", CaseEq"prod", option_CASE_rator,
           raise_def, return_def]
    \\ gvs[remcode_def, get_module_code_def, ADELKEY_def]
    \\ qpat_x_assum`OUTR _ _ = _`kall_tac
    \\ gvs[CaseEq"option"]
    \\ simp[bound_def]
    \\ qmatch_asmsub_rename_tac`lookup_callable_function _ fn ts = SOME (_, args, dflts, ret, body)`
    \\ Cases_on`(dflts, body) = ([], [])`
    >- gvs[bound_def]
    \\ drule_all_then(qspec_then`src_id_opt`strip_assume_tac)
         lookup_callable_function_eq_ALOOKUP_module_fns
    \\ drule_at_then Any drule ALOOKUP_FLAT_MAP_module_fns
    \\ qmatch_goalsub_abbrev_tac`ALOOKUP (FILTER P ls) k`
    \\ `P = λ(k,v). ¬MEM k cx.stk` by simp[Abbr`P`,FUN_EQ_THM,FORALL_PROD]
    \\ simp[ALOOKUP_FILTER, FILTER_FILTER, Abbr`k`]
    \\ simp[LAMBDA_PROD]
    \\ qmatch_goalsub_abbrev_tac`exprs_bound fts (DROP n dflts)`
    \\ qspecl_then[`fts`,`n`,`dflts`]mp_tac exprs_bound_DROP
    \\ simp[])
  \\ TRY (
    rename1`builtin_args_length_ok Len`
    \\ gvs[builtin_args_length_ok_def, check_def, type_check_def, type_check_def, assert_def,
           LENGTH_EQ_NUM_compute, bound_def] \\ NO_TAC)
  \\ gvs[check_def, type_check_def, assert_def]
  \\ gvs[push_function_def, return_def]
  \\ gvs[lift_option_def, lift_option_type_def, CaseEq"option", CaseEq"prod", option_CASE_rator,
         raise_def, return_def]
  \\ gvs[remcode_def, get_module_code_def, ADELKEY_def]
  \\ qpat_x_assum`OUTR _ _ = _`kall_tac
  \\ gvs[CaseEq"option"]
  (* Use lookup_callable_function_eq_ALOOKUP_module_fns to get ALOOKUP result *)
  \\ qmatch_asmsub_rename_tac`lookup_callable_function _ fn ts = SOME (_, args, dflts, ret, body)`
  \\ Cases_on`(dflts, body) = ([], [])`
  (* Case 1: body = [] (default constructor) - trivial, bound is 0 *)
  >- gvs[bound_def]
  (* Case 2: body ≠ [] - use the key lemma *)
  \\ drule_all_then(qspec_then`src_id_opt`strip_assume_tac)
       lookup_callable_function_eq_ALOOKUP_module_fns
  \\ drule_at_then Any drule ALOOKUP_FLAT_MAP_module_fns
  \\ qmatch_goalsub_abbrev_tac`ALOOKUP (FILTER P ls) k`
  \\ `P = λ(k,v). ¬MEM k cx.stk` by simp[Abbr`P`,FUN_EQ_THM,FORALL_PROD]
  \\ pop_assum SUBST_ALL_TAC
  \\ simp[ALOOKUP_FILTER]
  \\ rw[FILTER_FILTER,UNCURRY,Abbr`k`]
  \\ simp[LAMBDA_PROD]
End

Theorem eval_exprs_length:
  ∀es cx st vs rt.
  eval_exprs cx es st = (INL vs, rt)
  ⇒ LENGTH vs = LENGTH es
Proof
  Induct \\ rw[evaluate_def, return_def, bind_def]
  \\ gvs[CaseEq"prod", CaseEq"sum"]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

(* Semantics of initial state of a contract after deployment *)

Definition flag_value_def:
  flag_value m n acc [] = StructV $ REVERSE acc ∧
  flag_value m n acc (id::ids) =
  flag_value m (2n*n) ((id,FlagV m n)::acc) ids
End

val () = cv_auto_trans flag_value_def;

(* TODO: propagate errors? *)
Definition force_default_value_def:
  force_default_value env typ =
  case evaluate_type env typ of SOME tv => default_value tv
     | NONE => NoneV
End

(* Initialize immutables for a single module's toplevels *)
Definition initial_immutables_module_def:
  initial_immutables_module env src_id_opt [] acc = acc ∧
  initial_immutables_module env src_id_opt (VariableDecl _ Immutable id typ :: ts) acc =
  (let key = string_to_num id in
   let iv = force_default_value env typ in
     initial_immutables_module env src_id_opt ts
       (update_immutable src_id_opt key iv acc)) ∧
  initial_immutables_module env src_id_opt (_ :: ts) acc =
    initial_immutables_module env src_id_opt ts acc
End

val () = cv_auto_trans initial_immutables_module_def;

(* Initialize immutables for all modules *)
Definition initial_immutables_def:
  initial_immutables env [] = empty_immutables ∧
  initial_immutables env ((src_id_opt, ts) :: rest) =
    initial_immutables_module env src_id_opt ts (initial_immutables env rest)
End

val () = cv_auto_trans initial_immutables_def;

Definition initial_evaluation_context_def:
  initial_evaluation_context srcs layouts tx =
  <| sources := srcs
   ; layouts := layouts
   ; txn := tx
   ; stk := [(NONE, tx.function_name)]
   ; in_deploy := F
   |>
End

val () = cv_auto_trans initial_evaluation_context_def;

Datatype:
  abstract_machine = <|
    sources: (address, (num option, toplevel list) alist) alist
  ; exports: (address, (string, num) alist) alist  (* address -> (func_name -> source_id) *)
  ; immutables: (address, module_immutables) alist
  ; accounts: evm_accounts
  ; layouts: (address, storage_layout # storage_layout) alist  (* (storage, transient) *)
  ; tStorage: transient_storage
  |>
End

Definition initial_machine_state_def:
  initial_machine_state : abstract_machine = <|
    sources := []
  ; exports := []
  ; immutables := []
  ; accounts := empty_accounts
  ; layouts := []
  ; tStorage := empty_transient_storage
  |>
End

Definition initial_state_def:
  initial_state (am: abstract_machine) scs : evaluation_state =
  <| accounts := am.accounts
   ; immutables := am.immutables
   ; logs := []
   ; scopes := scs
   ; tStorage := am.tStorage
   |>
End

val () = cv_auto_trans initial_state_def;

Definition abstract_machine_from_state_def:
  abstract_machine_from_state srcs exps layouts (st: evaluation_state) =
  <| sources := srcs
   ; exports := exps
   ; immutables := st.immutables
   ; accounts := st.accounts
   ; layouts := layouts
   ; tStorage := st.tStorage
   |> : abstract_machine
End

val () = cv_auto_trans abstract_machine_from_state_def;

(* Top-level entry-points into the semantics: loading (deploying) a contract,
* and calling its external functions *)

Definition constants_env_def:
  constants_env _ _ [] acc = SOME acc ∧
  constants_env cx am ((VariableDecl vis (Constant e) id typ)::ts) acc =
    (case FST $ eval_expr cx e (initial_state am [acc]) of
     | INL (Value v) => constants_env cx am ts $
                        acc |+ (string_to_num id, v)
     | _ => NONE) ∧
  constants_env cx am (t::ts) acc = constants_env cx am ts acc
End

(* Merge a constants fmap into the immutables for a given module *)
Definition merge_constants_def:
  merge_constants addr src_id_opt cenv (am: abstract_machine) =
    let imms = case ALOOKUP am.immutables addr of
                 SOME m => m | NONE => empty_immutables in
    let src_imms = get_source_immutables src_id_opt imms in
    let merged = FUNION cenv src_imms in
    let imms' = set_source_immutables src_id_opt merged imms in
    am with immutables updated_by
      (λal. (addr, imms') :: ADELKEY addr al)
End

val () = cv_auto_trans merge_constants_def;

(* Evaluate constants for all modules and merge into am.immutables *)
Definition evaluate_all_constants_def:
  evaluate_all_constants cx am addr [] = SOME am ∧
  evaluate_all_constants cx am addr ((src_id_opt, ts) :: rest) =
    case constants_env cx am ts FEMPTY of
    | NONE => NONE
    | SOME cenv =>
        let am' = merge_constants addr src_id_opt cenv am in
        evaluate_all_constants cx am' addr rest
End

Definition send_call_value_def:
  send_call_value mut cx =
  let n = cx.txn.value in
  if n = 0 then return () else do
    type_check (mut = Payable) "not Payable";
    transfer_value cx.txn.sender cx.txn.target n
  od
End

val () = send_call_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR]
  |> cv_auto_trans;

Definition evaluate_defaults_def:
  evaluate_defaults cx am [] = SOME [] ∧
  evaluate_defaults cx am (e::es) =
    (case FST $ eval_expr cx e (initial_state am []) of
     | INL (Value v) =>
         (case evaluate_defaults cx am es of
          | SOME vs => SOME (v :: vs)
          | NONE => NONE)
     | _ => NONE)
End

Definition call_external_function_def:
  call_external_function am cx mut ts all_mods args dflts vals body ret =
  let all_tenv = type_env_all_modules all_mods in
  let n_provided = LENGTH vals in
  let n_expected = LENGTH args in
  let n_missing = n_expected - n_provided in
  if n_provided > n_expected ∨ n_missing > LENGTH dflts then
    (INR $ Error (RuntimeError "call args length"), am)
  else
  let needed_dflts = DROP (LENGTH dflts - n_missing) dflts in
  case evaluate_defaults cx am needed_dflts of
  | NONE => (INR $ Error (RuntimeError "call evaluate_defaults"), am)
  | SOME dflt_vs =>
  case bind_arguments all_tenv args (vals ++ dflt_vs)
  of NONE => (INR $ Error (RuntimeError "call bind_arguments"), am)
   | SOME env =>
  (case (if cx.in_deploy then evaluate_all_constants cx am cx.txn.target all_mods
         else SOME am)
   of NONE => (INR $ Error (RuntimeError "call constants_env"), am)
    | SOME am =>
   let st = initial_state am [env] in
   let srcs = am.sources in
   let exps = am.exports in
   let layouts = am.layouts in
   let (res, st) =
     (case do send_call_value mut cx; eval_stmts cx body od st
      of
       | (INL (), st) => (INL NoneV, abstract_machine_from_state srcs exps layouts st)
       | (INR (ReturnException v), st) =>
           (let am = abstract_machine_from_state srcs exps layouts st in
            case evaluate_type all_tenv ret
            of NONE => (INR (Error (RuntimeError "eval ret")), am)
             | SOME tv =>
            case safe_cast tv v
            of NONE => (INR (Error (RuntimeError "ext cast ret")), am)
             | SOME v => (INL v, am))
       | (INR e, st) => (INR e, abstract_machine_from_state srcs exps layouts st)) in
    (res, st (* transient storage cleared separately via ClearTransientStorage action *)))
End

(* Lookup function, checking exports first for external calls *)
Definition lookup_exported_function_def:
  lookup_exported_function cx am func_name =
    (* First check if this function is exported from another module *)
    case ALOOKUP am.exports cx.txn.target of
      NONE => (* No exports for this contract, use main module *)
        (case get_self_code cx of
           SOME ts => lookup_function NONE func_name External ts
         | NONE => NONE)
    | SOME export_map =>
        (case ALOOKUP export_map func_name of
           SOME src_id => (* Function is exported from module src_id *)
             (case get_module_code cx (SOME src_id) of
                SOME ts => lookup_function (SOME src_id) func_name External ts
              | NONE => NONE)
         | NONE => (* Not in exports, try main module *)
             (case get_self_code cx of
                SOME ts => lookup_function NONE func_name External ts
              | NONE => NONE))
End

(* Find which module a function is in (for exported functions) *)
Definition find_function_module_def:
  find_function_module cx am func_name =
    case ALOOKUP am.exports cx.txn.target of
      NONE => NONE  (* Use main module *)
    | SOME export_map =>
        ALOOKUP export_map func_name  (* Returns SOME src_id if exported *)
End

Definition call_external_def:
  call_external am tx =
  let cx = initial_evaluation_context am.sources am.layouts tx in
  (* Get all modules for this contract (needed for combined type_env) *)
  case ALOOKUP am.sources tx.target of
    NONE => (INR $ Error (RuntimeError "call get sources"), am)
  | SOME all_mods =>
  (* Determine which module to use for type environment *)
  let src_id_opt = find_function_module cx am tx.function_name in
  case (case src_id_opt of
          NONE => get_self_code cx
        | SOME src_id => get_module_code cx (SOME src_id))
  of NONE => (INR $ Error (RuntimeError "call get_self_code"), am)
   | SOME ts =>
  case lookup_exported_function cx am tx.function_name
  of NONE => (INR $ Error (RuntimeError "call lookup_function"), am)
   | SOME (mut, args, dflts, ret, body) =>
       call_external_function am cx mut ts all_mods args dflts tx.args body ret
End

Definition load_contract_def:
  load_contract am tx mods exps =
  let addr = tx.target in
  let ts = case ALOOKUP mods NONE of SOME ts => ts | NONE => [] in
  let tenv = type_env_all_modules mods in
  let imms = initial_immutables tenv mods in
  let am = am with <| immutables updated_by CONS (addr, imms);
                      exports updated_by CONS (addr, exps) |> in
  case lookup_function NONE tx.function_name Deploy ts of
     | NONE => INR $ Error (RuntimeError "no constructor")
     | SOME (mut, args, dflts, ret, body) =>
       let cx = (initial_evaluation_context ((addr,mods)::am.sources) am.layouts tx)
                with in_deploy := T in
       case call_external_function am cx mut ts mods args dflts tx.args body ret
         of (INR e, _) => INR e
       (* TODO: update balances on return *)
          | (_, am) => INL (am with sources updated_by CONS (addr, mods))
End
