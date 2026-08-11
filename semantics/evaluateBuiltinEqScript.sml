Theory evaluateBuiltinEq
Ancestors
  vyperContext

(* ===== Old definition of evaluate_builtin =====
   evaluate_builtin was rewritten from a multi-clause pattern-matching
   definition into a single case-expression definition so that it could
   be translated by cv_auto_trans.  This theory records the old form and
   proves the two definitions agree on all inputs.
   TOP-LEVEL: evaluate_builtin_old_def, evaluate_builtin_old_eq_evaluate_builtin
   Helper: none
*)

Definition evaluate_builtin_old_def:
  evaluate_builtin_old cx _ ty Not [BoolV b] = INL (BoolV (¬b)) ∧
  evaluate_builtin_old cx _ ty Not [IntV i] =
    (case type_to_int_bound ty of
       SOME u =>
         if is_Unsigned u ∧ 0 ≤ i then
           INL (IntV (&(2 ** int_bound_bits u) - 1 - i))
         else INR (TypeError "signed Not")
     | NONE => INR (TypeError "Not type")) ∧
  evaluate_builtin_old cx _ ty Not [FlagV n] =
    (case evaluate_type (get_tenv cx) ty of
       SOME (FlagTV m) => INL $ FlagV $
         w2n $ (~((n2w n):bytes32)) && ~(~(0w:bytes32) << m)
     | _ => INR (TypeError "Not flag type")) ∧
  evaluate_builtin_old cx _ ty Neg [IntV i] =
    (case type_to_int_bound ty
     of SOME u =>
       if within_int_bound u i then bounded_int_op u (-i)
       else INR (RuntimeError "Neg operand bound")
      | NONE => INR (TypeError "Neg type")) ∧
  evaluate_builtin_old cx _ _ Neg [DecimalV i] = bounded_decimal_op (-i) ∧
  evaluate_builtin_old cx _ ty Abs [IntV i] =
    (case type_to_int_bound ty
     of SOME u => bounded_int_op u (ABS i)
      | NONE => INR (TypeError "Abs type")) ∧
  evaluate_builtin_old cx _ _ Abs [DecimalV i] = bounded_decimal_op (ABS i) ∧
  evaluate_builtin_old cx _ _ Keccak256 [BytesV ls] = INL $ BytesV $
    Keccak_256_w64 ls ∧
  evaluate_builtin_old cx _ _ Keccak256 [StringV s] = INL $ BytesV $
    Keccak_256_w64 (MAP (n2w o ORD) s) ∧
  (* TODO(semantic-limitation): BytesV bounds are not validated before Keccak256. *)
  evaluate_builtin_old cx _ _ Sha256 [BytesV ls] = INL $ BytesV $
    word_to_bytes (SHA_256_bytes ls : bytes32) T ∧
  evaluate_builtin_old cx _ _ Sha256 [StringV s] = INL $ BytesV $
    word_to_bytes (SHA_256_bytes (MAP (n2w o ORD) s) : bytes32) T ∧
  evaluate_builtin_old cx _ _ (Uint2Str n) [IntV i] =
    INL $ StringV (num_to_dec_string (Num i)) ∧
  evaluate_builtin_old cx _ _ (AsWeiValue dn) [v] = evaluate_as_wei_value dn v ∧
  evaluate_builtin_old cx _ _ AddMod [IntV i1; IntV i2; IntV i3] =
    (if i3 = 0 then INR (RuntimeError "AddMod division by zero")
     else INL $ IntV $ &((Num i1 + Num i2) MOD Num i3)) ∧
  evaluate_builtin_old cx _ _ MulMod [IntV i1; IntV i2; IntV i3] =
    (if i3 = 0 then INR (RuntimeError "MulMod division by zero")
     else INL $ IntV $ &((Num i1 * Num i2) MOD Num i3)) ∧
  evaluate_builtin_old cx _ _ PowMod256 [IntV base; IntV exp] =
    INL $ IntV $ &(vfmExecution$modexp (Num base) (Num exp) (2 ** 256) 1) ∧
  evaluate_builtin_old cx _ _ Floor [DecimalV i] =
    INL $ IntV (i / 10000000000) ∧
  evaluate_builtin_old cx _ _ Ceil [DecimalV i] =
    INL $ IntV ((i + 9999999999) / 10000000000) ∧
  evaluate_builtin_old cx _ ty (Bop bop) [v1; v2] =
    (let u = case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0 in
     let tv = case evaluate_type (get_tenv cx) ty of SOME tv => tv | NONE => NoneTV in
       evaluate_binop u tv bop v1 v2) ∧
  evaluate_builtin_old cx _ _ (Env Sender) [] = INL $ AddressV cx.txn.sender ∧
  evaluate_builtin_old cx _ _ (Env SelfAddr) [] = INL $ AddressV cx.txn.target ∧
  evaluate_builtin_old cx _ _ (Env ValueSent) [] = INL $ IntV &cx.txn.value ∧
  evaluate_builtin_old cx _ _ (Env TimeStamp) [] = INL $ IntV &cx.txn.time_stamp ∧
  evaluate_builtin_old cx _ _ (Env BlockNumber) [] = INL $ IntV &cx.txn.block_number ∧
evaluate_builtin_old cx _ _ (Env BlobBaseFee) [] = INL $ IntV &cx.txn.blob_base_fee ∧
evaluate_builtin_old cx _ _ (Env GasPrice) [] = INL $ IntV &cx.txn.gas_price ∧
evaluate_builtin_old cx _ _ (Env ChainId) [] = INL $ IntV &cx.txn.chain_id ∧
evaluate_builtin_old cx _ _ (Env Coinbase) [] = INL $ AddressV cx.txn.coinbase ∧
evaluate_builtin_old cx _ _ (Env GasLimit) [] = INL $ IntV &cx.txn.gas_limit ∧
evaluate_builtin_old cx _ _ (Env BaseFee) [] = INL $ IntV &cx.txn.base_fee ∧
evaluate_builtin_old cx _ _ (Env PrevRandao) [] = INL $ IntV &cx.txn.prev_randao ∧
evaluate_builtin_old cx _ _ (Env TxOrigin) [] = INL $ AddressV cx.txn.origin ∧
evaluate_builtin_old cx _ _ (Env PrevHash) [] = evaluate_block_hash cx.txn (cx.txn.block_number - 1) ∧
evaluate_builtin_old cx _ _ BlockHash [IntV i] =
evaluate_block_hash cx.txn (Num i) ∧
evaluate_builtin_old cx _ _ BlobHash [IntV i] =
INL $ evaluate_blob_hash cx.txn (Num i) ∧
evaluate_builtin_old cx _ _ (Concat n) vs = evaluate_concat n vs ∧
evaluate_builtin_old cx _ _ (Slice n) [v1; v2; v3] = evaluate_slice v1 v2 v3 n ∧
evaluate_builtin_old cx _ _ (MakeArray to bd) vs =
(case to
 of NONE => INL $ ArrayV $ TupleV vs
  | SOME t =>
    (case evaluate_type (get_tenv cx) t
     of NONE => INR (TypeError "MakeArray type")
      | SOME tv => INL $ ArrayV $ make_array_value tv bd vs)) ∧
evaluate_builtin_old cx acc _ (Acc aop) [BytesV bs] =
(let a = lookup_account (word_of_bytes_be bs) acc in
  INL $ evaluate_account_op aop bs a) ∧
(* method_id: compute keccak256(signature)[:4] - returns 4-byte function selector *)
evaluate_builtin_old cx _ _ MethodId [StringV sig] =
INL $ BytesV (TAKE 4 (Keccak_256_w64 (MAP (n2w o ORD) sig))) ∧
(* Also support Bytes input for method_id *)
evaluate_builtin_old cx _ _ MethodId [BytesV bs] =
INL $ BytesV (TAKE 4 (Keccak_256_w64 bs)) ∧
evaluate_builtin_old cx _ _ ECRecover vs = evaluate_ecrecover vs ∧
evaluate_builtin_old cx _ _ ECAdd vs = evaluate_ecadd vs ∧
evaluate_builtin_old cx _ _ ECMul vs = evaluate_ecmul vs ∧
evaluate_builtin_old _ _ _ _ _ = INR (TypeError "builtin")
End

(* ===== The two definitions agree ===== *)
Theorem evaluate_builtin_old_eq_evaluate_builtin:
!cx acc ty bt vs.
evaluate_builtin_old cx acc ty bt vs = evaluate_builtin cx acc ty bt vs
Proof
  Cases_on `bt` >> Cases_on `vs`
  >> rw[evaluate_builtin_old_def, evaluate_builtin_def]
  (* Residual goals: vs is schematic (free h/t-tail variables at the
     sensitive positions of some clause), so rewrite alone cannot match.
     Case-split the list variables introduced by the case analyses, up to
     depth 4 (the deepest residual clause shape is [v1;v2;v3;v4]++rest),
     re-rewriting after each split so already-matching cases are pruned. *)
  >> rpt (FIRST [Cases_on `e`, Cases_on `item`,
                 Cases_on `h`, Cases_on `h'`, Cases_on `h''`, Cases_on `h'''`,
                 Cases_on `t`, Cases_on `t'`, Cases_on `t''`, Cases_on `t'''`]
          >> fs[evaluate_builtin_old_def, evaluate_builtin_def])
QED

