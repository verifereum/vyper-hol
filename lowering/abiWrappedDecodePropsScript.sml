Theory abiWrappedDecodeProps
Ancestors vyperABIValid vyperContext vyperTypeABI contractABI vyperABI list
Libs wordsLib

(* Exact Vyper-value roundtrip is not a valid general prerequisite: fixed
   array encoding forgets sparse default entries. *)
Theorem fixed_array_decode_normalizes_sparse_defaults:
  let ty = ArrayT (BaseT (UintT 256)) (Fixed 1) in
  let v = ArrayV (SArrayV [(0, IntV 0)]) in
    evaluate_abi_encode_bytes FEMPTY ty v = INL (REPLICATE 32 0w) /\
    evaluate_abi_decode FEMPTY ty (REPLICATE 32 0w) =
      INL (ArrayV (SArrayV []))
Proof
  EVAL_TAC >> simp[vyperValueTheory.enumerate_static_array_def]
QED

(* A source decoder boundary, independent of canonical encoding. *)
Theorem evaluate_abi_decode_normalized:
  vyper_valid_enc env ty bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME nv ==>
  evaluate_abi_decode env ty bs = INL nv
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def]
QED

(* All codec and size-window obligations are deliberately explicit. *)
Theorem evaluate_abi_decode_canonical_normalized:
  has_type (vyper_to_abi_type env ty) av /\
  LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  static_length (vyper_to_abi_type env ty) <=
    LENGTH (enc (vyper_to_abi_type env ty) av) /\
  LENGTH (enc (vyper_to_abi_type env ty) av) <= vyper_abi_size_bound env ty /\
  abi_to_vyper env ty av = SOME nv ==>
  evaluate_abi_decode env ty (enc (vyper_to_abi_type env ty) av) = INL nv
Proof
  strip_tac >>
  `dec (vyper_to_abi_type env ty) (enc (vyper_to_abi_type env ty) av) = av` by
    (drule_all (cj 1 dec_enc) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  irule evaluate_abi_decode_normalized >>
  simp[vyper_valid_enc_def, vyper_strict_enc_def] >>
  metis_tac[enc_valid, APPEND_NIL]
QED

(* Singleton conversion does not require codec or typing premises. *)
Theorem abi_to_vyper_singleton_tuple:
  abi_to_vyper env (TupleT [ty]) (ListV [av]) =
    OPTION_MAP (\v. ArrayV (TupleV [v])) (abi_to_vyper env ty av)
Proof
  Cases_on `abi_to_vyper env ty av` >> simp[abi_to_vyper_def]
QED

(* These interfaces apply to arbitrary buffers, including noncanonical ones. *)
Theorem evaluate_type_builtin_abi_decode_wrapped_success:
  unwrap /\ needs_external_call_wrap ty /\
  evaluate_abi_decode (get_tenv cx) (TupleT [ty]) bs =
    INL (ArrayV (TupleV [v])) ==>
  evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v
Proof
  strip_tac >> simp[evaluate_type_builtin_def]
QED

Theorem evaluate_type_builtin_abi_decode_unwrapped_success:
  ~(unwrap /\ needs_external_call_wrap ty) /\
  evaluate_abi_decode (get_tenv cx) ty bs = INL v ==>
  evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v
Proof
  strip_tac >> simp[evaluate_type_builtin_def]
QED

Theorem evaluate_type_builtin_abi_decode_wrapped_error:
  unwrap /\ needs_external_call_wrap ty /\
  evaluate_abi_decode (get_tenv cx) (TupleT [ty]) bs = INR err ==>
  evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] =
    INR (RuntimeError err)
Proof
  strip_tac >> simp[evaluate_type_builtin_def]
QED

Theorem evaluate_type_builtin_abi_decode_unwrapped_error:
  ~(unwrap /\ needs_external_call_wrap ty) /\
  evaluate_abi_decode (get_tenv cx) ty bs = INR err ==>
  evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] =
    INR (RuntimeError err)
Proof
  strip_tac >> simp[evaluate_type_builtin_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_WRAPPED_DECODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI wrapped decode not kernel closed: " ^ n)
  end) (DB.thms "abiWrappedDecodeProps");
