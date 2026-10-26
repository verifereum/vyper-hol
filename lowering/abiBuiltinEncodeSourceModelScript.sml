(* The source builtin selects the same singleton or tuple payload as lowering. *)
Theory abiBuiltinEncodeSourceModel
Ancestors
  vyperContext vyperABI vyperTypeSystem vyperAST contractABI list arithmetic

Definition abi_builtin_encode_type_def:
  abi_builtin_encode_type ensure tys =
    if LENGTH tys = 1 /\ ~ensure then HD tys else TupleT tys
End

Definition abi_builtin_encode_value_def:
  abi_builtin_encode_value ensure tys vs =
    if LENGTH tys = 1 /\ ~ensure then HD vs else ArrayV (TupleV vs)
End

Theorem abi_builtin_encode_source_single:
  vyper_to_abi (get_tenv cx) ty v = SOME av ==>
  evaluate_type_builtin cx (AbiEncode F method_id) (TupleT [ty]) [v] =
    INL (BytesV (abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) ty) av))
Proof
  simp[evaluate_type_builtin_def, evaluate_abi_encode_bytes_def, needs_external_call_wrap_def, LET_THM]
QED

Theorem abi_builtin_encode_source_tuple:
  ~(~ensure /\ LENGTH tys <= 1) /\ vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av ==>
  evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) vs =
    INL (BytesV (abi_encode_method_id_bytes method_id ++
      enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av))
Proof
  strip_tac >>
  asm_simp_tac (srw_ss()) [evaluate_type_builtin_def, evaluate_abi_encode_bytes_def,
    needs_external_call_wrap_def, LET_THM]
QED

Theorem abi_builtin_encode_source_result:
  tys <> [] /\ LENGTH vs = LENGTH tys /\
  vyper_to_abi (get_tenv cx) (abi_builtin_encode_type ensure tys)
    (abi_builtin_encode_value ensure tys vs) = SOME av ==>
  evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) vs =
    INL (BytesV (abi_encode_method_id_bytes method_id ++
      enc (vyper_to_abi_type (get_tenv cx) (abi_builtin_encode_type ensure tys)) av))
Proof
  Cases_on `ensure` >>
  simp_tac (srw_ss()) [abi_builtin_encode_type_def, abi_builtin_encode_value_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac (srw_ss()) [evaluate_type_builtin_def, evaluate_abi_encode_bytes_def,
    needs_external_call_wrap_def, LET_THM] >>
  Cases_on `tys` >> gvs[] >> rename1 `LENGTH vs = SUC (LENGTH tail_tys)` >>
  Cases_on `tail_tys` >> gvs[LENGTH_EQ_NUM_compute]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_SOURCE_MODEL_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encode source model not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeSourceModel");
