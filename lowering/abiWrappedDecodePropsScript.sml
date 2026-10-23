Theory abiWrappedDecodeProps
Ancestors vyperABIValid vyperContext vyperTypeABI contractABI
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
