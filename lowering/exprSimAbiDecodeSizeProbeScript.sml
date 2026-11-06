Theory exprSimAbiDecodeSizeProbe
Ancestors compileEnv arithmetic words vyperAST list

(* Diagnostic family only: not a counterexample to expression simulation. *)
Definition abi_decode_size_probe_type_def:
  abi_decode_size_probe_type 0 = BaseT (BytesT (Dynamic 1)) /\
  abi_decode_size_probe_type (SUC k) = TupleT [abi_decode_size_probe_type k]
End

Theorem abi_decode_size_probe_dynamic:
  !k. is_abi_dynamic sf (abi_decode_size_probe_type k)
Proof
  Induct >> simp[abi_decode_size_probe_type_def, Once is_abi_dynamic_def]
QED

Theorem abi_decode_size_probe_memory:
  !k. type_memory_bytes ce (abi_decode_size_probe_type k) = 64
Proof
  Induct >> simp[abi_decode_size_probe_type_def, Once type_memory_bytes_def]
QED

Theorem abi_decode_size_probe_abi:
  !k. abi_size_bound sf (abi_decode_size_probe_type k) = 64 + 32 * k
Proof
  Induct >> simp[abi_decode_size_probe_type_def, Once abi_size_bound_def,
    abi_decode_size_probe_dynamic, abi_embedded_static_size_def]
QED

Theorem abi_decode_size_probe_numerical_counterexample:
  type_memory_bytes ce (abi_decode_size_probe_type (2 ** 256)) < 2 ** 64 /\
  ~(abi_size_bound sf (abi_decode_size_probe_type (2 ** 256)) < dimword (:256))
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[abi_decode_size_probe_memory, abi_decode_size_probe_abi, dimword_def]
QED
