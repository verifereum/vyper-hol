(* Definition-level audit only: these equations do not claim that a hash
   collision can be embedded in a body frame. *)
Theory bodyPtrBopSemanticProbe
Ancestors
  vyperValueOperation compileEnv supportedExprForms allocLimits

Theorem bop_probe_bytes_eq:
  evaluate_binop u tv Eq (BytesV xs) (BytesV ys) =
  INL (BoolV (xs = ys))
Proof
  simp[evaluate_binop_def]
QED

Theorem bop_probe_string_eq:
  evaluate_binop u tv Eq (StringV xs) (StringV ys) =
  INL (BoolV (xs = ys))
Proof
  simp[evaluate_binop_def]
QED

Theorem bop_probe_dynamic_hash_dispatch:
  is_bytestring_type (BaseT (BytesT (Dynamic n))) /\
  is_bytestring_type (BaseT (StringT n))
Proof
  simp[is_bytestring_type_def]
QED

Theorem bop_probe_supported_dynamic_eq:
  ~supported_binop Eq (BaseT (BytesT (Dynamic n))) rhs lb ne /\
  ~supported_binop Eq (BaseT (StringT n)) rhs lb ne
Proof
  simp[supported_binop_def, supportedTypesTheory.supported_word_type_def]
QED

(* 33-byte payloads already exceed the 256-bit hash range. This checks
   only the local typing/allocation boundary, not a complete body frame. *)
Theorem bop_probe_33_byte_literal:
  LENGTH bs = 33 ==>
  well_typed_literal (BaseT (BytesT (Dynamic 33))) (BytesL bs) /\
  literal_alloc_ok (BytesL bs)
Proof
  simp[vyperTypeSystemTheory.well_typed_literal_def,
       vyperValueTheory.compatible_bound_def, literal_alloc_ok_def,
       vfmConstantsTheory.word_size_def]
QED
