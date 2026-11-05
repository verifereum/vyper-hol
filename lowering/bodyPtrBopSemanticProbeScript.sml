(* Definition-level audit only: these equations do not claim that a hash
   collision can be embedded in a body frame. *)
Theory bodyPtrBopSemanticProbe
Ancestors
  vyperValueOperation compileEnv supportedExprForms

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
