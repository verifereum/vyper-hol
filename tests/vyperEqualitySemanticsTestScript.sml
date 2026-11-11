Theory vyperEqualitySemanticsTest
Ancestors vyperValueOperation vyperValue vyperAST vyperMisc

(* Symbolic operands distinguish hash equality without a concrete collision. *)
Theorem string_equality_hash_test:
  evaluate_binop u (BaseTV (StringT n)) (if neq then NotEq else Eq)
    (StringV a) (StringV b) =
  INL (BoolV ((Keccak_256_w64 (MAP n2w_o_ORD a) =
               Keccak_256_w64 (MAP n2w_o_ORD b)) <> neq))
Proof
  Cases_on `neq` >> simp[evaluate_binop_def, binop_negate_def]
QED

Theorem dynamic_bytes_equality_hash_test:
  evaluate_binop u (BaseTV (BytesT (Dynamic n))) (if neq then NotEq else Eq)
    (BytesV a) (BytesV b) =
  INL (BoolV ((Keccak_256_w64 a = Keccak_256_w64 b) <> neq))
Proof
  Cases_on `neq` >> simp[evaluate_binop_def, binop_negate_def]
QED

Theorem fixed_bytes_equality_exact_test:
  evaluate_binop u (BaseTV (BytesT (Fixed n))) (if neq then NotEq else Eq)
    (BytesV a) (BytesV b) = INL (BoolV ((a = b) <> neq))
Proof
  Cases_on `neq` >> simp[evaluate_binop_def, binop_negate_def]
QED

Theorem address_equality_exact_test:
  evaluate_binop u (BaseTV AddressT) (if neq then NotEq else Eq)
    (BytesV a) (BytesV b) = INL (BoolV ((a = b) <> neq))
Proof
  Cases_on `neq` >> simp[evaluate_binop_def, binop_negate_def]
QED
