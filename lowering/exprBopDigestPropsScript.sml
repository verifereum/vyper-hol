(* Shared source boundary for digest comparisons; no hash injectivity assumed. *)
Theory exprBopDigestProps
Ancestors
  exprBopSimDefs vyperTypeBytesCrypto venomMemProps
  vyperContext vyperValueOperation vyperTyping vyperMisc byte words

Theorem comparison_digest_eq:
  (word_of_bytes T (0w:bytes32) (Keccak_256_w64 xs) =
   word_of_bytes T (0w:bytes32) (Keccak_256_w64 ys)) <=>
  Keccak_256_w64 xs = Keccak_256_w64 ys
Proof
  eq_tac >- (strip_tac >>
    irule (word_of_bytes_be_inj |> INST_TYPE [alpha |-> ``:256``]) >>
    simp[LENGTH_Keccak_256_w64, dividesTheory.compute_divides]) >>
  simp[]
QED

Theorem comparison_source_result:
  (bop = Eq \/ bop = NotEq) /\
  (?cap. ty = BaseT (BytesT (Dynamic cap)) \/ ty = BaseT (StringT cap)) /\
  evaluate_type tenv ty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  ((?bs. v1 = BytesV bs /\ d1 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
   (?str. v1 = StringV str /\ d1 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) /\
  ((?bs. v2 = BytesV bs /\ d2 = word_of_bytes T (0w:bytes32) (Keccak_256_w64 bs)) \/
   (?str. v2 = StringV str /\ d2 = word_of_bytes T (0w:bytes32)
       (Keccak_256_w64 (MAP (n2w o ORD) str)))) ==>
  !ss. bop_result cx ann bop [ty; ty] v1 v2 ss =
    INL (BoolV (if bop = Eq then d1 = d2 else d1 <> d2))
Proof
  strip_tac >> gvs[vyperValueTheory.evaluate_type_def, value_has_type_def] >>
  gvs[exprBopSimDefsTheory.bop_result_def, evaluate_builtin_def,
      vyperValueOperationTheory.evaluate_binop_def,
      vyperValueOperationTheory.binop_negate_def, comparison_digest_eq,
      vyperValueTheory.evaluate_type_def] >>
  simp[vyperMiscTheory.n2w_o_ORD_eq]
QED
