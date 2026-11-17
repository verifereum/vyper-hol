Theory vyperBytesBitwiseTest
Ancestors
  vyperTypeSystem vyperValueOperation vyperValue vyperAST byte words list
Libs
  wordsLib intLib

(* VYPER_PIN 577d2534, O1 experimental codegen, executed in Py-EVM. *)
Theorem bytes_bitwise_pin_outputs:
  (!m. MEM m [1;4;20;31;32] ==>
    evaluate_binop (Unsigned 0) NoneTV And
      (BytesV (REPLICATE m 0xa5w)) (BytesV (REPLICATE m 0x3cw)) =
      INL (BytesV (REPLICATE m 0x24w))) /\
  (!m. MEM m [1;4;20;31;32] ==>
    evaluate_binop (Unsigned 0) NoneTV Or
      (BytesV (REPLICATE m 0xa5w)) (BytesV (REPLICATE m 0x3cw)) =
      INL (BytesV (REPLICATE m 0xbdw))) /\
  (!m. MEM m [1;4;20;31;32] ==>
    evaluate_binop (Unsigned 0) NoneTV XOr
      (BytesV (REPLICATE m 0xa5w)) (BytesV (REPLICATE m 0x3cw)) =
      INL (BytesV (REPLICATE m 0x99w)))
Proof
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem bytes32_shift_pin_outputs:
  evaluate_binop (Unsigned 0) NoneTV ShL
    (BytesV (0x81w :: REPLICATE 30 0w ++ [3w])) (IntV 1) =
    INL (BytesV (2w :: REPLICATE 30 0w ++ [6w])) /\
  evaluate_binop (Unsigned 0) NoneTV ShR
    (BytesV (0x81w :: REPLICATE 30 0w ++ [3w])) (IntV 1) =
    INL (BytesV ([0x40w;0x80w] ++ REPLICATE 29 0w ++ [1w])) /\
  evaluate_binop (Unsigned 0) NoneTV ShL
    (BytesV (0x81w :: REPLICATE 30 0w ++ [3w])) (IntV 255) =
    INL (BytesV (0x80w :: REPLICATE 31 0w)) /\
  evaluate_binop (Unsigned 0) NoneTV ShR
    (BytesV (0x81w :: REPLICATE 30 0w ++ [3w])) (IntV 255) =
    INL (BytesV (REPLICATE 31 0w ++ [1w])) /\
  (!bop n. MEM bop [ShL;ShR] /\ MEM n [256;257;2 ** 256 - 1] ==>
    evaluate_binop (Unsigned 0) NoneTV bop
      (BytesV (0x81w :: REPLICATE 30 0w ++ [3w])) (IntV (&n)) =
    INL (BytesV (REPLICATE 32 0w)))
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem bytes_bitwise_checker_pairs:
  (!bop m ann rhs. MEM bop [And;Or;XOr] ==>
    (well_typed_binop ann bop (BaseT (BytesT (Fixed m))) rhs <=>
       ann = BaseT (BytesT (Fixed m)) /\ rhs = ann)) /\
  (!bop m ann rhs. MEM bop [ShL;ShR] ==>
    (well_typed_binop ann bop (BaseT (BytesT (Fixed m))) rhs <=>
       m = 32 /\ ann = BaseT (BytesT (Fixed 32)) /\ is_int_type rhs))
Proof
  simp[] >> rpt strip_tac >> gvs[well_typed_binop_def] >>
  eq_tac >> strip_tac >> gvs[]
QED

(* The pin annotates the literal in a << 4 as int8, but rejects a signed
   runtime amount. The operand-domain check makes this distinction. *)
Theorem bytes_shift_amount_domain:
  (!bop. MEM bop [ShL;ShR] ==>
    builtin_operands_ok (BaseT (BytesT (Fixed 32))) (Bop bop)
      [Name (BaseT (BytesT (Fixed 32))) "a";
       Literal (BaseT (IntT 8)) (IntL 4)] /\
    ~builtin_operands_ok (BaseT (BytesT (Fixed 32))) (Bop bop)
      [Name (BaseT (BytesT (Fixed 32))) "a";
       Name (BaseT (IntT 256)) "n"])
Proof
  simp[] >> rpt strip_tac >> gvs[builtin_operands_ok_def,
    shift_amount_ok_def, nonneg_int_literal_def, int_literal_value_def,
    expr_type_def]
QED

Theorem bytes_bitwise_mismatched_values:
  (!bop. MEM bop [And;Or;XOr] ==>
    evaluate_binop (Unsigned 0) NoneTV bop (BytesV [1w])
      (BytesV [1w;2w]) = INR (TypeError "binop")) /\
  evaluate_binop (Unsigned 0) NoneTV ShL (BytesV [1w]) (IntV 1) =
    INR (TypeError "binop") /\
  evaluate_binop (Unsigned 0) NoneTV ShR (BytesV [1w]) (IntV 1) =
    INR (TypeError "binop")
Proof
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED
