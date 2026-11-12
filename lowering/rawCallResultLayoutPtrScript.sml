(* Concrete raw_call layouts bridge the checked result stages to source types. *)
Theory rawCallResultLayoutPtr
Ancestors rawCallBufferPtr rawCallShapePtr allocLimits exprSimHypsDefs

Theorem raw_call_bytes_store_capacity:
  LENGTH bs <= n ==>
  val_store_size (BaseTV (BytesT (Dynamic n))) (BytesV bs) <=
    32 + ((n+31) DIV 32)*32
Proof
  simp[exprSimPropsTheory.val_store_size_def, vfmConstantsTheory.word_size_def] >>
  strip_tac >>
  ` (LENGTH bs+31) DIV 32 <= (n+31) DIV 32` by
    (irule arithmeticTheory.DIV_LE_MONOTONE >> simp[]) >> decide_tac
QED

Theorem raw_call_tuple_store_capacity:
  LENGTH bs <= n ==>
  val_store_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV flag;BytesV bs])) <= 64 + ((n+31) DIV 32)*32
Proof
  simp[exprSimPropsTheory.val_store_size_def, valueEncodingTheory.type_memory_size_def,
    vfmConstantsTheory.word_size_def]
QED

Theorem raw_call_bytes_type_capacity:
  type_memory_bytes cenv (lowered_value_type cenv
    (Call (BaseT (BytesT (Dynamic n))) (RawCallTarget flags) es ann)) =
    32 + ((n+31) DIV 32)*32
Proof
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
    compileEnvTheory.type_memory_bytes_def]
QED

Theorem raw_call_tuple_type_capacity:
  type_memory_bytes cenv (lowered_value_type cenv
    (Call (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) (RawCallTarget flags) es ann)) =
    64 + ((n+31) DIV 32)*32
Proof
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
    compileEnvTheory.type_memory_bytes_def]
QED

Theorem raw_call_bytes_pre_capacity:
  expr_body_pre cenv cx env
    (Call (BaseT (BytesT (Dynamic n))) (RawCallTarget flags) es ann) st ==>
  32 + ((n+31) DIV 32)*32 < dimword(:256)
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
    allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def,
    compileEnvTheory.type_memory_bytes_def] >>
  strip_tac >> `2 ** 64 < dimword(:256)` by simp[wordsTheory.dimword_def] >> fs[] >> decide_tac
QED

Theorem raw_call_tuple_pre_capacity:
  expr_body_pre cenv cx env
    (Call (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) (RawCallTarget flags) es ann) st ==>
  64 + ((n+31) DIV 32)*32 < dimword(:256)
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
    allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def,
    compileEnvTheory.type_memory_bytes_def] >>
  strip_tac >> `2 ** 64 < dimword(:256)` by simp[wordsTheory.dimword_def] >> fs[] >> decide_tac
QED
