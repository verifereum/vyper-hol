Theory bodyPtrIfExpWideningAudit
Ancestors supportedTypes context valueEncoding vyperTypeArgFits

(* Equal padded size does not imply equality of bytestring bounds. *)
Theorem ifexp_widening_padding_bucket:
  arg_type_fits (BaseT (StringT 1)) (BaseT (StringT 32)) /\
  type_memory_size (BaseTV (StringT 1)) = 64 /\
  type_memory_size (BaseTV (StringT 32)) = 64 /\
  type_memory_size (BaseTV (StringT 33)) = 96 /\
  arg_type_fits (BaseT (BytesT (Dynamic 1))) (BaseT (BytesT (Dynamic 33))) /\
  type_memory_size (BaseTV (BytesT (Dynamic 1))) = 64 /\
  type_memory_size (BaseTV (BytesT (Dynamic 33))) = 96
Proof
  EVAL_TAC
QED

Theorem ifexp_widening_tuple_same_bucket:
  !ce. supported_value_type [] (TupleT [BaseT (StringT 1); BaseT BoolT]) /\
    arg_type_fits (TupleT [BaseT (StringT 1); BaseT BoolT])
                  (TupleT [BaseT (StringT 32); BaseT BoolT]) /\
    same_memory_layout ce (TupleT [BaseT (StringT 1); BaseT BoolT])
                          (TupleT [BaseT (StringT 32); BaseT BoolT]) /\
    type_memory_size (TupleTV [BaseTV (StringT 1); BaseTV BoolT]) = 96 /\
    type_memory_size (TupleTV [BaseTV (StringT 32); BaseTV BoolT]) = 96
Proof
  gen_tac >> EVAL_TAC
QED

Theorem ifexp_widening_dynamic_word_sizes:
  !n m. type_memory_size (ArrayTV (BaseTV BoolT) (Dynamic n)) = 32 + 32 * n /\
    (type_memory_size (ArrayTV (BaseTV BoolT) (Dynamic n)) =
     type_memory_size (ArrayTV (BaseTV BoolT) (Dynamic m)) <=> n = m)
Proof
  simp[type_memory_size_def]
QED

Theorem ifexp_widening_fixed_word_sizes:
  !n. type_memory_size (ArrayTV (BaseTV BoolT) (Fixed n)) = 32 * n
Proof
  simp[type_memory_size_def]
QED
