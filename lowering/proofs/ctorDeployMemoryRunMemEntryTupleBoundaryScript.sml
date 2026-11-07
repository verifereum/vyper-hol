Theory ctorDeployMemoryRunMemEntryTupleBoundary
Ancestors
  ctorDeployMemoryRunMemEntryAggregate supportedTypes vyperValue vyperABI
  vyperTyping valueEncoding contractABI list words

Theorem ctor_bool_tuple_replicate_facts:
  !n.
    OPT_MMAP (evaluate_type env) (REPLICATE n (BaseT BoolT)) =
      SOME (REPLICATE n (BaseTV BoolT)) /\
    type_slot_size_list (REPLICATE n (BaseTV BoolT)) = n /\
    values_have_types (REPLICATE n (BaseTV BoolT)) (REPLICATE n (BoolV F)) /\
    tuple_val_wf (REPLICATE n (BoolV F)) (REPLICATE n (BaseTV BoolT)) /\
    vyper_to_abi_list env (REPLICATE n (BaseT BoolT))
      (REPLICATE n (BoolV F)) = SOME (REPLICATE n (NumV 0))
Proof
  Induct >> simp[evaluate_type_def, type_slot_size_def,
    value_has_type_def, val_wf_def, type_memory_size_def]
QED

Theorem ctor_bool_tuple_boundary:
  supported_value_type tops (TupleT (REPLICATE (dimword(:256)) (BaseT BoolT))) /\
  evaluate_type env (TupleT (REPLICATE (dimword(:256)) (BaseT BoolT))) =
    SOME (TupleTV (REPLICATE (dimword(:256)) (BaseTV BoolT))) /\
  value_has_type (TupleTV (REPLICATE (dimword(:256)) (BaseTV BoolT)))
    (ArrayV (TupleV (REPLICATE (dimword(:256)) (BoolV F)))) /\
  val_wf (TupleTV (REPLICATE (dimword(:256)) (BaseTV BoolT)))
    (ArrayV (TupleV (REPLICATE (dimword(:256)) (BoolV F)))) /\
  vyper_to_abi env (TupleT (REPLICATE (dimword(:256)) (BaseT BoolT)))
    (ArrayV (TupleV (REPLICATE (dimword(:256)) (BoolV F)))) =
    SOME (ListV (REPLICATE (dimword(:256)) (NumV 0))) /\
  ~has_type (vyper_to_abi_type env
      (TupleT (REPLICATE (dimword(:256)) (BaseT BoolT))))
    (ListV (REPLICATE (dimword(:256)) (NumV 0)))
Proof
  simp[supported_value_type_def, supported_scalar_type_def,
    supported_word_type_def, supported_string_type_def,
    evaluate_type_def, evaluate_types_OPT_MMAP, type_slot_size_def,
    value_has_type_def, val_wf_def, ctor_bool_tuple_replicate_facts,
    has_type_def, NULL_EQ, dimword_def]
QED
