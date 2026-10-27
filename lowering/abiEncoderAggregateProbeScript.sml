(* Checked aggregate interface diagnostics for the source encoder bridge. *)
Theory abiEncoderAggregateProbe
Ancestors
  abiEncoderSourceBridge abiEncoderInput vyperValue vyperTyping valueEncoding vyperABI
  contractABI words list rich_list

Theorem encoder_array_requires_positive_slots:
  evaluate_type env (ArrayT ty bd) = SOME atv ==>
  ?tv. evaluate_type env ty = SOME tv /\
       atv = ArrayTV tv bd /\ 0 < type_slot_size tv
Proof
  simp[evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem encoder_empty_tuple_array_rejected:
  evaluate_type env (ArrayT (TupleT []) bd) = NONE
Proof
  simp[evaluate_type_def, type_slot_size_def]
QED

Theorem encoder_tuple_abi_type_probe:
  has_type (Tuple tys) (ListV avs) <=>
  valid_length NONE avs /\ has_types tys avs
Proof
  simp[has_type_def]
QED

Theorem encoder_zero_tuple_evaluate_members:
  !n acc. evaluate_types env (REPLICATE n (TupleT [])) acc =
    SOME (REVERSE acc ++ REPLICATE n (TupleTV []))
Proof
  Induct >> simp[evaluate_type_def, type_slot_size_def, REPLICATE] >>
  simp[GSYM APPEND_ASSOC]
QED

Theorem encoder_zero_tuple_slot_members:
  !n. type_slot_size_list (REPLICATE n (TupleTV [])) = 0 /\
      type_memory_size_list (REPLICATE n (TupleTV [])) = 0
Proof
  Induct >> simp[REPLICATE, type_slot_size_def, type_memory_size_def]
QED

Theorem encoder_zero_tuple_value_members:
  !n. values_have_types (REPLICATE n (TupleTV []))
    (REPLICATE n (ArrayV (TupleV [])))
Proof
  Induct >> simp[REPLICATE, value_has_type_def]
QED

Theorem encoder_zero_tuple_convert_members:
  !n. vyper_to_abi_list env (REPLICATE n (TupleT []))
    (REPLICATE n (ArrayV (TupleV []))) =
    SOME (REPLICATE n (ListV []))
Proof
  Induct >> simp[REPLICATE, vyper_to_abi_def]
QED

Theorem encoder_zero_tuple_abi_members:
  !n. vyper_to_abi_types env (REPLICATE n (TupleT [])) =
    REPLICATE n (Tuple [])
Proof
  Induct >> simp[REPLICATE, vyper_to_abi_type_def]
QED

(* Source type evaluation and capacity do not bound tuple cardinality. *)
Theorem encoder_zero_tuple_source_diagnostic:
  !n. evaluate_type env (TupleT (REPLICATE n (TupleT []))) =
        SOME (TupleTV (REPLICATE n (TupleTV []))) /\
      value_has_type (TupleTV (REPLICATE n (TupleTV [])))
        (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) /\
      type_memory_size (TupleTV (REPLICATE n (TupleTV []))) = 0 /\
      vyper_to_abi env (TupleT (REPLICATE n (TupleT [])))
        (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) =
        SOME (ListV (REPLICATE n (ListV [])))
Proof
  simp[evaluate_type_def, encoder_zero_tuple_evaluate_members,
       encoder_zero_tuple_slot_members, type_slot_size_def, value_has_type_def,
       encoder_zero_tuple_value_members, type_memory_size_def,
       vyper_to_abi_def, encoder_zero_tuple_convert_members]
QED

Theorem encoder_zero_tuple_abi_cardinality_diagnostic:
  ~has_type (vyper_to_abi_type env
      (TupleT (REPLICATE (dimword (:256)) (TupleT []))))
    (ListV (REPLICATE (dimword (:256)) (ListV [])))
Proof
  simp[vyper_to_abi_type_def, encoder_zero_tuple_abi_members,
       has_type_def, valid_length_def]
QED

Theorem encoder_zero_tuple_memory_members:
  !n. tuple_in_memory (REPLICATE n (ArrayV (TupleV [])))
    (REPLICATE n (TupleTV [])) sb mem
Proof
  Induct >> simp[REPLICATE, val_in_memory_def, type_memory_size_def]
QED

Theorem encoder_zero_tuple_memory_diagnostic:
  val_in_memory (TupleTV (REPLICATE n (TupleTV [])))
    (ArrayV (TupleV (REPLICATE n (ArrayV (TupleV []))))) sb mem
Proof
  simp[val_in_memory_def, encoder_zero_tuple_memory_members]
QED

Theorem encoder_zero_tuple_input_unavailable:
  ~abi_encoder_input ei (vyper_to_abi_type env
      (TupleT (REPLICATE (dimword (:256)) (TupleT []))))
    (ListV (REPLICATE (dimword (:256)) (ListV []))) sb cap mem
Proof
  strip_tac >> drule abi_encoder_input_typed >>
  simp[encoder_zero_tuple_abi_cardinality_diagnostic]
QED
