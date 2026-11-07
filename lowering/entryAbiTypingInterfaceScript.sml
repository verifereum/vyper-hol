Theory entryAbiTypingInterface
Ancestors entryAbiScalarTyping vyperABIRoundtrip vyperTypeDefaults contractABI
          vyperValue vyperTyping vyperTypeSystem vyperABI words list

(* Zero-slot members expose the difference between slot and ABI cardinality. *)
Theorem entry_none_replicate_evaluation[local]:
  !n acc. evaluate_types env (REPLICATE n NoneT) acc =
    SOME (REVERSE acc ++ REPLICATE n NoneTV)
Proof
  Induct >> simp[evaluate_type_def, APPEND_ASSOC]
QED

Theorem entry_none_replicate_slots[local]:
  !n. type_slot_size_list (REPLICATE n NoneTV) = 0
Proof
  Induct >> simp[type_slot_size_def]
QED

Theorem entry_none_replicate_conversion[local]:
  !n. vyper_to_abi_list env (REPLICATE n NoneT) (REPLICATE n NoneV) =
      SOME (REPLICATE n (ListV []))
Proof
  Induct >> simp[vyper_to_abi_def]
QED

Theorem entry_none_replicate_typing[local]:
  !n. values_have_types (REPLICATE n NoneTV) (REPLICATE n NoneV) /\
      has_types (vyper_to_abi_types env (REPLICATE n NoneT))
        (REPLICATE n (ListV []))
Proof
  Induct >> simp[value_has_type_def, vyper_to_abi_type_def, has_type_def]
QED

Theorem entry_none_tuple_cardinality_probe[local]:
  !n. evaluate_type env (TupleT (REPLICATE n NoneT)) =
        SOME (TupleTV (REPLICATE n NoneTV)) /\
      value_has_type (TupleTV (REPLICATE n NoneTV))
        (ArrayV (TupleV (REPLICATE n NoneV))) /\
      abi_decode_bytes_widths env (TupleT (REPLICATE n NoneT)) /\
      vyper_to_abi env (TupleT (REPLICATE n NoneT))
        (ArrayV (TupleV (REPLICATE n NoneV))) =
        SOME (ListV (REPLICATE n (ListV []))) /\
      (has_type (vyper_to_abi_type env (TupleT (REPLICATE n NoneT)))
        (ListV (REPLICATE n (ListV []))) <=> n < dimword (:256))
Proof
  simp[evaluate_type_def, entry_none_replicate_evaluation,
       type_slot_size_def, entry_none_replicate_slots,
       value_has_type_def, abi_decode_bytes_widths_def,
       vyper_to_abi_def, entry_none_replicate_conversion,
       vyper_to_abi_type_def, has_type_def, entry_none_replicate_typing]
QED

(* A checked counterexample to the proposed unrestricted helper, not to the
   frozen entry theorem: supported_place_type excludes these NoneT members. *)
Theorem entry_forward_typing_cardinality_counterexample[local]:
  let ty = TupleT (REPLICATE (dimword (:256)) NoneT);
      tv = TupleTV (REPLICATE (dimword (:256)) NoneTV);
      v = ArrayV (TupleV (REPLICATE (dimword (:256)) NoneV));
      av = ListV (REPLICATE (dimword (:256)) (ListV [])) in
  evaluate_type env ty = SOME tv /\ value_has_type tv v /\
  abi_decode_bytes_widths env ty /\ vyper_to_abi env ty v = SOME av /\
  ~has_type (vyper_to_abi_type env ty) av
Proof
  qspec_then `dimword (:256)` mp_tac entry_none_tuple_cardinality_probe >>
  simp[]
QED
