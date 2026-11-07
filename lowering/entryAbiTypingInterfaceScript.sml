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

(* FROZEN-ORIGIN ADMISSIBILITY AUDIT (not a proposed theorem):

   Branch        ABI typing obligations            Existing source facts / gap
   Tuple         has_types ats avs and              evaluate_types + conversion
                 LENGTH avs < dimword(:256)         align members; slot size <=
                                                    dimword gives no strict
                                                    cardinality producer.
   Struct        same as Tuple, in env \\ nsid      field names and evaluation
                                                    align; empty structs have
                                                    zero slots. Same gap.
   Fixed array   all members typed; length=n;       evaluate_type gives n>0,
                 length < dimword(:256)            element slots>0, and
                                                    n*slots < dimword, enough
                                                    for n < dimword. Sparse
                                                    missing cells need typed
                                                    default_to_abi tv.
   Dynamic       all members typed; actual         source value typing bounds
   array         length < dimword(:256)            actual length by n, and
                                                    1+n*slots < dimword with
                                                    positive slots bounds n.
   Default       has_type converted type           default_value_has_type_thm:
                 (default_to_abi tv)                evaluate_type -> source
                                                    default typing; cj 1 of
                                                    vyper_to_abi_default_value
                                                    supplies conversion, NOT
                                                    target ABI typing. The
                                                    same tuple/struct gap
                                                    persists for defaults.

   Frozen-premise producer map:
   - e2eDefs.valid_vyper_call_def gives equal argument lengths, successful
     binding, and selectorDispatch.calldata_encodes_def. The latter requires
     conversion and equality with enc, but NO has_type or successful decoder
     result. enc is total, not a checked partial encoding operation.
   - entryArgumentCastFacts.bind_arguments_source_values gives evaluated
     original input typing. entryArgumentAbiFacts records params_ok provenance.
   - e2eDefs.source_typing_ok_def supplies check_contract, machine typing,
     call_tx_well_typed and checked_contract_runtime_ready. call_tx_well_typed
     bounds tx.calldata length and transaction fields, not aggregate argument
     cardinalities. checked_contract_runtime_ready supplies deployment/export
     and immutable readiness, not argument ABI typing.
   - abi_decode_bytes_widths is a source guard only for the AbiDecode builtin
     (vyperTypeSystem.type_builtin_result_ok_def), not external parameters.
     supported_nested_type ensures positive fixed bytes at scalar leaves, but
     a bridge through supported_struct_fields and env deletion is still needed.
   - Even such a width bridge will not prove strict tuple/struct cardinality:
     supported tuples can contain zero-slot empty structs. Positive slot bounds
     alone also leave the equality boundary because tuple evaluation uses <=.

   Exact missing producer: from frozen selected-call hypotheses, obtain strict
   cardinality for each tuple/struct on the selected argument and on evaluated
   defaults that sparse conversion may insert. No existing theorem with this
   output was found in generated signatures or lowering/venom sources. A
   general mutual forward-typing theorem remains unauthorized; replacing its
   premise with assignable_type is not justified by this audit. *)
