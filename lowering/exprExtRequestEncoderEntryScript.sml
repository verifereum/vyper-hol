(* The request tuple supplies a real source window, not scratch-per-id room. *)
Theory exprExtRequestEncoderEntry
Ancestors
  abiEncoderWindowRun abiEncoderSourceProducer abiEncoderWindow
  abiEncoderAdmissible abiEncoderSourceInvoke valueEncoding
  vyperABI contractABI list

Theorem extrequest_encoder_source_window:
  abi_enc_plan env (TupleT tys) ei /\
  evaluate_type env (TupleT tys) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi env (TupleT tys) (ArrayV (TupleV vs)) = SOME av /\
  tuple_in_memory vs tvs sb mem ==>
  ?at rv. enc at rv = enc (vyper_to_abi_type env (TupleT tys)) av /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at rv sb
      (type_memory_size (TupleTV tvs)) mem
Proof
  strip_tac >>
  `val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) sb mem` by
    simp[val_in_memory_def] >>
  drule_all abi_encoder_source_window >> strip_tac >>
  qexistsl_tac [`ct`, `rv`] >> simp[] >>
  metis_tac[abi_encoder_open_input_window, cj 1 abi_enc_plan_admissible]
QED
