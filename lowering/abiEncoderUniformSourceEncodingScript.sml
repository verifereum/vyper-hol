(* Encoding congruence depends on source metadata, not on memory. *)
Theory abiEncoderUniformSourceEncoding
Ancestors
  abiEncoderSourceAggregate abiEncoderOpenInput vyperABI contractABI list

Theorem abi_encoder_source_reps_encoding_cong:
  source_reps env ts infos cts /\ LENGTH avs = LENGTH ts /\
  LENGTH rvs = LENGTH ts /\
  abi_encoder_tuple_type at (vyper_to_abi_types env ts) /\
  abi_encoder_tuple_type ct cts /\
  (!i. i < LENGTH ts ==>
    enc (EL i cts) (EL i rvs) =
      enc (vyper_to_abi_type env (EL i ts)) (EL i avs)) ==>
  enc ct (ListV rvs) = enc at (ListV avs)
Proof
  strip_tac >> drule source_reps_abi_metadata >> strip_tac >>
  drule source_reps_lengths >> strip_tac >>
  irule abi_encoder_tuple_type_encoding_cong >>
  conj_tac >- simp[] >>
  qexistsl_tac [`cts`, `vyper_to_abi_types env ts`] >>
  gvs[source_translation_list, EL_MAP]
QED
