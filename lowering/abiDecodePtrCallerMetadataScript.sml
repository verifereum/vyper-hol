Theory abiDecodePtrCallerMetadata
Ancestors
  abiCallerBuiltinInput abiDecoderPrimitiveCaller abiDecoderReadableTypes
  supportedTypes abiValidMembers vyperTypeABI valueEncodingTyping
  abiDecoderCoherence vyperTypeSystem vyperTyping vyperTypeDefaults list

Theorem abi_decode_flat_evaluated_coherence:
  !tys tvs. EVERY supported_scalar_type tys /\
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs ==>
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `supported_scalar_type ty` >> Cases_on `ty` >>
  gvs[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  irule abi_decoder_base_caller_coherent >> simp[]
QED

Theorem abi_decode_flat_tuple_coherence:
  EVERY supported_scalar_type tys /\
  evaluate_type env (TupleT tys) = SOME tv ==>
  abi_decoder_coherent ce env sf (TupleT tys) tv
Proof
  strip_tac >> irule abi_caller_tuple_coherent >> simp[] >>
  metis_tac[abi_decode_flat_evaluated_coherence]
QED

(* Source typing is already provided by abi_valid_tuple_source_members and
   abi_decoder_members_relations; value_has_type_val_wf supplies well-formedness.
   No second source-value contract is needed here. *)

Theorem abi_decode_coherent_member_machine_bounds:
  !tys tvs. LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  SUM (MAP (type_memory_bytes ce) tys) < bound ==>
  EVERY (\tv. type_memory_size tv < bound) tvs
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def]
QED
