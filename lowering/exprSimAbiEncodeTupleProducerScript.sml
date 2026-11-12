(* Checked source-facing interfaces for actual-footprint tuple staging. *)
Theory exprSimAbiEncodeTupleProducer
Ancestors
  exprSimAbiEncodeTupleOpen abiEncodeInputSupplier abiTupleEncodeOpenAssembly
  abiTupleEncodeOpenStatic abiEncodeArgsSim abiTupleEncodeOpenInput
  abiTupleEncodeOpenMemory abiEncoderSourceAggregate arithmetic list

Theorem abi_encode_tuple_open_input_interface:
  abi_tuple_open_input sf ce ty at av op next lo hi s <=>
  abi_tuple_encode_open_input sf ce ty at av op next lo hi s
Proof
  Cases_on `is_word_type ty` >>
  simp[abi_tuple_open_input_def, abi_tuple_encode_open_input_def] >>
  metis_tac[ADD_COMM]
QED

Theorem abi_encode_tuple_open_memory_interface:
  !xs ats avs d mem.
  abi_tuple_open_memory sf ce xs ats avs d mem <=>
  abi_tuple_encode_open_memory sf ce xs ats avs d mem
Proof
  Induct >- simp[abi_tuple_open_memory_def, abi_tuple_encode_open_memory_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_open_memory_def, abi_tuple_encode_open_memory_def]
QED

Theorem abi_encode_tuple_dynamic_consumer:
  abi_tuple_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ any_dynamic ats ==>
  abi_encoder_open_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
    (Tuple ats) (ListV avs) d (abi_tuple_bytes ce xs) mem
Proof
  pure_rewrite_tac[abi_encode_tuple_open_memory_interface] >>
  metis_tac[abi_tuple_encode_open_dynamic_input]
QED

Theorem abi_encode_tuple_static_consumer:
  abi_tuple_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats /\
  abi_tuple_bytes ce xs MOD 32 = 0 ==>
  ?ct rv. has_type ct rv /\ ~is_dynamic ct /\
    static_length ct = abi_tuple_bytes ce xs /\
    enc ct rv = enc (Tuple ats) (ListV avs) /\
    abi_encoder_open_input (AbiCopy (abi_tuple_bytes ce xs)) ct rv d
      (abi_tuple_bytes ce xs) mem
Proof
  pure_rewrite_tac[abi_encode_tuple_open_memory_interface] >>
  metis_tac[abi_tuple_encode_open_static_representative]
QED

Theorem abi_encode_tuple_source_encoding:
  LENGTH ts = LENGTH cts /\ LENGTH ts = LENGTH avs /\ LENGTH avs = LENGTH rvs /\
  (!i. i < LENGTH ts ==>
    source_rep env (EL i ts) (EL i infos) (EL i cts) /\
    (?tv. evaluate_type env (EL i ts) = SOME tv) /\
    enc (EL i cts) (EL i rvs) = enc (vyper_to_abi_type env (EL i ts)) (EL i avs)) ==>
  enc (Tuple cts) (ListV rvs) =
    enc (Tuple (MAP (vyper_to_abi_type env) ts)) (ListV avs)
Proof
  strip_tac >> irule abi_encoder_tuple_encoding_cong >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH ts ==> _` (qspec_then `i` strip_assume_tac) >>
  gvs[] >> drule_all source_rep_metadata >> simp[EL_MAP]
QED

