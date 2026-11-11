(* Exact static staging windows without aggregate cardinality typing. *)
Theory abiTupleEncodeOpenStatic
Ancestors
  valueEncodingDefs
  abiTupleEncodeOpenMemory abiTupleEncodeLayout abiEncoderOpenInput
  abiEncoderInput abiEncoderAdmissible abiEncoderMemory abiEncoderSourceWindow
  abiStaticAggregateProps abiTupleProps abiDecodeRanges exprLowering compileEnv
  valueEncoding contractABI words list rich_list arithmetic

Theorem abi_encoder_open_static_leaf_window:
  abi_encoder_static_leaf ei /\ abi_encoder_open_input ei at av sb cap mem /\
  ~is_dynamic at ==>
  mem_bytes_at sb (static_length at) mem = enc at av
Proof
  rw[abi_encoder_static_leaf_def]
  >- gvs[Once abi_encoder_open_input_cases]
  >- gvs[Once abi_encoder_open_input_cases] >>
  gvs[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def] >>
  simp[static_length_def, enc_def, LET_THM, REV_DEF, mem_bytes_at_def]
QED

Theorem abi_tuple_encode_open_static_window:
  !xs ats avs d mem.
  abi_tuple_encode_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats ==>
  mem_bytes_at d (abi_tuple_bytes ce xs) mem = FLAT (MAP2 enc ats avs)
Proof
  Induct >- simp[abi_tuple_encode_open_memory_def, abi_tuple_bytes_def, mem_bytes_at_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[abi_tuple_encode_open_memory_def, abi_tuple_encode_layout_def, is_dynamic_def] >>
  rpt strip_tac >> gvs[] >>
  rename1 `abi_encoder_open_input (type_to_abi_enc_info sf ce h1) head_at head_av d _ mem` >>
  `abi_encoder_static_leaf (type_to_abi_enc_info sf ce h1)` by
    (drule_all abi_encoder_translation_static_leaf >> simp[]) >>
  `mem_bytes_at d (type_memory_bytes ce h1) mem = enc head_at head_av` by
    (drule_all abi_encoder_open_static_leaf_window >> simp[]) >>
  qpat_x_assum `!ats avs d mem. _`
    (fn th => drule_all (SIMP_RULE bool_ss [abi_tuple_encode_layout_def] th)) >> strip_tac >>
  mp_tac (Q.SPECL [`d`, `type_memory_bytes ce h1`, `abi_tuple_bytes ce (xs:(operand # type) list)`, `mem`]
    abi_encoder_mem_split) >> fs[abi_tuple_bytes_def]
QED

Theorem abi_tuple_encode_open_static_encoding:
  abi_tuple_encode_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats ==>
  mem_bytes_at d (abi_tuple_bytes ce xs) mem = enc (Tuple ats) (ListV avs)
Proof
  strip_tac >> drule abi_tuple_encode_open_memory_lengths >> strip_tac >>
  drule_all abi_tuple_encode_open_static_window >>
  simp[enc_static_tuple]
QED

(* Arbitrary aligned windows admit typed static copy representatives, even empty. *)
Triviality abi_encoder_open_window_representative:
  sz MOD 32 = 0 /\ mem_bytes_at sb sz mem = bs ==>
  ?ct rv. has_type ct rv /\ ~is_dynamic ct /\ static_length ct = sz /\
    enc ct rv = bs /\
    abi_encoder_open_input (AbiCopy sz) ct rv sb sz mem
Proof
  strip_tac >> drule abi_encoder_uniform_aligned_representative >>
  disch_then (qx_choose_then `ct` strip_assume_tac) >>
  `LENGTH bs = sz` by (qpat_x_assum `mem_bytes_at _ _ _ = bs` (SUBST1_TAC o SYM) >> simp[mem_bytes_at_def]) >>
  first_x_assum (qspec_then `bs` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `rv` strip_assume_tac) >>
  qexistsl_tac [`ct`, `rv`] >> simp[] >>
  irule abiEncoderOpenInputTheory.copy >> simp[]
QED

Theorem abi_tuple_encode_open_static_representative:
  abi_tuple_encode_open_memory sf ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats /\
  abi_tuple_bytes ce xs MOD 32 = 0 ==>
  ?ct rv. has_type ct rv /\ ~is_dynamic ct /\
    static_length ct = abi_tuple_bytes ce xs /\
    enc ct rv = enc (Tuple ats) (ListV avs) /\
    abi_encoder_open_input (AbiCopy (abi_tuple_bytes ce xs)) ct rv d
      (abi_tuple_bytes ce xs) mem
Proof
  strip_tac >> drule_all abi_tuple_encode_open_static_encoding >> strip_tac >>
  irule abi_encoder_open_window_representative >> simp[]
QED
