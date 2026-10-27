(* Resource-boundary diagnostics for the frozen source encoder contract.
   These concern internal runner premises, not execution counterexamples. *)
Theory abiEncoderResourceAdapter
Ancestors
  abiEncoderProps abiEncoderOpenInput abiEncoderOpenInputFrame
  abiEncoderInput abiDecodeRanges valueEncodingProps contractABI
  fragExec words list vyperTyping valueEncoding vyperValue vyperABI

Theorem abi_encoder_zero_source_separation_diagnostic:
  evaluate_type FEMPTY
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)]) =
    SOME (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)]) /\
  type_memory_size
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)]) = 0 /\
  venomMemDefs$regions_disjoint (16,0) (0,32) /\
  (!source_cap:num. ~(16 + source_cap <= 0 \/ 0 + 32 <= 16))
Proof
  simp[evaluate_type_def, type_memory_size_def, type_slot_size_def,
    wordsTheory.dimword_def, vfmConstantsTheory.word_size_def,
    venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encoder_zero_source_value_diagnostic:
  value_has_type
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) /\
  vyper_to_abi FEMPTY
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) = SOME (ListV [ListV []]) /\
  val_in_memory
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) 16 mem /\
  LENGTH (enc (vyper_to_abi_type FEMPTY
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)]))
    (ListV [ListV []])) = 32
Proof
  simp[value_has_type_def, vyper_to_abi_def, vyper_to_abi_type_def,
    val_in_memory_def, type_memory_size_def, enc_def, is_dynamic_def,
    REV_DEF, evaluate_type_def, type_slot_size_def,
    vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]
QED

Theorem abi_encoder_zero_source_pre_diagnostic:
  enc_pre st st' ops 64 top
    (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)])
    (ArrayV (TupleV [ArrayV (SArrayV [])])) 16 [(0,32)] s <=>
  ((!y. MEM (Var y) ops ==> not_fresh_at st y) /\
   enc_scratch (frag_ids st st') 64 top s)
Proof
  simp[enc_pre_def, abi_encoder_zero_source_value_diagnostic,
    type_memory_size_def, venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encoder_pre_memory_bounds:
  enc_pre st st' ops lo top tv v sb [(d,n)] s ==>
  sb + type_memory_size tv < dimword (:256) /\
  d + n < dimword (:256)
Proof
  simp[enc_pre_def, enc_scratch_def] >> rpt strip_tac >> decide_tac
QED

Theorem abi_encoder_zero_source_open_diagnostic:
  abi_encoder_open_input (AbiComplex [(AbiComplex [],32,0,T)])
    (Tuple [Array (SOME 0) (Bytes NONE)]) (ListV [ListV []]) 16 0 mem
Proof
  simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
    abi_encoder_member_span_def] >>
  simp[abi_member_head_size_def, is_dynamic_def,
    abi_encoder_open_complex_iff, abi_encoder_tuple_type_def,
    abi_encoder_member_span_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_encoder_zero_source_open_transport:
  abi_encoder_open_input (AbiComplex [(AbiComplex [],32,0,T)])
    (Tuple [Array (SOME 0) (Bytes NONE)]) (ListV [ListV []]) 16 0 mem'
Proof
  irule abi_encoder_open_input_empty_memory >>
  qexists_tac `[]` >> simp[abi_encoder_zero_source_open_diagnostic]
QED
