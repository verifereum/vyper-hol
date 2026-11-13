Theory externalReturnZeroWindow
Ancestors
  abiEncoderWindow abiEncoderInput abiDecodeRanges contractABI valueEncoding valueEncodingDefs list rich_list arithmetic


Theorem zero_window_dynamic_array_probe:
  abi_encoder_window_input (AbiComplex []) (Array (SOME 0) (Bytes NONE))
    (ListV []) 0 0 mem /\ is_dynamic (Array (SOME 0) (Bytes NONE))
Proof
  simp[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def, is_dynamic_def]
QED

Theorem zero_window_dynamic_member_probe:
  abi_encoder_window_input (AbiComplex [(AbiComplex [],32,0,T)])
    (Tuple [Array (SOME 0) (Bytes NONE)]) (ListV [ListV []]) 0 0 mem /\
  is_dynamic (Tuple [Array (SOME 0) (Bytes NONE)])
Proof
  simp[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
       is_dynamic_def, abi_member_head_size_def,
       abi_encoder_member_span_def, zero_window_dynamic_array_probe]
QED

Theorem zero_window_dynamic_member_output_probe:
  LENGTH (enc (Tuple [Array (SOME 0) (Bytes NONE)]) (ListV [ListV []])) = 32
Proof
  EVAL_TAC >>
  simp[fcpTheory.index_bit0, fcpTheory.index_one,
       fcpTheory.finite_bit0, fcpTheory.finite_one] >> EVAL_TAC
QED

Inductive zero_read_plan:
[zero_read_copy:]
  zero_read_plan (AbiCopy 0)
[zero_read_complex:]
  (!infos. EVERY (\(ei,abi_sz,mem_sz,dyn). zero_read_plan ei) infos ==>
    zero_read_plan (AbiComplex infos))
End

Theorem zero_window_read_plan:
  !ei at av sb cap mem.
    abi_encoder_window_input ei at av sb cap mem ==>
    (cap = 0 ==> zero_read_plan ei)
Proof
  ho_match_mp_tac abi_encoder_window_input_ind >> rpt strip_tac >> gvs[]
  >- simp[zero_read_copy] >>
  irule zero_read_complex >> simp[EVERY_EL] >> rpt strip_tac >>
  Cases_on `EL n infos` >> PairCases_on `r` >> gvs[] >> metis_tac[]
QED

Theorem zero_window_relocate:
  !ei at av sb cap mem.
    abi_encoder_window_input ei at av sb cap mem ==>
    (cap = 0 ==> !sb' mem'. abi_encoder_window_input ei at av sb' 0 mem')
Proof
  ho_match_mp_tac abi_encoder_window_input_ind >> rpt strip_tac >> gvs[]
  >- (irule window_copy >> gvs[mem_bytes_at_def]) >>
  irule window_complex >> qexists_tac `ats` >> simp[]
QED
