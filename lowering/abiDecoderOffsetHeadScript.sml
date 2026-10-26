(* TOP-LEVEL: characterize the former readable-head restriction exactly.
   Recursive callers use the ordinary offset path or the empty-member path. *)
Theory abiDecoderOffsetHead
Ancestors
  abiDecoderOffset abiDecoderDynamic abiDecoderCoherence abiDecoderReadableTypes
  abiDecoderHeadAdequacy abiEncoder exprLowering compileEnv vyperABI vyperValue
  contractABI finite_map list

Theorem abi_decoder_zero_array_type:
  (?at. vyper_to_abi_type env ty = Array (SOME 0) at) <=>
    ?elem. ty = ArrayT elem (Fixed 0)
Proof
  Cases_on `ty` >> simp[vyper_to_abi_type_def, AllCaseEqs()] >|
  [rename1 `vyper_base_to_abi_type bt` >> Cases_on `bt` >> simp[] >>
   rename1 `BytesT bound` >> Cases_on `bound` >> simp[],
   rename1 `ArrayT elem bound` >> Cases_on `bound` >> simp[vyper_to_abi_type_def]]
QED

Theorem abi_decoder_readable_head_iff:
  abi_decoder_coherent ce env sf ty tv ==>
  (abi_decoder_readable_head env ty <=>
    type_to_abi_dec_info sf ce ty <> DecComplex T [])
Proof
  strip_tac >> drule abi_decoder_coherent_dynamic >> strip_tac >>
  Cases_on `?elem. ty = ArrayT elem (Fixed 0)`
  >- (gvs[] >>
      gvs[abi_decoder_readable_head_def, type_to_abi_dec_info_def,
        abi_decoder_dynamic_def, vyper_to_abi_type_def, is_dynamic_def]) >>
  `!at. vyper_to_abi_type env ty <> Array (SOME 0) at` by
    metis_tac[abi_decoder_zero_array_type] >>
  simp[abi_decoder_readable_head_def, abi_decoder_empty_dynamic_translation] >> metis_tac[]
QED

Theorem abi_decoder_nonempty_readable_head:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty <> DecComplex T [] ==>
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)
Proof
  metis_tac[abi_decoder_readable_head_iff, abi_decoder_readable_head_def]
QED

Theorem abi_decoder_evaluated_array_head:
  evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound) ==>
  !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem
Proof
  strip_tac >>
  `evaluate_type env ty = SOME tv /\ 0 < type_slot_size tv` by
    (qpat_x_assum `evaluate_type env (ArrayT ty bound) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()]) >>
  drule_all evaluated_positive_type_excludes_empty_abi_array >> simp[]
QED
