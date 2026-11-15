(* Robust staged representations fix only meaningful encoder input bytes.
   In particular no cleanliness of bytestring padding is required. *)
Theory logAbiInputPtr
Ancestors
  stmtSimLogDataInput abiEncoderInput representationCleanPtr
  bodyPtrDefs valueEncoding contractABI words list arithmetic

Theorem robust_log_data_layout_input:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  (!mem'. mem_agree_outside m mem mem' ==> log_data_layout cx tys vs a mem') /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) ==>
  ?avs. vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf ce (TupleT tys))
      (vyper_to_abi_type (get_tenv cx) (TupleT tys)) (ListV avs) a
      (SUM (MAP (type_memory_bytes ce) tys)) mem /\
    (!mem'. mem_agree_outside m mem mem' ==>
      abi_encoder_input (type_to_abi_enc_info sf ce (TupleT tys))
        (vyper_to_abi_type (get_tenv cx) (TupleT tys)) (ListV avs) a
        (SUM (MAP (type_memory_bytes ce) tys)) mem')
Proof
  strip_tac >>
  `log_data_layout cx tys vs a mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all log_data_layout_input >>
  disch_then (qspec_then `sf` (qx_choose_then `avs` strip_assume_tac)) >>
  qexists_tac `avs` >> simp[] >> rpt strip_tac >>
  `log_data_layout cx tys vs a mem'` by metis_tac[] >>
  drule_all log_data_layout_input >>
  disch_then (qspec_then `sf` strip_assume_tac) >> gvs[]
QED

Theorem robust_abi_copy_input_clean:
  (!mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input (AbiCopy n) at av a cap mem') ==>
  !i. a <= i /\ i < a+n ==> i NOTIN m
Proof
  simp_tac bool_ss [abi_encoder_input_copy_iff] >> strip_tac >>
  `!mem'. mem_agree_outside m mem mem' ==>
    mem_bytes_at a n mem' = enc at av` by metis_tac[] >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem robust_abi_bytes_input_clean:
  (!mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input (AbiBytestring maxlen) at (BytesV bs) a cap mem') ==>
  !i. a <= i /\ i < a+32+LENGTH bs ==> i NOTIN m
Proof
  simp[abi_encoder_input_bytes_iff] >> strip_tac >>
  `!mem'. mem_agree_outside m mem mem' ==>
    mem_word_at a mem' = n2w (LENGTH bs)` by metis_tac[] >>
  `!mem'. mem_agree_outside m mem mem' ==>
    mem_bytes_at (a+32) (LENGTH bs) mem' = bs` by metis_tac[] >>
  drule robust_mem_word_at_clean >> strip_tac >>
  drule robust_mem_bytes_at_clean >> strip_tac >>
  rpt strip_tac >> Cases_on `i < a+32` >- metis_tac[] >>
  qpat_x_assum `!i. a+32 <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
  simp[]
QED
