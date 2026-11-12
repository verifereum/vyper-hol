(* Semantic read footprint; no claim about encoder execution. *)
Theory extRetAbiReadCleanPtr
Ancestors
  abiEncoderInput abiEncoderBufferFrame representationCleanPtr bodyPtrDefs
  list arithmetic pred_set

Theorem robust_abi_encoder_array_child:
  (!mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn)
      (Array NONE ct) (ListV avs) sb cap mem') /\ i < LENGTH avs ==>
  !mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input ei ct (EL i avs) (sb+32+i*mem_sz) mem_sz mem'
Proof
  simp[abi_encoder_array_input_iff] >> metis_tac[]
QED

Theorem robust_abi_encoder_complex_child:
  (!mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input (AbiComplex infos) at (ListV avs) sb cap mem') /\
  abi_encoder_tuple_type at ats /\ i < LENGTH infos /\
  EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
  !mem'. mem_agree_outside m mem mem' ==>
    abi_encoder_input ei (EL i ats) (EL i avs)
      (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem'
Proof
  rpt strip_tac >> first_x_assum drule >>
  simp[abi_encoder_complex_input_iff] >> strip_tac >>
  `ats' = ats` by metis_tac[abi_encoder_tuple_type_unique] >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Inductive abi_encoder_read_window:
[word:]
  (!av sb. abi_encoder_read_window AbiPrimWord av sb sb 32)
[copy:]
  (!sz av sb. abi_encoder_read_window (AbiCopy sz) av sb sb sz)
[bytes_head:]
  (!maxlen bs sb.
    abi_encoder_read_window (AbiBytestring maxlen) (BytesV bs) sb sb 32)
[bytes_data:]
  (!maxlen bs sb.
    abi_encoder_read_window (AbiBytestring maxlen) (BytesV bs) sb (sb+32) (LENGTH bs))
[array_head:]
  (!ei abi_sz mem_sz dyn avs sb.
    abi_encoder_read_window (AbiDynArray ei abi_sz mem_sz dyn) (ListV avs) sb sb 32)
[array_child:]
  (!ei abi_sz mem_sz dyn avs sb i a n.
    i < LENGTH avs /\
    abi_encoder_read_window ei (EL i avs) (sb+32+i*mem_sz) a n ==>
    abi_encoder_read_window (AbiDynArray ei abi_sz mem_sz dyn) (ListV avs) sb a n)
[complex_child:]
  (!infos avs sb i ei abi_sz mem_sz dyn a n.
    i < LENGTH infos /\ i < LENGTH avs /\
    EL i infos = (ei,abi_sz,mem_sz,dyn) /\
    abi_encoder_read_window ei (EL i avs)
      (sb+abi_encoder_member_span (TAKE i infos)) a n ==>
    abi_encoder_read_window (AbiComplex infos) (ListV avs) sb a n)
End

Theorem abi_encoder_read_window_clean:
  !ei av sb a n.
    abi_encoder_read_window ei av sb a n ==>
    !m mem at cap.
      (!mem'. mem_agree_outside m mem mem' ==>
        abi_encoder_input ei at av sb cap mem') ==>
      !j. a <= j /\ j < a+n ==> j NOTIN m
Proof
  ho_match_mp_tac abi_encoder_read_window_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[abi_encoder_input_word_iff] >>
      metis_tac[robust_mem_bytes_at_clean, ADD_COMM])
  >- (rpt gen_tac >> simp[abi_encoder_input_copy_iff] >>
      metis_tac[robust_mem_bytes_at_clean, ADD_COMM])
  >- (rpt gen_tac >> simp_tac (srw_ss()) [abi_encoder_input_bytes_iff] >>
      metis_tac[robust_mem_word_at_clean])
  >- (rpt gen_tac >> simp_tac (srw_ss()) [abi_encoder_input_bytes_iff] >>
      metis_tac[robust_mem_bytes_at_clean, ADD_COMM])
  >- (rpt gen_tac >> simp[abi_encoder_array_input_iff] >>
      metis_tac[robust_mem_word_at_clean])
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
      `abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn)
         at (ListV avs) sb cap mem` by
        (first_x_assum irule >> simp[mem_agree_outside_def]) >>
      gvs[abi_encoder_array_input_iff] >>
      first_x_assum (qspecl_then [`m`, `mem`, `ct`, `mem_sz`] mp_tac) >>
      impl_tac >- metis_tac[] >> simp[])
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  `abi_encoder_input (AbiComplex infos) at (ListV avs) sb cap mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  pop_assum mp_tac >> simp[abi_encoder_complex_input_iff] >> strip_tac >>
  qpat_x_assum `!m mem at cap. _`
    (qspecl_then [`m`, `mem`, `EL i ats`, `mem_sz`] mp_tac) >>
  impl_tac >- metis_tac[robust_abi_encoder_complex_child] >>
  simp[]
QED

(* Empty values still read their length word, never padding or spare slots. *)
Theorem abi_encoder_read_window_empty_bytes:
  abi_encoder_read_window (AbiBytestring maxlen) (BytesV []) sb a n <=>
  (a = sb /\ n = 32) \/ (a = sb+32 /\ n = 0)
Proof
  simp[Once abi_encoder_read_window_cases] >> metis_tac[]
QED

Theorem abi_encoder_read_window_empty_array:
  abi_encoder_read_window (AbiDynArray ei abi_sz mem_sz dyn) (ListV []) sb a n <=>
  a = sb /\ n = 32
Proof
  simp[Once abi_encoder_read_window_cases] >> metis_tac[]
QED

Theorem abi_encoder_empty_reads_no_payload:
  ~abi_encoder_read_window (AbiBytestring maxlen) (BytesV []) sb (sb+32) 1 /\
  ~abi_encoder_read_window (AbiDynArray ei abi_sz mem_sz dyn) (ListV []) sb (sb+32) 1
Proof
  simp[abi_encoder_read_window_empty_bytes, abi_encoder_read_window_empty_array]
QED
