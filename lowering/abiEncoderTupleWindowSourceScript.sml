(* Declared tuple strides with actual bytestring read windows. *)
Theory abiEncoderTupleWindowSource
Ancestors abiEncoderWindowSource abiEncoderSourceTransport
  normalizationTupleResourcesPtr

Theorem abi_encoder_tuple_bytes_window_source:
  LENGTH ts = LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
  LENGTH infos = LENGTH ts /\ LENGTH ats = LENGTH ts /\
  tuple_in_memory vs tvs b mem /\ vyper_to_abi_list env ts vs = SOME avs /\
  (!i. i < LENGTH ts ==>
    evaluate_type env (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    ((?k. EL i ts = BaseT (BytesT (Dynamic k)) /\ EL i ats = Bytes NONE /\
      EL i infos = (AbiBytestring k,32,type_memory_size (EL i tvs),T)) \/
     (?k. EL i ts = BaseT (StringT k) /\ EL i ats = String /\
      EL i infos = (AbiBytestring k,32,type_memory_size (EL i tvs),T)))) ==>
  abi_encoder_window_input (AbiComplex infos) (Tuple ats) (ListV avs)
    b (SUM (MAP type_memory_size tvs)) mem
Proof
  strip_tac >>
  `!i. i < LENGTH ts ==>
    evaluate_type env (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs)` by metis_tac[] >>
  drule_all abi_encoder_tuple_source >> strip_tac >>
  `!i. abi_encoder_member_span (TAKE i infos) =
    SUM (MAP type_memory_size (TAKE i tvs))` by
    (rewrite_tac[abiEncoderInputTheory.abi_encoder_member_span_def] >>
     irule typedCopyTuplePtrTheory.sum_map_take_pointwise >>
     simp[] >> gen_tac >> strip_tac >>
     qpat_assum `!i. i < LENGTH ts ==> _ /\ _ /\ ((_ \/ _))`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
  simp[abiEncoderWindowTheory.abi_encoder_window_complex_iff, abiEncoderInputTheory.abi_encoder_tuple_type_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i. i < LENGTH ts ==> _ /\ _ /\ ((_ \/ _))`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!i. i < LENGTH ts ==> val_in_memory _ _ _ _ /\ _`
    (qspec_then `i` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  gvs[abiDecodeRangesTheory.abi_member_head_size_def, contractABITheory.is_dynamic_def] >>
  (qexists_tac `type_memory_size (EL i tvs)` >> simp[] >>
   conj_tac >-
     (irule normalizationTupleResourcesPtrTheory.mapped_prefix_element_bound >> simp[]) >>
   irule abiEncoderWindowTheory.abi_encoder_open_input_window)
  >- (irule abiEncoderSourceWindowTheory.abi_encoder_open_bytes_source >>
      qexistsl_tac [`env`, `EL i vs`] >>
      qpat_x_assum `!i. _ ==> evaluate_type _ _ = _ /\ _` (qspec_then `i` mp_tac) >>
      qpat_x_assum `!i. _ ==> val_in_memory _ _ _ _ /\ _` (qspec_then `i` mp_tac) >> simp[]) >>
  irule abiEncoderSourceWindowTheory.abi_encoder_open_string_source >>
  qexistsl_tac [`env`, `EL i vs`] >>
  qpat_x_assum `!i. _ ==> evaluate_type _ _ = _ /\ _` (qspec_then `i` mp_tac) >>
  qpat_x_assum `!i. _ ==> val_in_memory _ _ _ _ /\ _` (qspec_then `i` mp_tac) >> simp[]
QED

Theorem abi_encoder_tuple_bytes_robust_window_source:
  LENGTH ts = LENGTH tvs /\ LENGTH vs = LENGTH tvs /\
  LENGTH infos = LENGTH ts /\ LENGTH ats = LENGTH ts /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) b mem) /\
  vyper_to_abi_list env ts vs = SOME avs /\
  (!i. i < LENGTH ts ==>
    evaluate_type env (EL i ts) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i vs) /\
    ((?k. EL i ts = BaseT (BytesT (Dynamic k)) /\ EL i ats = Bytes NONE /\
      EL i infos = (AbiBytestring k,32,type_memory_size (EL i tvs),T)) \/
     (?k. EL i ts = BaseT (StringT k) /\ EL i ats = String /\
      EL i infos = (AbiBytestring k,32,type_memory_size (EL i tvs),T)))) ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input (AbiComplex infos) (Tuple ats) (ListV avs)
      b (SUM (MAP type_memory_size tvs)) mem
Proof
  rpt strip_tac >> irule abi_encoder_tuple_bytes_window_source >>
  qexistsl_tac [`env`, `ts`, `vs`] >> simp[] >>
  first_x_assum drule >> simp[valueEncodingTheory.val_in_memory_def]
QED
