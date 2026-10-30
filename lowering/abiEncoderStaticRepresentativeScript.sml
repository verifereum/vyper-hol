(* Additive static-copy representatives; no source cardinality restriction. *)
Theory abiEncoderStaticRepresentative
Ancestors
  abiEncoderOpenInput valueEncodingProps abiCallerTupleLayout contractABI valueEncoding words list arithmetic

Theorem abi_encoder_zero_copy_representative:
  abi_encoder_open_input (AbiCopy 0) (Tuple []) (ListV []) sb 0 mem /\
  enc (Tuple []) (ListV []) = []
Proof
  conj_tac
  >- (irule abiEncoderOpenInputTheory.copy >>
      simp[has_type_def, is_dynamic_def, static_length_def, enc_def, REV_DEF, mem_bytes_at_def]) >>
  simp[enc_def, REV_DEF]
QED

Theorem abi_encoder_static_zero_source_representative:
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\ val_in_memory tv v sb mem /\
  type_memory_size tv = 0 ==>
  ?at' av'. enc at' av' = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_open_input (AbiCopy (type_memory_size tv)) at' av' sb
      (type_memory_size tv) mem
Proof
  rpt strip_tac >>
  drule_all val_in_memory_static_abi >> simp[mem_bytes_at_def] >> strip_tac >>
  qexistsl_tac [`Tuple []`, `ListV []`] >>
  simp[abi_encoder_zero_copy_representative]
QED

(* The sparse fixed-array representation explicitly owns omitted defaults. *)
Theorem abi_encoder_fixed_omitted_default_window:
  val_in_memory (ArrayTV elem_tv (Fixed n)) (ArrayV (SArrayV kvs)) sb mem /\
  i < n /\ ALOOKUP kvs i = NONE ==>
  val_in_memory elem_tv (default_value elem_tv)
    (sb + i * type_memory_size elem_tv) mem
Proof
  simp[val_in_memory_def]
QED

Theorem abi_encoder_bytes32_representative:
  LENGTH bs = 32 ==>
  has_type (Bytes (SOME 32)) (BytesV bs) /\
  ~is_dynamic (Bytes (SOME 32)) /\ static_length (Bytes (SOME 32)) = 32 /\
  enc (Bytes (SOME 32)) (BytesV bs) = bs
Proof
  simp[has_type_def, valid_length_def, valid_bytes_bound_def,
    is_dynamic_def, static_length_def, enc_def, wordsTheory.dimword_def]
QED

Theorem abi_encoder_static_pair_encoding:
  ~is_dynamic a /\ ~is_dynamic b ==>
  enc (Tuple [a;b]) (ListV [x;y]) = enc a x ++ enc b y
Proof
  simp[enc_def, is_dynamic_def, REV_DEF]
QED

Theorem abi_encoder_pair_typing:
  has_type a x /\ has_type b y ==>
  has_type (Tuple [a;b]) (ListV [x;y])
Proof
  simp[has_type_def, valid_length_def, wordsTheory.dimword_def]
QED

Theorem abi_encoder_static_length_alignment_mutual:
  (!at. static_length at MOD 32 = 0) /\
  (!ats. SUM (MAP static_length ats) MOD 32 = 0)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops abi_type_induction) >>
  simp[static_length_def, static_length_Tuple_SUM, arithmeticTheory.MOD_PLUS,
    arithmeticTheory.MOD_TIMES2] >> rpt strip_tac
  >- (rename1 `static_length (Array bound at)` >> Cases_on `bound` >>
      simp[static_length_def] >>
      once_rewrite_tac[GSYM arithmeticTheory.MOD_TIMES2] >> simp[]) >>
  once_rewrite_tac[GSYM arithmeticTheory.MOD_PLUS] >> simp[]
QED

Theorem abi_encoder_static_length_alignment:
  !at. static_length at MOD 32 = 0
Proof
  simp[abi_encoder_static_length_alignment_mutual]
QED

Theorem abi_encoder_static_source_alignment:
  evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  type_memory_size tv MOD 32 = 0
Proof
  strip_tac >> drule_all abi_caller_static_memory >>
  metis_tac[abi_encoder_static_length_alignment]
QED
