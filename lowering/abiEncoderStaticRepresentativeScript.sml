(* Additive static-copy representatives; no source cardinality restriction. *)
Theory abiEncoderStaticRepresentative
Ancestors
  abiEncoderOpenInput valueEncodingProps abiCallerStaticMemory contractABI valueEncoding words list arithmetic

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
  ho_match_mp_tac abi_type_induction >>
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

Theorem abi_encoder_block_count_representative:
  !n bs. LENGTH bs = 32*n ==>
  ?at av. has_type at av /\ ~is_dynamic at /\
    static_length at = LENGTH bs /\ enc at av = bs
Proof
  Induct
  >- (rpt strip_tac >> gvs[] >> qexistsl_tac [`Tuple []`, `ListV []`] >>
      simp[has_type_def, is_dynamic_def, static_length_def, enc_def, REV_DEF]) >>
  rpt strip_tac >>
  `32 <= LENGTH bs /\ LENGTH (DROP 32 bs) = 32*n` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  first_x_assum (qspec_then `DROP 32 bs` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`at`, `av`] strip_assume_tac) >>
  `LENGTH (TAKE 32 bs) = 32` by simp[LENGTH_TAKE] >>
  drule abi_encoder_bytes32_representative >> strip_tac >>
  qexistsl_tac [`Tuple [Bytes (SOME 32); at]`, `ListV [BytesV (TAKE 32 bs); av]`] >>
  simp[abi_encoder_pair_typing, abi_encoder_static_pair_encoding,
    is_dynamic_def, static_length_def, static_length_Tuple_SUM] >>
  metis_tac[TAKE_DROP]
QED

Theorem abi_encoder_aligned_bytes_representative:
  LENGTH bs MOD 32 = 0 ==>
  ?at av. has_type at av /\ ~is_dynamic at /\
    static_length at = LENGTH bs /\ enc at av = bs
Proof
  strip_tac >> irule abi_encoder_block_count_representative >>
  qexists_tac `LENGTH bs DIV 32` >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (qspec_then `LENGTH bs` mp_tac) >> simp[] >> decide_tac
QED

Theorem abi_encoder_static_source_representative:
  evaluate_type env ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\ val_in_memory tv v sb mem ==>
  ?at' av'. enc at' av' = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_open_input (AbiCopy (type_memory_size tv)) at' av' sb
      (type_memory_size tv) mem
Proof
  rpt strip_tac >>
  drule_all abi_encoder_static_source_alignment >> strip_tac >>
  drule_all val_in_memory_static_abi >> strip_tac >>
  `LENGTH (mem_bytes_at sb (type_memory_size tv) mem) MOD 32 = 0` by
    simp[mem_bytes_at_def] >>
  drule abi_encoder_aligned_bytes_representative >>
  disch_then (qx_choosel_then [`at'`, `av'`] strip_assume_tac) >>
  qexistsl_tac [`at'`, `av'`] >> conj_tac >- metis_tac[] >>
  irule abiEncoderOpenInputTheory.copy >>
  gvs[mem_bytes_at_def]
QED
