(* A static unclamped bulk array with a complete input span is not malformed. *)
Theory abiDecodeRejectBulkDomain
Ancestors
  abiMalformedBulkIntegration abiUnclampedInhabited abiDecoderBulk
  abiDecoderCoherence abiStaticLayoutProps vyperTypeSystem valueEncoding
  abiVyperAdmissible vyperABI contractABI venomState arithmetic words

Theorem malformed_dynarray_passing_not_bulk:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic cap)) (ArrayTV tv (Dynamic cap)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic cap)) =
    DecDynArray ei stride mem_sz elem_dyn cap /\
  assignable_type env (ArrayT ty (Dynamic cap)) /\
  type_memory_size (ArrayTV tv (Dynamic cap)) < dimword (:256) /\
  mem_bytes_at B L s.vs_memory = xs /\ B+L < dimword (:256) /\
  ~(vyper_decode_valid_enc (vyper_to_abi_type env (ArrayT ty (Dynamic cap))) (DROP p xs) /\
    abi_vyper_admissible env (ArrayT ty (Dynamic cap))
      (dec (vyper_to_abi_type env (ArrayT ty (Dynamic cap))) (DROP p xs))) /\
  n = w2n (mload (B+p) s) /\ n <= cap /\ p+32+n*stride <= L ==>
  elem_dyn \/ dec_info_needs_clamp ei
Proof
  disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  CCONTR_TAC >>
  qpat_x_assum `~(_ \/ _)` (strip_assume_tac o REWRITE_RULE [DE_MORGAN_THM]) >>
  `DecDynArray ei stride mem_sz F cap =
   type_to_abi_dec_info sf ce (ArrayT ty (Dynamic cap))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  drule_then strip_assume_tac static_layout_compatible_properties >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `cap <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a` by
    (strip_tac >>
     `type_memory_size tv <= cap * type_memory_size tv` by
       (Cases_on `cap` >> fs[MULT_CLAUSES]) >>
     `type_memory_size tv < dimword (:256)` by
       (qpat_assum `type_memory_size (ArrayTV _ _) < _` mp_tac >>
        pure_rewrite_tac[type_memory_size_def] >> decide_tac) >>
     irule abi_unclamped_static_inhabited >>
     conj_tac >- fs[assignable_type_def] >>
     qexistsl_tac [`ce`, `sf`, `tv`] >> metis_tac[]) >>
  `p+32+n*static_length (vyper_to_abi_type env ty) <= L` by (simp[] >> (gvs[])) >>
  `n = 0 \/ static_length (vyper_to_abi_type env ty) < dimword (:256)` by
    (Cases_on `n` >> simp[] >>
     fs[MULT_CLAUSES] >> decide_tac) >>
  `mload (B+p) s = n2w n` by
    (qpat_assum `n = w2n _` SUBST1_TAC >> simp[]) >>
  `n < dimword (:256)` by decide_tac >>
  `~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by metis_tac[] >>
  (metis_tac[abi_malformed_bulk_memory_reflected])
QED
