(* Actual source observations justify the emitted array initializer. *)
Theory abiDecoderValidArrayInitInputs
Ancestors
  abiDecoderValidContract abiDecoderValidArrayValues abiDecoderRecursiveArrayFacts
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiValidAggregateHeads abiValidMember abiCanonicalLoad abiCanonicalArrayLoad abiDecodeRanges
  compileEnv valueEncoding vyperABI vyperValue contractABI venomState words list arithmetic

Theorem abi_decoder_valid_array_pre_observations:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d b cap initial ==>
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once vyper_to_abi_type_def]) >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_source_head_load:
  32 <= LENGTH bs /\ mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_decode_load opc (n2w sb : bytes32) s = n2w (abi_head_word bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (mp_tac (SIMP_RULE bool_ss [ADD_CLAUSES, DROP_0]
      (Q.INST [`off` |-> `0:num`, `n` |-> `32:num`] abi_decode_source_window)) >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes, abi_head_word_bytes]
QED

Theorem abi_decoder_valid_array_init_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc initial) = bs ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)) /\ (d + 32 <= b \/ b + cap <= d)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  drule abi_decoder_coherent_array_capacity >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)`
    by metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_assum `abi_head_word bs = LENGTH vs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH bs` by
    (fs[LENGTH_DROP, Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >> decide_tac) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_decoder_source_head_load >> strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  SUBGOAL_THEN ``d + 32 <= b \/ b + cap <= d`` assume_tac
  >- (qpat_x_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b \/ _` mp_tac >>
      simp_tac bool_ss [Once type_memory_bytes_def] >> strip_tac >> decide_tac) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH (vs:vyperValue$value list) * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      qexists_tac `h` >> asm_simp_tac bool_ss [] >>
      qpat_x_assum `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= _` mp_tac >>
      asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED
