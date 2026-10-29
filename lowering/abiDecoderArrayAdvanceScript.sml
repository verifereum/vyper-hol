(* Advance the initialized prefix using the concrete child's output-only frame. *)
Theory abiDecoderArrayAdvance
Ancestors
  abiDecoderArrayInvariant abiDecoderArrayChild abiDecoderArrayPrefix
  abiDecoderFrameCompose abiDecoderContract abiDecoderCoherence abiDecoderWordTyped
  abiDecoderTypedContract valueEncodingProps valueEncoding compileEnv vyperTyping
  venomState contractABI words list rich_list arithmetic
Libs
  Omega

Theorem abi_decoder_primitive_array_sizes:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  type_memory_bytes ce ty = 32 /\ type_memory_size tv = 32 /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32
Proof
  strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `type_memory_size tv = 32` by fs[abi_decoder_header_def] >>
  asm_simp_tac bool_ss [Once type_memory_bytes_def]
QED

Theorem abi_decoder_array_cell_bound:
  !j n cap d:num. j < n /\ n <= cap ==>
  d + 32 + j * 32 + 32 <= d + (32 + cap * 32)
Proof
  Omega.OMEGA_TAC
QED

Theorem abi_decoder_array_memory_advance:
  abi_decoder_array_memory opc aty avs tv vs sb d j before /\ j < LENGTH vs /\
  elems_in_memory (TAKE j vs ++ [EL j vs]) (d + 32) tv after.vs_memory /\
  abi_decode_frame (d + 32 + j * type_memory_size tv) (type_memory_size tv) before after /\
  d + 32 + j * type_memory_size tv + type_memory_size tv <= d + outsz /\
  abi_decode_source_opcode opc /\
  (opc = MLOAD ==> sb + LENGTH (enc (Array NONE aty) (ListV avs)) <= d \/
                     d + outsz <= sb) ==>
  abi_decoder_array_memory opc aty avs tv vs sb d (SUC j) after
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_array_memory _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_array_memory_def]) >>
  `abi_decode_frame d outsz before after` by
    (irule abi_decode_frame_widen >>
     qexistsl_tac [`d + 32 + j * type_memory_size tv`, `type_memory_size tv`] >>
     asm_simp_tac bool_ss [] >> pure_rewrite_tac [GSYM ADD_ASSOC] >> irule LESS_EQ_ADD) >>
  `mem_word_at d after.vs_memory = mem_word_at d before.vs_memory` by
    (irule abi_decode_frame_mem_word >>
     qexistsl_tac [`d + 32 + j * type_memory_size tv`, `type_memory_size tv`] >>
     asm_simp_tac bool_ss [LESS_EQ_ADD]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs))) (abi_decode_source opc after) =
   mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs))) (abi_decode_source opc before)` by
    (irule abi_decode_frame_source_window >> simp[Excl "enc_def"] >>
     qexistsl_tac [`d`, `outsz`] >> simp[Excl "enc_def"]) >>
  `SUC j <= LENGTH vs` by decide_tac >>
  asm_simp_tac bool_ss [abi_decoder_array_memory_def, TAKE_SUC, TAKE1_DROP]
QED
