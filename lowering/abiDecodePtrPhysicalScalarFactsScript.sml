(* Source observations for allocation-free scalar decoder execution. *)
Theory abiDecodePtrPhysicalScalarFacts
Ancestors
  abiDecoderPrimitiveCaller abiDecoderWordTyped abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiValidStatic vyperABIValid
  abiCanonicalHeadSize abiDecoderValidBytesInput abiDecoderValidBytes
  abiDecoderBytesTyped abiValidBytes abiEncoder compileEnv valueEncoding
  vyperABI contractABI venomState words list arithmetic

Theorem abi_decode_physical_word_input:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv di (dec (vyper_to_abi_type env ty) bs) v /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\ 32 <= LENGTH bs /\
  a < dimword(:256) /\
  mem_bytes_at a (LENGTH bs) (abi_decode_source opc s) = bs ==>
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w a : bytes32) s) /\
  (!mem d. mem_bytes_at d 32 mem = TAKE 32 bs ==> val_in_memory tv v d mem)
Proof
  strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty) /\
    static_length (vyper_to_abi_type env ty) = 32` by suspend "shape" >>
  `enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs) = TAKE 32 bs` by
    (drule_all vyper_decode_valid_enc_static >> strip_tac >>
     mp_tac (cj 1 abi_static_prefix_static_mutual) >>
     simp[abi_static_prefix_def] >> metis_tac[]) >>
  `mem_bytes_at a 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (qspec_then `abi_decode_source opc s` mp_tac
      (Q.SPECL [`a`, `0`, `32`, `LENGTH (bs:word8 list)`] mem_bytes_at_window) >> simp[]) >>
  conj_tac
  >- (irule abi_decoder_primitive_clamp >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> irule abi_decoder_primitive_canonical_layout >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume abi_decode_physical_word_input[shape]:
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >- (Cases_on `bt` >> gvs[is_word_type_def, vyper_base_to_abi_type_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >> gvs[is_word_type_def]) >>
  simp[vyper_to_abi_type_def]
QED

Finalise abi_decode_physical_word_input

Theorem abi_decode_physical_bytes_input:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_decoder_metadata ce env ty tv di (dec (vyper_to_abi_type env ty) bs) v /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc s) = bs /\
  n < dimword(:256) /\ B + sb + LENGTH bs < dimword(:256) /\
  eval_operand base_op s = SOME (n2w B) /\
  (base_op <> Lit 0w ==>
    B + sb + LENGTH bs <= d \/ d + abi_decode_bytes_copy_size n <= B + sb) /\
  d + abi_decode_bytes_copy_size n < dimword(:256) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_source_opcode opc /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?at payload. abi_decoder_valid_bytes_pre n at bs payload st src dst opc base_op hi B sb d s /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_bytes_metadata >>
  disch_then (qx_choose_then `at` (qx_choose_then `payload`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `vyper_decode_valid_enc at bs` by metis_tac[] >>
  drule_all abi_valid_bytes_decode >> strip_tac >>
  qexistsl_tac [`at`, `payload`] >>
  conj_tac
  >- (asm_simp_tac bool_ss [abi_decoder_valid_bytes_pre_def] >> strip_tac >>
      qpat_x_assum `base_op <> Lit 0w ==> _` drule >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []
QED
