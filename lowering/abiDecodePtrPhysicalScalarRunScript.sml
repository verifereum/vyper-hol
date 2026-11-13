(* Allocation-free execution from actual source-valid scalar bytes. *)
Theory abiDecodePtrPhysicalScalarRun
Ancestors
  abiDecodePtrPhysicalScalarFacts abiDecoderClampedWord abiDecoderWordTyped
  abiDecoderValidBytes abiDecoderBytesShape abiDecoderBytesTyped abiDecoderContract
  abiDecoderTypedContract abiDecoderCoherence abiDecoderFrame abiEncoder
  abiCanonicalHeadSize exprLowering compileEnv valueEncoding supportedTypes vyperABI contractABI
  venomState words list arithmetic

Definition abi_decode_physical_scalar_pre_def:
  abi_decode_physical_scalar_pre ce env sf ty tv bs v st src dst base_op hi B pos d s <=>
    supported_scalar_type ty /\ abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info sf ce ty)
      (dec (vyper_to_abi_type env ty) bs) v /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\ 32 <= LENGTH bs /\
    mem_bytes_at (B + pos) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
    B + pos + LENGTH bs < dimword(:256) /\
    d + type_memory_bytes ce ty < dimword(:256) /\
    (B + pos + LENGTH bs <= d \/ d + type_memory_bytes ce ty <= B + pos) /\
    eval_operand base_op s = SOME (n2w B) /\
    eval_operand src s = SOME (n2w pos) /\ eval_operand dst s = SOME (n2w d) /\
    fresh_vars_wrt st s /\
    (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
      pos + LENGTH bs <= h /\ h < dimword(:256))
End

Theorem abi_decode_physical_word_sequence[local]:
  abi_decode_physical_scalar_pre ce env sf ty tv bs v st src dst base_op hi B pos d s /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory tv v d t.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) s t /\ fresh_vars_wrt st' t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_decode_physical_scalar_pre`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_physical_scalar_pre_def]) >>
  `B + pos < dimword(:256) /\ d < dimword(:256)` by decide_tac >>
  drule_all abi_decode_physical_word_input >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_copied_window >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  drule (cj 2 abi_decoder_primitive_cases) >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `mem_bytes_at (B + pos) 32 (abi_decode_source MLOAD s) = TAKE 32 bs` by
    (qspec_then `abi_decode_source MLOAD s` mp_tac
      (Q.SPECL [`B + pos`, `0`, `32`, `LENGTH (bs:word8 list)`] mem_bytes_at_window) >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decode_physical_bytes_sequence[local]:
  abi_decode_physical_scalar_pre ce env sf ty tv bs v st src dst base_op hi B pos d s /\
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi (type_to_abi_dec_info sf ce ty) st = ((),st') ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory tv v d t.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) s t /\ fresh_vars_wrt st' t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_decode_physical_scalar_pre`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_physical_scalar_pre_def]) >>
  mp_tac (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``] abi_valid_bytes_lowering) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `n < dimword(:256)` by
    (mp_tac (cj 3 abi_decoder_bytes_copy_size) >> strip_tac >>
     qpat_x_assum `d + type_memory_bytes ce ty < _` mp_tac >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `?at payload. abi_decoder_valid_bytes_pre n at bs payload st src dst MLOAD base_op hi B pos d s /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)` by
    (irule abi_decode_physical_bytes_input >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> disch_tac >>
  drule abi_decoder_valid_bytes_sequence >>
  asm_simp_tac bool_ss [] >> disch_then drule >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  qexists_tac `t` >> simp[]
QED

Theorem abi_decode_physical_scalar_sequence:
  abi_decode_physical_scalar_pre ce env sf ty tv bs v st src dst base_op hi B pos d s /\
  compile_abi_decode_to_buf dst src MLOAD base_op hi (type_to_abi_dec_info sf ce ty) st = ((),st') ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory tv v d t.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) s t /\ fresh_vars_wrt st' t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `supported_scalar_type ty` by fs[abi_decode_physical_scalar_pre_def] >>
  `(?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp) \/
    (?n. ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n))` by
    (Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     fs[supported_word_type_def, supported_string_type_def, type_to_abi_dec_info_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     fs[supported_word_type_def, supported_string_type_def, type_to_abi_dec_info_def])
  >- (irule abi_decode_physical_word_sequence >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule abi_decode_physical_bytes_sequence >> metis_tac[]
QED
