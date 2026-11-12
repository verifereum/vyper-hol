(* Reflection of checked primitive ranges into source ABI acceptance. *)
Theory abiBoundedLeafReflection
Ancestors
  abiBoundedLeafExecution abiBoundedBytesExecution abiDecoderBytestringCases
  abiVyperAdmissible abiValidBytes abiCanonicalHeadSize
  abiDecoderContract valueEncoding abiDecoderClamp abiDecoderCoherence
  abiDecoderWordTyped entryDecodeProps exprLowering compileEnv valueEncodingProps
  abiEncoderWordSource vyperTypeABI vyperABIValid contractABI vyperABI
  vyperValue vyperTyping venomMemProps words byte list arithmetic

Theorem abi_decoder_clamp_entry_ok:
  abi_decoder_clamp_valid clamp w ==> abi_clamp_ok clamp w
Proof
  Cases_on `clamp` >>
  simp[abi_decoder_clamp_valid_def, abi_clamp_ok_def]
  >- (Cases_on `b` >> simp[abi_decoder_clamp_valid_def] >> strip_tac >>
      `n < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
      simp_tac std_ss [w2n_n2w, LESS_MOD] >>
      irule (iffLR w2n_eq_0) >>
      asm_simp_tac arith_ss [w2n_lsr, LESS_DIV_EQ_ZERO]) >>
  strip_tac >> irule (iffLR w2n_eq_0) >>
  asm_simp_tac arith_ss [w2n_lsr, LESS_DIV_EQ_ZERO]
QED

Theorem abi_decoder_primitive_word_witness:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_clamp_valid clamp w ==>
  ?v. value_has_type tv v /\ typed_val_to_w256 tv v = w
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  drule_all abi_decoder_primitive_cases >> strip_tac
  >- (irule (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``]
        word_arg_clamp_inverse_selected) >>
      qexistsl_tac [`ce`, `sf`, `env`, `ty`] >>
      simp[] >> drule_all abi_decoder_clamp_entry_ok >> simp[]) >>
  gvs[] >>
  irule (INST_TYPE [alpha |-> ``:string``, beta |-> ``:num``]
        word_arg_clamp_inverse_selected) >>
  qexistsl_tac [`ce`, `sf`, `env`, `FlagT nsid`] >>
  simp[is_word_type_def] >>
  gvs[abi_decoder_coherent_flag_iff] >>
  drule_all abi_decoder_clamp_entry_ok >> simp[]
QED

Theorem abi_base_typed_admissible:
  value_has_type (BaseTV bt) v /\ vyper_to_abi_base bt v = SOME av ==>
  abi_vyper_admissible env (BaseT bt) av
Proof
  Cases_on `bt` >> Cases_on `v` >>
  simp[vyper_to_abi_base_def, value_has_type_def] >> rpt strip_tac >>
  gvs[Once abi_vyper_admissible_cases]
  >- simp[within_int_bound_def]
  >- (Cases_on `b` >> simp[])
  >- (Cases_on `b` >> gvs[value_has_type_def, compatible_bound_def]) >>
  qspec_then `word_of_bytes_be l : address` mp_tac w2n_lt >>
  simp[within_int_bound_def, dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem abi_base_typed_conversion_has_type:
  is_word_type (BaseT bt) /\
  value_has_type (BaseTV bt) v /\
  vyper_to_abi_base bt v = SOME av /\
  (?a. has_type (vyper_base_to_abi_type bt) a) ==>
  has_type (vyper_base_to_abi_type bt) av
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bd` >> Cases_on `bd`, all_tac] >>
  Cases_on `v` >>
  simp[is_word_type_def, vyper_to_abi_base_def, value_has_type_def,
    vyper_base_to_abi_type_def] >>
  rpt strip_tac >> Cases_on `a` >>
  gvs[has_type_def, within_int_bound_def, int_bits_bound_def,
    valid_int_bound_def]
  >- (Cases_on `i < 0` >> gvs[PRE_SUB1] >> intLib.COOPER_TAC)
  >- (Cases_on `b` >> simp[])
  >- (Cases_on `i < 0` >> gvs[] >> intLib.COOPER_TAC) >>
  qspec_then `word_of_bytes_be l : address` mp_tac w2n_lt >>
  simp[dimword_def] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem abi_base_word_reflect:
  is_word_type (BaseT bt) /\ value_has_type (BaseTV bt) v /\
  (?a. has_type (vyper_base_to_abi_type bt) a) /\
  32 <= LENGTH bs /\
  word_of_bytes T (0w:bytes32) (TAKE 32 bs) = typed_val_to_w256 (BaseTV bt) v ==>
  vyper_decode_valid_enc (vyper_base_to_abi_type bt) bs /\
  abi_vyper_admissible env (BaseT bt) (dec (vyper_base_to_abi_type bt) bs)
Proof
  strip_tac >>
  `?av. vyper_to_abi_base bt v = SOME av` by
    (Cases_on `bt` >> Cases_on `v` >>
     gvs[value_has_type_def, vyper_to_abi_base_def]) >>
  `has_type (vyper_base_to_abi_type bt) av` by
    (irule abi_base_typed_conversion_has_type >> metis_tac[]) >>
  `LENGTH (enc (vyper_base_to_abi_type bt) av) = 32` by
    (drule (cj 1 enc_has_static_length) >>
     Cases_on `bt` >>
     FIRST [rename1 `BytesT bd` >> Cases_on `bd`, all_tac] >>
     gvs[is_word_type_def, vyper_base_to_abi_type_def, static_length_def,
       is_dynamic_def]) >>
  drule_all abi_encoder_base_source_word >> strip_tac >>
  `TAKE 32 bs = enc (vyper_base_to_abi_type bt) av` by
    (qpat_assum `word_to_bytes _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
     qpat_assum `word_of_bytes _ _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
     irule (GSYM word_bytes_roundtrip) >>
     simp[LENGTH_TAKE_EQ, dividesTheory.divides_def]) >>
  `bs = enc (vyper_base_to_abi_type bt) av ++ DROP 32 bs` by
    metis_tac[TAKE_DROP] >>
  drule_all abi_base_typed_admissible >> strip_tac >>
  qpat_assum `bs = _ ++ _` (fn th => once_rewrite_tac[th]) >>
  conj_tac
  >- (irule valid_enc_vyper_decode_valid_enc >>
      irule (cj 1 enc_valid) >> simp[dimword_def]) >>
  simp[cj 1 dec_enc, dimword_def]
QED

Theorem abi_decoder_primitive_reflect:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  32 <= LENGTH bs /\
  word_of_bytes T (0w:bytes32) (TAKE 32 bs) = w /\
  abi_decoder_clamp_valid clamp w ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >> drule_all abi_decoder_primitive_word_witness >> strip_tac >>
  drule_all abi_decoder_primitive_cases >> strip_tac
  >- (gvs[vyper_to_abi_type_def] >>
      irule abi_base_word_reflect >> metis_tac[]) >>
  gvs[abi_decoder_coherent_flag_iff, value_has_type_def,
    typed_val_to_w256_def, val_to_w256_def, vyper_to_abi_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, val_to_w256_def] >>
  `2 ** ce.ce_flag_n_members (nsid_to_string nsid) <= 2 ** 256` by simp[] >>
  `n < 2 ** 256` by metis_tac[LESS_LESS_EQ_TRANS] >>
  `n < dimword (:256)` by gvs[dimword_def] >>
  qpat_x_assum `n2w n = _` (assume_tac o SYM) >>
  simp[vyper_decode_valid_enc_def, dec_number_def, has_type_def,
    valid_int_bound_def, Once abi_vyper_admissible_cases]
QED

Theorem abi_decoder_primitive_memory_reflect:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  abi_decode_load opc (n2w sb:bytes32) s = w /\
  sb < dimword (:256) /\ 32 <= n /\
  mem_bytes_at sb n (abi_decode_source opc s) = bs /\
  abi_decoder_clamp_valid clamp w ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >>
  `TAKE 32 bs = mem_bytes_at sb 32 (abi_decode_source opc s)` by
    (qspecl_then [`sb`, `0`, `32`, `n`, `abi_decode_source opc s`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  `word_of_bytes T (0w:bytes32) (TAKE 32 bs) = w` by
    gvs[abi_decode_load_bytes] >>
  `LENGTH bs = n` by metis_tac[LENGTH_mem_bytes_at] >>
  irule abi_decoder_primitive_reflect >> metis_tac[]
QED

Theorem abi_decoder_primitive_clamp_width:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord (IntClamp bits F) ==>
  bits <= 256
Proof
  strip_tac >> drule_all abi_decoder_primitive_cases >> strip_tac
  >- (gvs[abi_decoder_coherent_base_iff] >>
      Cases_on `bt` >>
      FIRST [rename1 `BytesT bd` >> Cases_on `bd`, all_tac] >>
      gvs[Once type_to_abi_dec_info_def, type_to_abi_clamp_def,
        abi_decoder_scalar_valid_def, AllCaseEqs()]) >>
  gvs[abi_decoder_coherent_flag_iff, Once type_to_abi_dec_info_def] >>
  Cases_on `ce.ce_flag_n_members (nsid_to_string nsid) >= 256` >> gvs[]
QED

Theorem abi_decoder_primitive_reflected_total:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  B + pos < dimword (:256) /\ 32 <= n /\
  mem_bytes_at (B+pos) n (abi_decode_source opc s) = bs /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs) /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     mem_word_at d t.vs_memory = abi_decode_load opc (n2w (B + pos):bytes32) s /\
     abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     inst_extends st st')
Proof
  strip_tac >>
  `!bits. clamp = IntClamp bits F ==> bits <= 256` by
    (rpt strip_tac >> gvs[] >> drule_all abi_decoder_primitive_clamp_width >> simp[]) >>
  drule_all abi_decoder_clamped_word_total >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)` by
    (irule abi_decoder_primitive_memory_reflect >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem abi_bounded_bytes_vyper_reflect:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  word_of_bytes T (0w:bytes32) (TAKE 32 bs) = n2w c /\
  c < dimword (:256) /\ 32 + c <= LENGTH bs /\ c <= n ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >>
  gvs[vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    vyper_decode_valid_enc_def, dec_def, dec_number_def, dest_NumV_def,
    is_num_value_def, Once abi_vyper_admissible_cases, compatible_bound_def,
    LENGTH_TAKE_EQ, LENGTH_DROP] >> decide_tac
QED

Theorem abi_decoder_bytestring_reflect:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  word_of_bytes T (0w:bytes32) (TAKE 32 bs) = n2w c /\
  c < dimword (:256) /\ 32 + c <= LENGTH bs /\ c <= n ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >> drule_all abi_decoder_bytestring_cases >> strip_tac >>
  irule abi_bounded_bytes_vyper_reflect >> metis_tac[]
QED

Theorem abi_decoder_bytestring_memory_reflect:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring maxlen /\
  abi_decode_load opc (n2w sb:bytes32) s = n2w c /\
  sb < dimword (:256) /\ c < dimword (:256) /\
  32 + c <= n /\ c <= maxlen /\
  mem_bytes_at sb n (abi_decode_source opc s) = bs ==>
  vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)
Proof
  strip_tac >>
  `TAKE 32 bs = mem_bytes_at sb 32 (abi_decode_source opc s)` by
    (qspecl_then [`sb`, `0`, `32`, `n`, `abi_decode_source opc s`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  `word_of_bytes T (0w:bytes32) (TAKE 32 bs) = n2w c` by
    gvs[abi_decode_load_bytes] >>
  `LENGTH bs = n` by metis_tac[LENGTH_mem_bytes_at] >>
  irule abi_decoder_bytestring_reflect >> metis_tac[]
QED

Theorem abi_decoder_bytestring_reflected_total:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ p < dimword (:256) /\
  eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\
  eval_operand dst s = SOME (n2w d) /\
  b+h < dimword (:256) /\ n+32 < dimword (:256) /\
  d+(32+32*((n+31) DIV 32)) < dimword (:256) /\
  (b+h <= d \/ d+(32+32*((n+31) DIV 32)) <= b) /\
  mem_bytes_at (b+p) (h-p) s.vs_memory = bs /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs) /\
   ?c t. c <= n /\ p+32+c <= h /\
     abi_decode_load MLOAD (n2w (b+p) : bytes32) s = n2w c /\
     run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
     mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
     mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
       REPLICATE (32*((c+31) DIV 32)-c) 0w /\
     abi_decode_frame d (32+32*((n+31) DIV 32)) s t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bounded_memory_bytes_total >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  disj2_tac >>
  `b+p < dimword (:256) /\ c < dimword (:256) /\ 32+c <= h-p` by decide_tac >>
  `mem_bytes_at (b+p) (h-p) (abi_decode_source MLOAD s) = bs` by
    simp[abi_decode_source_def] >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)` by
    (drule_all abi_decoder_bytestring_memory_reflect >> simp[]) >>
  asm_rewrite_tac[] >> qexistsl_tac [`c`, `t`] >> asm_rewrite_tac[]
QED
