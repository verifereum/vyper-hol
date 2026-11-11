(* Readable primitive heads: reflection without canonical-input assumptions. *)
Theory abiDecoderPrimitiveReflected
Ancestors
  abiDecoderPrimitiveConversion abiBoundedLeafExecution abiDecoderClampedWord
  abiBoundedLeafReflection abiDecoderWordTyped abiDecoderCoherence
  abiDecoderContract abiDecoderTypedCompose valueEncoding valueEncodingProofs
  abiEncoder compileEnv venomState words list arithmetic
  venomMemProps abiEncoderWordSource abiCanonicalHeadSize
  abiDecoderAbortReentry abiDecoderReentryPointer abiDecoderReentry abiDecoderVarExtend
  abiDecoderReservation

Theorem abi_decoder_readable_primitive_total:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  has_type (vyper_to_abi_type env ty) av /\
  eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\
  B + pos < dimword (:256) /\ d < dimword (:256) /\
  32 <= LENGTH bs /\
  mem_bytes_at (B+pos) (LENGTH bs) s.vs_memory = bs /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  ?t v. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
    value_has_type tv v /\
    mem_word_at d t.vs_memory = typed_val_to_w256 tv v /\
    val_in_memory tv v d t.vs_memory /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs) /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  strip_tac >>
  `!bits. clamp = IntClamp bits F ==> bits <= 256` by
    (rpt strip_tac >> gvs[] >> drule_all abi_decoder_primitive_clamp_width >> simp[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_total >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  `word_of_bytes T (0w:bytes32) (TAKE 32 bs) =
    abi_decode_load MLOAD (n2w (B+pos):bytes32) s` by
    (`TAKE 32 bs = mem_bytes_at (B+pos) 32 s.vs_memory` by
       (qspecl_then [`B+pos`, `0`, `32`, `LENGTH bs`, `s.vs_memory`]
         mp_tac mem_bytes_at_window >> simp[]) >>
     gvs[abi_decode_load_bytes, abi_decode_source_def]) >>
  `?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
       value_has_type tv v /\
       typed_val_to_w256 tv v = abi_decode_load MLOAD (n2w (B+pos):bytes32) s /\
       vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
       abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs)` by
    (irule abi_decoder_primitive_reflected_conversion >> metis_tac[]) >>
  `val_in_memory tv v d t.vs_memory` by
    (drule_all abi_decoder_primitive_cases >> strip_tac >> gvs[]
     >- (Cases_on `bt` >> Cases_on `v` >>
         gvs[vyperTypingTheory.value_has_type_def, is_word_type_def,
             val_in_memory_def, typed_val_to_w256_def] >>
         Cases_on `b` >> gvs[is_word_type_def, val_in_memory_def,
                            typed_val_to_w256_def]) >>
     Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def, val_in_memory_def,
         typed_val_to_w256_def]) >>
  disj2_tac >> metis_tac[]
QED

Theorem abi_decoder_readable_primitive_reentry:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  has_type (vyper_to_abi_type env ty) av /\
  eval_operand src initial = SOME (n2w pos) /\
  eval_operand base_op initial = SOME (n2w B) /\
  eval_operand dst initial = SOME (n2w d) /\
  B + pos < dimword (:256) /\ d < dimword (:256) /\
  32 <= LENGTH bs /\
  mem_bytes_at (B+pos) (LENGTH bs) initial.vs_memory = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  (?t. run_inst_seq (emitted_insts st st') initial = Abort Revert_abort t) \/
  ?t v. run_inst_seq (emitted_insts st st') initial = OK t /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
    value_has_type tv v /\ val_in_memory tv v d t.vs_memory /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bs) /\
    abi_decode_frame d 32 initial t /\ fresh_vars_wrt limit_st t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_halted = initial.vs_halted /\ inst_extends st st'
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w pos) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w d) /\
   eval_operand base_op (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w B)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `mem_bytes_at (B+pos) (LENGTH bs)
    (abi_decoder_prune_vars st.cs_next_var initial).vs_memory = bs` by
    simp[abi_decoder_prune_vars_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)` by
    irule abi_decoder_prune_fresh >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_readable_primitive_total >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  disj2_tac >> qexistsl [`actual`, `v`] >>
  gvs[abi_decoder_prune_vars_def]
QED

(* The payload guard owns readability for static primitive array elements.
   The count-layout bound must be supplied from coherent type/cap metadata. *)
Theorem abi_decoder_primitive_array_head_readable:
  cnt <= max_count /\ 32 * max_count < dimword (:256) /\
  start + 32 < dimword (:256) /\ hi < dimword (:256) /\
  start + 32 <= (start + 32 + cnt * 32) MOD dimword (:256) /\
  (start + 32 + cnt * 32) MOD dimword (:256) <= hi /\ j < cnt ==>
  start + 32 + j * 32 + 32 <= hi
Proof
  strip_tac >>
  `cnt * 32 < dimword (:256) /\
   start + 32 + cnt * 32 < 2 * dimword (:256)` by decide_tac >>
  `start + 32 + cnt * 32 < dimword (:256)` by
    (spose_not_then assume_tac >>
     `(start + 32 + cnt * 32) MOD dimword (:256) =
      start + 32 + cnt * 32 - dimword (:256)` by
       (irule MOD_UNIQUE >> qexists `1` >> simp[] >> decide_tac) >>
     decide_tac) >>
  gvs[LESS_MOD] >> decide_tac
QED

Theorem abi_decoder_primitive_complex_head_readable:
  src + static_size <= hi /\ offset + 32 <= static_size ==>
  src + offset + 32 <= hi
Proof
  decide_tac
QED

Theorem abi_decoder_primitive_root_head_readable:
  32 <= min_size /\ min_size <= data_size /\ min_size <= cap ==>
  32 <= MIN data_size cap
Proof
  simp[MIN_DEF] >> decide_tac
QED
