(* Concrete encoder leaves satisfy the recursive containing-function contract. *)
Theory abiEncoderCorrectLeaves
Ancestors
  abiEncoderCorrect abiEncoderSequence abiEncoderLeafCode abiEncoderAdmissible
  abiEncoderReentryLeaves abiEncoderBytesCorrect abiEncoderBytesCode abiEncoderInputLayout
  abiEncoderInput abiDecoderEffect abiDecoderAllocation abiDecoderLoop abiDecoderReentry abiDecoderContract
  abiEncoder compileEnv emitHelper valueEncoding contractABI venomState venomExecSemantics
  emitHelperProps words list rich_list arithmetic

Theorem abi_encoder_correct_word:
  abi_encoder_correct AbiPrimWord
Proof
  simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  `sb < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_word_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK actual` >>
  `abi_encoder_sequence_post at av out start limit_st d initial actual` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  mp_tac (Q.INST [`ei` |-> `AbiPrimWord`, `st` |-> `start`, `st'` |-> `end_st`]
    abi_encode_static_leaf_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_static_leaf_def] >> strip_tac >>
  irule abi_encoder_sequence_reach >> asm_simp_tac bool_ss [] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_correct_copy:
  abi_encoder_correct (AbiCopy sz)
Proof
  simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  `LENGTH (enc at av) = sz` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o REWRITE_RULE [abi_encoder_input_copy_iff]) >>
     drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK actual` >>
  `abi_encoder_sequence_post at av out start limit_st d initial actual` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  mp_tac (Q.INST [`ei` |-> `AbiCopy sz`, `st` |-> `start`, `st'` |-> `end_st`]
    abi_encode_static_leaf_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_static_leaf_def] >> strip_tac >>
  irule abi_encoder_sequence_reach >> asm_simp_tac bool_ss [] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_correct_bytes:
  abi_encoder_correct (AbiBytestring maxlen)
Proof
  simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  `sb < dimword (:256)` by decide_tac >>
  drule_all abi_encoder_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts start end_st) initial = OK actual` >>
  `abi_encoder_sequence_post at av out start limit_st d initial actual` by
    asm_simp_tac bool_ss [abi_encoder_sequence_post_def] >>
  drule abi_encode_bytes_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start end_st)` by fs[EVERY_CONJ] >>
  irule abi_encoder_sequence_reach >> asm_simp_tac bool_ss [] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_empty_input:
  abi_encoder_input (AbiComplex []) at av sb source_cap mem ==>
  av = ListV [] /\ enc at av = []
Proof
  gvs[abi_encoder_complex_input_iff, abi_encoder_tuple_type_def, abi_encoder_member_span_def,
    enc_def, LET_THM] >> strip_tac >> gvs[enc_def, LET_THM, REV_DEF]
QED

Theorem abi_encoder_correct_empty:
  abi_encoder_correct (AbiComplex [])
Proof
  simp_tac bool_ss [abi_encoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  rename1 `abi_encoder_pre (AbiComplex []) at av start src dst sb source_cap d b cap initial` >>
  qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >>
  drule abi_encoder_empty_input >> strip_tac >>
  `abi_decoder_effect first last start.cs_next_id start.cs_next_id start.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial initial` by
    (irule abi_decoder_effect_refl >> asm_simp_tac bool_ss []) >>
  qexists_tac `initial` >>
  asm_simp_tac (srw_ss()) [mem_bytes_at_def, eval_operand_def, abi_decode_sim_refl]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CORRECT_LEAVES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder recursive leaf not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderCorrectLeaves");
