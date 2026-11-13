Theory ctorAbiActualBytes
Ancestors
  ctorAbiActualReentry ctorAbiActualWorld ctorAbiActualNarrow
  abiDecoderBytes abiDecoderBytesTyped abiDecoderBytesFrame abiCanonicalBytes
  abiDecoderString abiDecoderBytestring abiDecoderBytestringCases vyperABI vyperTyping
  abiDecoderReentryPointer abiDecoderReentry abiDecoderVarExtend
  abiDecoderContract abiDecoderTypedContract abiEncoder compileEnv abiEncoderRegisteredEffect
  valueEncoding valueEncodingDefs valueEncodingProps vyperValue contractABI venomState
  venomExecSemantics venomInst words list arithmetic finite_map

Theorem ctor_actual_bytes_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  LENGTH bs <= n /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) s.vs_data_section =
    enc (Bytes NONE) (contractABI$BytesV bs) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    abi_encoder_registered_effect {} [(d,abi_decode_bytes_copy_size n)] s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `n+32 <= abi_decode_bytes_copy_size n` by simp[abi_decoder_bytes_copy_size] >>
  `n < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))
    (abi_decode_source DLOAD s) = enc (Bytes NONE) (contractABI$BytesV bs)` by
    simp[abi_decode_source_def, Excl "enc_def"] >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >> simp[]) >>
  `32 + LENGTH bs <= LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))` by
    simp[canonical_bytes_payload_length] >>
  mp_tac (Q.INST [`opc` |-> `DLOAD`, `c` |-> `LENGTH (bs:word8 list)`,
    `pos` |-> `src:operand`, `p` |-> `sb:num`]
    abi_decode_bytes_zero_base_sequence) >>
  impl_tac >-
    (asm_simp_tac bool_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
     disj2_tac >> qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_rewrite_tac[] >>
     disch_then (qx_choose_then `h` strip_assume_tac) >>
     qexists `h` >> simp[Excl "enc_def"] >> decide_tac) >> strip_tac >>
  `val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)` by
    (simp[val_wf_def, GSYM (cj 2 abi_decoder_bytes_copy_size)] >> decide_tac) >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d t.vs_memory` by
    (irule canonical_bytes_copied_layout >>
     reverse conj_tac >- (first_assum ACCEPT_TAC) >>
     qexistsl [`abi_decode_bytes_copy_size n`, `sb`, `abi_decode_source DLOAD s`] >>
     simp[GSYM (cj 2 abi_decoder_bytes_copy_size)]) >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\ i.inst_opcode <> ALLOCA)
    (emitted_insts st st')` by
    (simp_tac bool_ss [EVERY_CONJ] >> conj_tac >- (first_assum ACCEPT_TAC) >>
     rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. ~is_terminator _ /\ _) _` mp_tac >>
     simp_tac bool_ss [EVERY_MEM] >> disch_then drule >>
     strip_tac >> strip_tac >> gvs[is_alloca_op_def]) >>
  drule_all ctor_actual_sequence_no_alloca >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_scratch_free_effect >>
  disch_then (qspecl_then [`site`, `{}`, `fn`, `ctx`] strip_assume_tac) >>
  qexists `t` >> simp[]
QED

Theorem ctor_actual_bytes_ceiling_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  LENGTH bs <= n /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) initial.vs_data_section =
    enc (Bytes NONE) (contractABI$BytesV bs) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    abi_encoder_registered_effect {} [(d,abi_decode_bytes_copy_size n)] initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `pruned = abi_decoder_prune_vars st.cs_next_var initial` >>
  mp_tac (Q.INST [`s` |-> `pruned:venom_state`] ctor_actual_bytes_sequence) >>
  impl_tac >-
    (asm_simp_tac bool_ss [Abbr `pruned`, abi_decoder_prune_eval,
      abi_decoder_prune_fresh, abi_decoder_prune_vars_def] >>
     simp[abi_decoder_prune_eval, Excl "enc_def"]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') pruned = OK clean` >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  qunabbrev_tac `pruned` >>
  drule_all ctor_actual_reentry_sequence >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule_all abi_decoder_prefix_vars_extend >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  qexists `actual` >>
  gvs[abi_decoder_prune_vars_def, abi_encoder_registered_effect_def, Excl "enc_def"] >>
  metis_tac[]
QED

Theorem ctor_actual_bytestring_metadata:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv root_di av v ==>
  ?bs. av = contractABI$BytesV bs /\ LENGTH bs <= n /\
    enc (vyper_to_abi_type env ty) av = enc (Bytes NONE) (contractABI$BytesV bs) /\
    type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
    (!d mem. val_in_memory tv v d mem <=>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d mem)
Proof
  strip_tac >> drule abi_decoder_bytestring_cases >>
  disch_then (qspec_then `n` mp_tac) >> asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  Cases_on `av` >>
  gvs[abi_decoder_metadata_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    has_type_def, abi_to_vyper_def, AllCaseEqs(),
    value_has_type_def, abi_decode_bytes_copy_size_def, type_memory_bytes_def,
    abi_decoder_string_memory]
QED

Theorem ctor_actual_bytestring_ceiling_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecBytestring n) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  type_memory_bytes ce ty < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section =
    enc (vyper_to_abi_type env ty) av /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) initial actual /\
    fresh_vars_wrt limit_st actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    abi_encoder_registered_effect {} [(d,type_memory_bytes ce ty)] initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_bytestring_metadata >> strip_tac >>
  drule ctor_actual_bytes_ceiling_sequence >>
  disch_then (qspecl_then [`sb`, `limit_st`, `initial`, `d`, `bs`] mp_tac) >>
  impl_tac >- (simp[Excl "enc_def"] >> metis_tac[]) >>
  strip_tac >> qexists `actual` >> fs[Excl "enc_def"]
QED
