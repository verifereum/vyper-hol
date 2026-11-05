(* Canonical word execution without any interval allocation reservation. *)
Theory ctorAbiActualScalar
Ancestors
  ctorAbiActualReentry abiDecoderPrimitiveCaller abiDecoderClampedWord
  abiDecoderWordTyped abiDecoderLoop abiDecoderContract compileEnv venomState
  abiDecoderReentry abiDecoderReentryPointer abiDecoderVarExtend
  valueEncoding words list

Theorem ctor_actual_word_sequence:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 s.vs_data_section = enc (vyper_to_abi_type env ty) av /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory tv v d t.vs_memory /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `mem_bytes_at sb 32 (abi_decode_source DLOAD s) =
    enc (vyper_to_abi_type env ty) av` by simp[abi_decode_source_def] >>
  drule_all abi_decoder_primitive_clamp >> strip_tac >>
  drule_all (Q.INST [`base_op` |-> `Lit 0w`, `B` |-> `0:num`]
    abi_decoder_clamped_word_copied_window |> SIMP_RULE (srw_ss()) [eval_operand_def]) >> strip_tac >>
  qexists `t` >> simp[] >>
  irule abi_decoder_primitive_canonical_layout >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`clamp`, `sf`] >> simp[]
QED

Theorem ctor_actual_word_reentry:
  compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecPrimWord clamp) st = ((),st') /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ d < dimword (:256) /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d 32 initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb) /\
   eval_operand dst (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w d)` by
    simp[abi_decoder_prune_eval] >>
  `?clean. run_inst_seq (emitted_insts st st')
      (abi_decoder_prune_vars st.cs_next_var initial) = OK clean /\
    val_in_memory tv v d clean.vs_memory /\
    abi_decode_frame d 32 (abi_decoder_prune_vars st.cs_next_var initial) clean /\
    fresh_vars_wrt st' clean /\
    (!op w. eval_operand op (abi_decoder_prune_vars st.cs_next_var initial) = SOME w ==>
      eval_operand op clean = SOME w) /\
    clean.vs_allocas = (abi_decoder_prune_vars st.cs_next_var initial).vs_allocas /\
    clean.vs_alloca_next = (abi_decoder_prune_vars st.cs_next_var initial).vs_alloca_next` by
    (`fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)` by
       simp[abi_decoder_prune_fresh] >>
     `mem_bytes_at sb 32 (abi_decoder_prune_vars st.cs_next_var initial).vs_data_section =
       enc (vyper_to_abi_type env ty) av` by simp[abi_decoder_prune_vars_def] >>
     drule_all (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`]
       ctor_actual_word_sequence) >> simp[]) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all ctor_actual_reentry_sequence >> strip_tac >>
  drule_all abi_decoder_reentry_frame >> strip_tac >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  qexists `actual` >> simp[] >>
  rpt strip_tac >> irule abi_decoder_vars_extend_eval >>
  qexistsl [`initial.vs_vars`, `clean`] >> simp[] >>
  first_x_assum irule >> simp[abi_decoder_prune_eval]
QED
