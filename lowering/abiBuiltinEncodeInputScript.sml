(* Pure input/resources for either method-ID choice. The source is separate
   from both the complete returned buffer and the full 32-byte prefix store. *)
Theory abiBuiltinEncodeInput
Ancestors
  abiBuiltinEncodePre abiBuiltinEncodeSetup abiBuiltinAllocation abiEncoderCorrect
  abiEncoderInput abiDecoderAllocation abiDecoderReentry abiDecoderContract compileEnv
  venomState finite_map words list arithmetic

Definition abi_builtin_encode_pre_def:
  abi_builtin_encode_pre ei at av st method_id_opt src sb source_cap p maxlen first last b cap s <=>
    let mid_size = case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4 in
    let outsz = maxlen+32+mid_size in
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
    sb+source_cap < dimword (:256) /\ p+outsz < dimword (:256) /\ LENGTH (enc at av) <= maxlen /\
    (sb+source_cap <= p \/ p+outsz <= sb) /\
    (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) /\
    (sb+source_cap <= b \/ b+cap <= sb) /\ (p+outsz <= b \/ b+cap <= p) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
    st.cs_next_id < first /\ first <= st.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
    abi_decoder_budget first last b cap (abi_builtin_allocate_state st.cs_next_id outsz s)
End

Theorem abi_builtin_encode_pre_none:
  abi_builtin_encode_pre ei at av st NONE src sb source_cap p maxlen first last b cap s <=>
  abi_builtin_encode_no_method_pre ei at av st src sb source_cap p maxlen first last b cap s
Proof
  simp[abi_builtin_encode_pre_def, abi_builtin_encode_no_method_pre_def, LET_THM,
    AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_builtin_encode_method_ready:
  abi_builtin_encode_pre ei at av st (SOME mid) src sb source_cap p maxlen first last b cap initial /\
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (maxlen+36) p 32 initial prepared /\
  eval_operand dst prepared = SOME (n2w (p+36)) /\
  st.cs_next_var <= ready.cs_next_var /\ abi_decoder_operand_live ready.cs_next_var dst ==>
  abi_encoder_pre ei at av ready src dst sb source_cap (p+36) b cap prepared /\
  abi_decoder_budget first last b cap prepared /\
  (p+36+LENGTH (enc at av) <= b \/ b+cap <= p)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_encode_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss())
      [abi_builtin_encode_pre_def, LET_THM, GSYM ADD_ASSOC]) >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `site` |-> `st.cs_next_id`,
    `outsz` |-> `maxlen+36:num`, `write_size` |-> `32:num`,
    `s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`]
    abi_builtin_encode_setup_frame_input) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (drule abi_builtin_encode_setup_frame_budget >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
  `eval_operand src prepared = SOME (n2w sb)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_encoder_pre_def] >> decide_tac
QED
