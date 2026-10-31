(* Pure incoming data and allocator conditions for lower_abi_encode without a
   method ID. Complete source memory is required, including sparse defaults. *)
Theory abiBuiltinEncodePre
Ancestors
  abiBuiltinAllocation abiEncoderCorrect abiEncoderInput abiDecoderAllocation abiDecoderReentry
  abiDecoderContract compileEnv venomState finite_map words list arithmetic

Definition abi_builtin_encode_no_method_pre_def:
  abi_builtin_encode_no_method_pre ei at av st src sb source_cap p maxlen first last b cap s <=>
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
    sb+source_cap < dimword (:256) /\ p+32+maxlen < dimword (:256) /\
    LENGTH (enc at av) <= maxlen /\
    (sb+source_cap <= p \/ p+32+maxlen <= sb) /\
    (sb+source_cap <= b \/ b+cap <= sb) /\
    (p+32+maxlen <= b \/ b+cap <= p) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,maxlen+32)) /\
    st.cs_next_id < first /\ first <= st.cs_next_id+2 /\
    abi_decoder_budget first last b cap
      (abi_builtin_allocate_state st.cs_next_id (maxlen+32) s)
End

Theorem abi_builtin_encode_no_method_ready:
  abi_builtin_encode_no_method_pre ei at av st src sb source_cap p maxlen first last b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (maxlen+32) initial prepared /\
  eval_operand dst prepared = SOME (n2w (p+32)) /\
  st.cs_next_var <= ready.cs_next_var /\ abi_decoder_operand_live ready.cs_next_var dst ==>
  abi_encoder_pre ei at av ready src dst sb source_cap (p+32) b cap prepared /\
  abi_decoder_budget first last b cap prepared /\
  (p+32+LENGTH (enc at av) <= b \/ b+cap <= p)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_encode_no_method_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_no_method_pre_def]) >>
  `abi_decoder_budget first last b cap prepared` by
    (drule abi_builtin_allocation_frame_budget >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `eval_operand src prepared = SOME (n2w sb)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_encoder_pre_def] >> decide_tac
QED
