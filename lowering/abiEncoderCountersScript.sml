(* Both SSA and instruction-id counters increase across recursive encoders. *)
Theory abiEncoderCounters
Ancestors
  abiEncoderAppend abiEncoder compileEnv emitHelper context venomInst arithmetic pair

Definition abi_encoder_counters_mono_def:
  abi_encoder_counters_mono (action : 'a compiler) <=>
    !st. st.cs_next_var <= (SND (action st)).cs_next_var /\
      st.cs_next_id <= (SND (action st)).cs_next_id
End

Theorem abi_encoder_counters_mono_bind:
  abi_encoder_counters_mono action /\ (!v. abi_encoder_counters_mono (next v)) ==>
  abi_encoder_counters_mono (comp_bind action next)
Proof
  rw[abi_encoder_counters_mono_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  metis_tac[LESS_EQ_TRANS, SND]
QED

Theorem abi_encoder_counters_mono_ignore_bind:
  abi_encoder_counters_mono action /\ abi_encoder_counters_mono next ==>
  abi_encoder_counters_mono (comp_ignore_bind action next)
Proof
  simp[comp_ignore_bind_def] >> strip_tac >>
  irule abi_encoder_counters_mono_bind >> simp[]
QED

Theorem abi_encoder_counters_mono_return:
  abi_encoder_counters_mono (comp_return v)
Proof
  simp[abi_encoder_counters_mono_def, comp_return_def]
QED

Theorem abi_encoder_counters_mono_prims:
  (!opc ops. abi_encoder_counters_mono (emit_op opc ops)) /\
  (!opc ops. abi_encoder_counters_mono (emit_void opc ops)) /\
  (!opc ops outs. abi_encoder_counters_mono (emit_inst opc ops outs)) /\
  (!prefix. abi_encoder_counters_mono (fresh_label prefix)) /\
  (!lbl. abi_encoder_counters_mono (new_block lbl))
Proof
  simp[abi_encoder_counters_mono_def, emit_op_def, emit_void_def, emit_inst_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, fresh_label_def, new_block_def, LET_THM]
QED

fun encode_counters_tac extra g =
  (FIRST [FIRST_PROVE [asm_simp_tac (srw_ss())
      (extra @ [abi_encoder_counters_mono_return, abi_encoder_counters_mono_prims, LET_THM])],
    first_x_assum (fn th => FIRST_PROVE [irule (SRULE[] th) >> asm_simp_tac (srw_ss()) []]),
    ho_match_mp_tac abi_encoder_counters_mono_bind >> conj_tac
      >- encode_counters_tac extra >> rpt gen_tac >> encode_counters_tac extra,
    ho_match_mp_tac abi_encoder_counters_mono_ignore_bind >> conj_tac >> encode_counters_tac extra,
    IF_CASES_TAC >> fs[] >> encode_counters_tac extra]) g;

Theorem abi_encoder_counters_mono_alloc:
  abi_encoder_counters_mono (compile_alloc_buffer n)
Proof
  rewrite_tac [compile_alloc_buffer_def] >> encode_counters_tac []
QED

Theorem abi_encoder_counters_mono_static:
  abi_encoder_counters_mono (compile_abi_encode_static dst src)
Proof
  rewrite_tac [compile_abi_encode_static_def] >> encode_counters_tac []
QED

Theorem abi_encoder_counters_mono_static_info:
  !dst src ei. abi_encoder_counters_mono (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >> rewrite_tac [compile_abi_encode_static_info_def] >>
  encode_counters_tac [abi_encoder_counters_mono_static]
QED

Theorem abi_encoder_counters_mono_static_loop:
  abi_encoder_counters_mono (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rewrite_tac [compile_abi_encode_dyn_static_loop_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  encode_counters_tac [abi_encoder_counters_mono_alloc, abi_encoder_counters_mono_static_info]
QED

Theorem abi_encoder_counters_mono_mutual:
  (!dst src ei dyn off ptr. abi_encoder_counters_mono (compile_abi_encode_child dst src ei dyn off ptr)) /\
  (!dst src ei. abi_encoder_counters_mono (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr. abi_encoder_counters_mono (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len. abi_encoder_counters_mono (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt (disch_then strip_assume_tac) >> ONCE_REWRITE_TAC [compile_abi_encode_child_def] >>
  simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  TRY (drule_all abi_encoder_complex_append_bindings >> strip_tac) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  encode_counters_tac [abi_encoder_counters_mono_static, abi_encoder_counters_mono_alloc,
    abi_encoder_counters_mono_static_loop]
QED

Theorem abi_encoder_counters:
  compile_abi_encode_to_buf dst src ei st = (out,st') ==>
  st.cs_next_var <= st'.cs_next_var /\ st.cs_next_id <= st'.cs_next_id
Proof
  metis_tac[cj 2 abi_encoder_counters_mono_mutual, abi_encoder_counters_mono_def, SND]
QED
