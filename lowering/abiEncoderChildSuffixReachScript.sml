(* Execute child bookkeeping stores inside the containing function. *)
Theory abiEncoderChildSuffixReach
Ancestors
  abiEncoderChildSuffix abiEncoderChildCode abiDecoderReentry abiDecoderFrame abiDecoderContract
  abiDecoderLoop fragExec instIdxIndep compileEnv emitHelperProps valueEncoding
  venomExecSemantics venomState words list rich_list

Definition abi_encoder_child_suffix_post_def:
  abi_encoder_child_suffix_post out st limit_st h p off len initial actual <=>
    eval_operand out actual = SOME (n2w len) /\ fresh_vars_wrt limit_st actual /\
    actual.vs_memory = (mstore p (n2w (off+len)) (mstore h (n2w off) initial)).vs_memory /\
    abi_decode_footprint_frame [(h,32);(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
End

Theorem abi_encoder_child_suffix_post_inst_idx[simp]:
  abi_encoder_child_suffix_post out st limit_st h p off len initial (actual with vs_inst_idx := ix) <=>
  abi_encoder_child_suffix_post out st limit_st h p off len initial actual
Proof
  simp[abi_encoder_child_suffix_post_def, abi_decode_footprint_frame_def,
    fresh_vars_wrt_def, lookup_var_def, eval_op_inst_idx]
QED

Theorem abi_encode_child_suffix_from_state:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w p) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_encoder_child_suffix_post out st limit_st h p off len initial) (K F)
Proof
  strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encode_child_suffix_sequence >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_child_suffix_post_inst_idx,
    abi_encoder_child_suffix_post_def]
QED

Theorem abi_encode_child_suffix_reach:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\ fn_has_code st st' func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w p) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_encoder_child_suffix_post out st limit_st h p off len initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_suffix_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_encoder_child_suffix_post_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
