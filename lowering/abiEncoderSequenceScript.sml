(* Lift proved straight-line encoder execution to its containing function. *)
Theory abiEncoderSequence
Ancestors
  abiEncoderCorrect abiDecoderCorrectWord abiDecoderEffect abiDecoderAllocation abiDecoderLoop
  abiDecoderReentry abiDecoderContract fragExec emitHelperProps compileEnv valueEncoding
  venomState venomExecSemantics instIdxIndep list rich_list words

Definition abi_encoder_sequence_post_def:
  abi_encoder_sequence_post at av out st limit_st d initial actual <=>
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (LENGTH (enc at av)) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
End

Theorem abi_encoder_sequence_post_inst_idx[simp]:
  abi_encoder_sequence_post at av out st limit_st d initial (actual with vs_inst_idx := ix) <=>
  abi_encoder_sequence_post at av out st limit_st d initial actual
Proof
  simp[abi_encoder_sequence_post_def, abi_decode_frame_def, fresh_vars_wrt_def,
    lookup_var_def, eval_op_inst_idx]
QED

Theorem abi_encoder_sequence_post_effect:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  abi_decoder_budget first last b cap initial /\
  (d+LENGTH (enc at av) <= b \/ b+cap <= d) ==>
  abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def] >> strip_tac >>
  irule abi_decoder_scratch_free_effect >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_sequence_from_state:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  (?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_sequence_post at av out st limit_st d initial actual) ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_encoder_sequence_post at av out st limit_st d initial) (K F)
Proof
  strip_tac >> `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >> qexists_tac `actual` >> simp[]
QED

Theorem abi_encoder_sequence_reach:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  (?raw. run_inst_seq (emitted_insts st st') initial = OK raw /\
    abi_encoder_sequence_post at av out st limit_st d initial raw) /\
  fn_has_code st st' func /\ abi_decoder_budget first last b cap initial /\
  (d+LENGTH (enc at av) <= b \/ b+cap <= d) /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_sequence_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decoder_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual` by
    (irule abi_encoder_sequence_post_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `out` >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> fs[abi_encoder_sequence_post_def, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_SEQUENCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder sequence not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderSequence");
