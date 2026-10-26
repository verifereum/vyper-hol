(* Leaf encoders write only their output and preserve all allocation records.
   TOP-LEVEL: abi_scratch_leaf_effect upgrades that actual execution result to
   the recursive precise effect, without separating buffers from an arena. *)
Theory abiScratchLeafEffect
Ancestors
  abiScratchEncoderContract abiScratchFootprint abiDecoderFootprint abiEncoderSequence
  abiDecoderCorrectWord abiDecoderLoop abiDecoderReentry
  abiDecoderAllocation abiDecoderArrayInitExec abiDecoderPrimitiveLoopFrames
  abiDecoderFrame abiDecoderContract compileEnv venomState finite_map pred_set arithmetic

Theorem abi_scratch_leaf_effect:
  abi_decoder_budget first last b cap s /\ fresh_vars_wrt limit_st t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  abi_decode_frame d sz s t /\ t.vs_halted = s.vs_halted /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t
Proof
  strip_tac >>
  `(abi_decoder_budget first last b cap t <=> abi_decoder_budget first last b cap s)` by
    (irule abi_decoder_budget_transport >> simp[]) >>
  `s.vs_alloca_next <= b+cap` by (drule abi_decoder_budget_frontier >> simp[]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap s t` by
    (rw[abi_scratch_evolution_def] >> gvs[]) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t` by
    (irule abi_decoder_frame_in_footprint >> qexistsl_tac [`d`, `sz`] >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_scratch_sequence_post_effect:
  abi_encoder_sequence_post at av out st limit_st d initial actual /\
  abi_decoder_budget first last b cap initial ==>
  abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual
Proof
  simp_tac bool_ss [abi_encoder_sequence_post_def] >> strip_tac >>
  irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED

Theorem abi_scratch_leaf_reach:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  (?raw. run_inst_seq (emitted_insts st st') initial = OK raw /\
    abi_encoder_sequence_post at av out st limit_st d initial raw) /\
  fn_has_code st st' func /\ abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_sequence_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual` by
    (irule abi_scratch_sequence_post_effect >> asm_simp_tac bool_ss [] >>
     qexists_tac `out` >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> fs[abi_encoder_sequence_post_def, Excl "enc_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_LEAF_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch leaf effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchLeafEffect");
