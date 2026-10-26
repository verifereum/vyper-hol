(* Apply the precise recursive contract and retain parent observations.
   TOP-LEVEL: abi_scratch_dynamic_child_core executes a compiled child under
   its constructor induction hypothesis; source data and parent slots survive. *)
Theory abiScratchEncoderRun
Ancestors
  abiScratchEncoderContract abiScratchEffectProtected abiEncoderCounters
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry
  abiDecoderContract abiDecoderLoop compileEnv valueEncoding contractABI
  venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_encoder_run:
  abi_scratch_encoder ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
    first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> qpat_x_assum `abi_scratch_encoder _` (mp_tac o PURE_REWRITE_RULE [abi_scratch_encoder_def]) >>
  disch_then (qspecl_then [`dst`, `src`, `start`, `end_st`, `out`, `func`, `ctx`, `first`, `last`,
    `b`, `cap`, `limit_st`, `initial`, `at`, `av`, `sb`, `source_cap`, `d`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_dynamic_child_core:
  abi_scratch_encoder ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
    first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live start.cs_next_var head /\ abi_decoder_operand_live start.cs_next_var offset /\
  abi_decoder_operand_live start.cs_next_var dyn_ptr /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand offset initial = SOME (n2w off) /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ first <= site /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    eval_operand head actual = SOME (n2w h) /\ eval_operand offset actual = SOME (n2w off) /\
    eval_operand dyn_ptr actual = SOME (n2w slot) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ mload slot actual = mload slot initial /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> drule abi_encoder_counters >> strip_tac >>
  drule_all abi_scratch_encoder_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `site IN abi_decoder_ids first last /\
   ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o List.last o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def])) >>
  drule_all abi_scratch_effect_slot >> strip_tac >>
  drule_all abi_scratch_effect_source >> disch_then assume_tac >>
  imp_res_tac abi_scratch_effect_operand >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_scratch_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ENCODER_RUN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch child execution not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEncoderRun");
