(* Physical observations at a supplied suffix endpoint. No source execution. *)
Theory abiEncoderSharedSuffix
Ancestors
  abiEncoderSharedContract abiScratchMemberAdapter abiScratchEncoderContract
  abiScratchFootprint abiDecoderContract abiDecoderLoop abiDecoderAllocation
  abiDecoderReentry abiEncoderMemberPhaseRaw compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_encoder_shared_suffix_observations:
  abi_encoder_shared_endpoint (ctx,func) (p,ce,len,limit_st)
    (first,last,b,cap) (at,av,d+off) ready encoded /\
  abi_footprint_disjoint d extent
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap ready) /\
  abi_encode_child_suffix head dp offset len ce = (out,en) /\ fn_has_code ce en func /\
  eval_operand head encoded = SOME (n2w h) /\ eval_operand dp encoded = SOME (n2w slot) /\
  eval_operand offset encoded = SOME (n2w off) /\
  abi_decoder_operand_live ce.cs_next_var dp /\ abi_decoder_operand_live ce.cs_next_var len /\
  d <= h /\ h+32 <= d+off /\ off+LENGTH (enc at av) <= extent /\
  d+extent < dimword (:256) /\
  site IN abi_decoder_ids first last /\ FLOOKUP encoded.vs_allocas site = SOME (slot,32) /\
  en.cs_next_var <= limit_st.cs_next_var /\
  abi_encoder_member_phase_raw ce en encoded actual ==>
  mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
  mem_word_at h actual.vs_memory = n2w off /\
  mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
  eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  actual.vs_current_bb = en.cs_current_bb /\ actual.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~actual.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap ready encoded /\
    fresh_vars_wrt limit_st encoded /\ abi_decoder_budget first last b cap encoded /\
    eval_operand len encoded = SOME (n2w (LENGTH (enc at av))) /\
    ~encoded.vs_halted /\ encoded.vs_current_bb = ce.cs_current_bb /\
    encoded.vs_inst_idx = LENGTH ce.cs_current_insts /\
    mem_bytes_at (d+off) (LENGTH (enc at av)) encoded.vs_memory = enc at av` by
    fs[abi_encoder_shared_endpoint_def, abi_scratch_effect_def] >>
  `abi_footprint_disjoint d extent
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `ready` >> simp[]) >>
  drule_all abi_scratch_dynamic_finish_raw_transport >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> asm_rewrite_tac []
QED
