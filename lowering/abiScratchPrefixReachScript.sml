(* Precise cursor-initialization frames in the containing function.
   TOP-LEVEL: abi_scratch_encoder_prefix_input_caller derives the allocation
   budget and preserves complete encoder inputs from a live source allocation. *)
Theory abiScratchPrefixReach
Ancestors
  abiScratchEncoderPrefix abiScratchFootprint abiCallerAllocation abiEncoderComplexPrefix
  abiEncoderSequence abiEncoderInputFrame abiEncoderInput abiDecoderFootprint
  abiDecoderAllocation abiDecoderFrame abiDecoderLoop compileEnv valueEncoding venomState
  finite_map pred_set words list arithmetic

Theorem abi_scratch_inst_idx:
  (abi_scratch_evolution ids b cap s (t with vs_inst_idx := ix) <=>
    abi_scratch_evolution ids b cap s t) /\
  (abi_decode_footprint_frame fp s (t with vs_inst_idx := ix) <=>
    abi_decode_footprint_frame fp s t)
Proof
  simp[abi_scratch_evolution_def, abi_decode_footprint_frame_def]
QED

Theorem abi_scratch_encoder_prefix_reach:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FINITE ids /\ st.cs_next_id IN ids /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution ids b cap initial actual /\
    abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap initial) initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_encoder_prefix_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK encoded` >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~encoded.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[abi_scratch_inst_idx]
QED

Theorem abi_scratch_encoder_prefix_input:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FINITE ids /\ st.cs_next_id IN ids /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv initial /\ FLOOKUP initial.vs_allocas live = SOME (loff,len) /\
  ~(live IN ids) /\ loff <= sb /\ sb + source_cap <= loff + len /\
  abi_encoder_input ei at av sb source_cap initial.vs_memory ==>
  ?actual. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution ids b cap initial actual /\
    abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap initial) initial actual /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_encoder_prefix_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `initial.vs_alloca_next <= b + cap` by
    (qpat_x_assum `abi_decoder_budget first last b cap initial` mp_tac >>
     simp[abi_decoder_budget_def] >> decide_tac) >>
  drule_all abi_caller_allocation_scratch >> disch_then assume_tac >>
  drule_all abi_encoder_input_frame >> disch_then assume_tac >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_encoder_prefix_input_caller:
  let cap = initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial) in
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  alloca_inv initial /\ cap < dimword (:256) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP initial.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP initial.vs_allocas live = SOME (loff,len) /\
  ~(live IN abi_decoder_ids first last) /\ loff <= sb /\ sb + source_cap <= loff + len /\
  abi_encoder_input ei at av sb source_cap initial.vs_memory ==>
  ?actual. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last 0 cap initial actual /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_caller_allocation_budget_zero >> strip_tac >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`]
    abi_scratch_encoder_prefix_input) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >> qexists_tac `actual` >> simp[]
QED
