(* Precise scratch frames for the actual compiled parent cursor initializer.
   TOP-LEVEL: abi_scratch_encoder_prefix_source preserves a live source
   allocation without separating it from the entire numeric scratch envelope. *)
Theory abiScratchEncoderPrefix
Ancestors
  abiScratchSequence abiScratchFootprint abiCallerAllocation
  abiEncoderComplexPrefixReach abiEncoderComplexPrefix
  abiDecoderFootprint abiDecoderAllocation abiDecoderFrame
  compileEnv venomState valueEncoding finite_map pred_set list arithmetic words

Theorem abi_scratch_encoder_prefix_sequence:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FINITE ids /\ st.cs_next_id IN ids ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    abi_scratch_evolution ids b cap initial actual /\
    abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap initial) initial actual
Proof
  strip_tac >> drule_all abi_encoder_complex_prefix_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') initial = OK actual` >>
  `actual.vs_alloca_next <= b + cap` by
    (qpat_x_assum `abi_decoder_budget first last b cap actual` mp_tac >>
     simp[abi_decoder_budget_def] >> decide_tac) >>
  `abi_scratch_evolution ids b cap initial actual` by
    (mp_tac (Q.SPECL [`emitted_insts st st'`, `initial`, `actual`, `ids`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> simp[]) >>
  `abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap initial) initial actual` by
    (mp_tac (Q.INST [`site` |-> `st.cs_next_id`, `slot` |-> `slot`, `sz` |-> `32`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`]
       abi_scratch_final_slot_frame) >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  pure_rewrite_tac [abi_encoder_complex_prefix_post_def] >>
  qexists_tac `slot` >> simp[]
QED

Theorem abi_scratch_encoder_prefix_source:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FINITE ids /\ st.cs_next_id IN ids /\
  alloca_inv initial /\ FLOOKUP initial.vs_allocas live = SOME (loff,len) /\
  ~(live IN ids) /\ loff <= p /\ p + n <= loff + len ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    mem_bytes_at p n actual.vs_memory = mem_bytes_at p n initial.vs_memory
Proof
  strip_tac >> drule_all abi_scratch_encoder_prefix_sequence >> strip_tac >>
  `initial.vs_alloca_next <= b + cap` by
    (qpat_x_assum `abi_decoder_budget first last b cap initial` mp_tac >>
     simp[abi_decoder_budget_def] >> decide_tac) >>
  drule_all abi_caller_allocation_frame >> strip_tac >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_encoder_prefix_caller:
  let cap = initial.vs_alloca_next + 32 * CARD (abi_decoder_missing first last initial) in
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ alloca_inv initial /\
  cap < dimword (:256) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP initial.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  FLOOKUP initial.vs_allocas live = SOME (loff,len) /\
  ~(live IN abi_decoder_ids first last) /\ loff <= p /\ p + n <= loff + len ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last 0 cap initial actual /\
    mem_bytes_at p n actual.vs_memory = mem_bytes_at p n initial.vs_memory
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_caller_allocation_budget_zero >> strip_tac >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`]
    abi_scratch_encoder_prefix_source) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ENCODER_PREFIX_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch encoder prefix not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEncoderPrefix");
