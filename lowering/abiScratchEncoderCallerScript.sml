(* Run translated encoders from ordinary live-buffer allocation facts.
   TOP-LEVEL: abi_scratch_encoder_caller derives the precise input and scratch
   budget from alloca_inv, distinct owned buffers and numeric allocation credit.
   Complete source memory and generated-site ownership remain caller inputs. *)
Theory abiScratchEncoderCaller
Ancestors
  abiScratchEncoderRecursive abiScratchEncoderRun abiScratchEncoderContract abiScratchEffect
  abiCallerAllocation abiEncoderInput abiEncoderArrayFrame abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop
  compileEnv exprLowering valueEncoding contractABI venomState venomMemDefs finite_map pred_set
  words list arithmetic

Theorem abi_scratch_allocation_input:
  alloca_inv s /\ abi_decoder_budget first last b cap s /\
  FLOOKUP s.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,output_cap) /\ source_id <> output_id /\
  ~(source_id IN abi_decoder_ids first last) /\ ~(output_id IN abi_decoder_ids first last) /\
  abi_encoder_input ei at av sb source_cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  LENGTH (enc at av) <= output_cap ==>
  abi_scratch_input ei at av st src dst sb source_cap d (LENGTH (enc at av)) first last b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `s.vs_alloca_next <= b+cap /\ b+cap < dimword (:256)` by
    (fs[abi_decoder_budget_def] >> decide_tac) >>
  `sb+source_cap <= s.vs_alloca_next` by
    (mp_tac (Q.INST [`live` |-> `source_id`, `loff` |-> `sb:num`, `len` |-> `source_cap:num`,
       `p` |-> `sb:num`, `n` |-> `source_cap:num`] abi_caller_allocation_end) >> simp[]) >>
  `d+output_cap <= s.vs_alloca_next` by
    (mp_tac (Q.INST [`live` |-> `output_id`, `loff` |-> `d:num`, `len` |-> `output_cap:num`,
       `p` |-> `d:num`, `n` |-> `output_cap:num`] abi_caller_allocation_end) >> simp[]) >>
  `abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (mp_tac (Q.INST [`live` |-> `source_id`, `loff` |-> `sb:num`, `len` |-> `source_cap:num`,
       `p` |-> `sb:num`, `n` |-> `source_cap:num`, `ids` |-> `abi_decoder_ids first last`]
       abi_caller_allocation_scratch) >> simp[]) >>
  `abi_footprint_disjoint d (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (mp_tac (Q.INST [`live` |-> `output_id`, `loff` |-> `d:num`, `len` |-> `output_cap:num`,
       `p` |-> `d:num`, `n` |-> `LENGTH (enc at av)`, `ids` |-> `abi_decoder_ids first last`]
       abi_caller_allocation_scratch) >> simp[]) >>
  `sb+source_cap <= d \/ d+output_cap <= sb` by
    (mp_tac (Q.INST [`live` |-> `source_id`, `site` |-> `output_id`, `loff` |-> `sb:num`,
       `len` |-> `source_cap:num`, `q` |-> `d:num`, `sz` |-> `output_cap:num`]
       abi_caller_allocation_separate) >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_input_def, LESS_EQ_REFL] >> decide_tac
QED

Theorem abi_scratch_encoder_caller:
  let cap = initial.vs_alloca_next+32*CARD (abi_decoder_missing first last initial) in
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ cap < dimword (:256) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP initial.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_cap) /\ source_id <> output_id /\
  ~(source_id IN abi_decoder_ids first last) /\ ~(output_id IN abi_decoder_ids first last) /\
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live start.cs_next_var src /\ abi_decoder_operand_live start.cs_next_var dst /\
  LENGTH (enc at av) <= output_cap /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) 0 cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_caller_allocation_budget_zero >> disch_tac >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `st` |-> `start:compile_state`,
    `ei` |-> `type_to_abi_enc_info sf ce ty`, `b` |-> `0:num`,
    `cap` |-> `initial.vs_alloca_next+32*CARD (abi_decoder_missing first last initial)`]
    abi_scratch_allocation_input) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_scratch_encoder (type_to_abi_enc_info sf ce ty)` by simp[abi_scratch_encoder_translation] >>
  drule_all abi_scratch_encoder_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_scratch_effect_source >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
