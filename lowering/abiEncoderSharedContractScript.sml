(* A single endpoint for the shared recursive encoder derivation. *)
Theory abiEncoderSharedContract
Ancestors
  abiEncoderOpenInput abiEncoderOpenInputFrame abiEncoderExtendSim
  abiEncoderRegisteredEffect abiEncoderPrimitiveEffect abiScratchEncoderContract
  abiDecoderAllocation abiDecoderFootprint abiDecoderContract abiDecoderLoop
  abiDecoderReentry abiEncoderInput abiEncoder compileEnv fragExec
  valueEncoding contractABI venomMemDefs venomState instIdxIndep words list arithmetic

Definition abi_encoder_shared_input_def:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s <=>
    abi_encoder_open_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    LENGTH (enc at av) <= output_size /\
    sb+source_cap < dimword (:256) /\ d+output_size < dimword (:256) /\
    venomMemDefs$regions_disjoint (sb,source_cap) (d,output_size) /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
End

Definition abi_encoder_shared_endpoint_def:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual <=>
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial actual /\
    abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
      [(d,LENGTH (enc at av))] initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual
End

Definition abi_encoder_shared_def:
  abi_encoder_shared ei <=>
    !dst src start end_st out func ctx first last b cap limit_st initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei start = (out,end_st) /\ fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_encoder_shared_input (ei,at,av) (start,src,dst) (sb,source_cap) (d,LENGTH (enc at av))
      (first,last,b,cap) initial /\
    abi_decoder_budget first last b cap initial /\
    first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?actual. abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual
End

Theorem abi_scratch_input_shared:
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap s ==>
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s
Proof
  simp_tac bool_ss [abi_scratch_input_def, abi_encoder_shared_input_def,
    abi_encoder_zero_aware_separation] >> strip_tac >>
  drule abi_encoder_input_open >> simp[]
QED

Theorem abi_encoder_shared_input_typed:
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap) (d,output_size) (first,last,b,cap) s /\
  abi_encoder_input ei at av sb source_cap s.vs_memory /\
  (sb+source_cap <= d \/ d+output_size <= sb) ==>
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap s
Proof
  simp[abi_encoder_shared_input_def, abi_scratch_input_def]
QED

Theorem abi_encoder_shared_endpoint_bytes:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_output:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  eval_operand out actual = SOME (n2w (LENGTH (enc at av)))
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_scratch:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_registered:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
    [(d,LENGTH (enc at av))] initial actual
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_alloca_inv:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual /\
  alloca_inv initial ==> alloca_inv actual
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_block:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  actual.vs_current_bb = end_st.cs_current_bb
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_index:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  actual.vs_inst_idx = LENGTH end_st.cs_current_insts
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_nonhalted:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  ~actual.vs_halted
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_extend_sim:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  abi_encoder_extend_sim ctx func initial actual
Proof
  simp[abi_encoder_shared_endpoint_def]
QED

Theorem abi_encoder_shared_endpoint_sim:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st) (first,last,b,cap) (at,av,d) initial actual ==>
  abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule abi_encoder_shared_endpoint_extend_sim >>
  simp[abi_encoder_extend_sim_sim]
QED

Theorem abi_encoder_shared_run:
  abi_encoder_shared ei /\
  compile_abi_encode_to_buf dst src ei start = (out,end_st) /\ fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (start,src,dst) (sb,source_cap) (d,LENGTH (enc at av))
    (first,last,b,cap) initial /\
  abi_decoder_budget first last b cap initial /\
  first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    (first,last,b,cap) (at,av,d) initial actual
Proof
  simp_tac bool_ss [abi_encoder_shared_def] >> metis_tac[]
QED

Theorem abi_encoder_shared_scratch:
  abi_encoder_shared ei ==> abi_scratch_encoder ei
Proof
  strip_tac >> simp_tac bool_ss [abi_scratch_encoder_def] >> rpt strip_tac >>
  drule abi_scratch_input_shared >> strip_tac >>
  `?actual. abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    (first,last,b,cap) (at,av,d) initial actual` by
    (irule abi_encoder_shared_run >> asm_simp_tac bool_ss [] >>
     metis_tac[]) >>
  qexists_tac `actual` >>
  fs[abi_encoder_shared_endpoint_def, abi_encoder_extend_sim_sim]
QED

Theorem abi_encoder_shared_input_inst_idx[simp]:
  abi_encoder_shared_input source code window output resources (s with vs_inst_idx := ix) <=>
  abi_encoder_shared_input source code window output resources s
Proof
  PairCases_on `source` >> PairCases_on `code` >> PairCases_on `window` >>
  PairCases_on `output` >> PairCases_on `resources` >>
  simp[abi_encoder_shared_input_def, eval_op_inst_idx,
    abi_decoder_child_scratch_def]
QED

Theorem abi_encoder_shared_endpoint_end_index:
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    resources value initial actual ==>
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    resources value initial (actual with vs_inst_idx := LENGTH end_st.cs_current_insts)
Proof
  PairCases_on `resources` >> PairCases_on `value` >>
  strip_tac >>
  `actual.vs_inst_idx = LENGTH end_st.cs_current_insts` by
    (drule abi_encoder_shared_endpoint_index >> simp[]) >>
  `actual with vs_inst_idx := LENGTH end_st.cs_current_insts = actual` by
    (simp[venom_state_component_equality]) >> simp[]
QED

Theorem abi_encoder_shared_endpoint_intro:
  mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
  eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
  abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
    limit_st d (LENGTH (enc at av)) b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids start.cs_next_id end_st.cs_next_id)
    [(d,LENGTH (enc at av))] initial actual /\
  (alloca_inv initial ==> alloca_inv actual) /\
  actual.vs_current_bb = end_st.cs_current_bb /\
  actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
  ~actual.vs_halted /\ abi_encoder_extend_sim ctx func initial actual ==>
  abi_encoder_shared_endpoint (ctx,func) (start,end_st,out,limit_st)
    (first,last,b,cap) (at,av,d) initial actual
Proof
  simp[abi_encoder_shared_endpoint_def]
QED
