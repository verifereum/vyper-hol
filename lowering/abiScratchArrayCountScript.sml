(* Actual array count copying preserves the complete source outside its output.
   TOP-LEVEL: abi_scratch_array_count_caller derives this separation from
   distinct live allocations; no separation from a scratch arena is required. *)
Theory abiScratchArrayCount
Ancestors
  abiCallerAllocation abiEncoderArrayCountReach abiEncoderArrayPrefix
  abiEncoderInputFrame abiEncoderInputLayout abiEncoderInput
  abiDecoderArrayHeader abiDecoderFrameCompose abiDecoderFrame abiDecoderContract
  abiDecoderReentry compileEnv valueEncoding valueEncodingProps
  contractABI venomState finite_map words list arithmetic

Theorem abi_scratch_array_count_separate:
  alloca_inv s /\ FLOOKUP s.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,output_size) /\
  source_id <> output_id /\ 32 <= output_size ==>
  abi_footprint_disjoint sb source_cap [(d,32)]
Proof
  strip_tac >> drule_all abi_caller_allocation_separate >>
  simp[abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_scratch_array_count_reach:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_footprint_disjoint sb source_cap [(d,32)] /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  `mload sb initial = n2w (LENGTH avs)` by
    fs[abi_encoder_array_input_iff, mem_word_at_eq_mload] >>
  drule_all abi_encoder_array_count_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decode_footprint_frame [(d,32)] initial actual` by
    fs[abi_decode_frame_footprint] >>
  drule_all abi_encoder_input_frame >> disch_then assume_tac >>
  `abi_encoder_array_prefix ty avs 0 d actual.vs_memory` by
    (irule abi_encoder_array_prefix_empty >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_array_count_caller:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_inv initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_id <> output_id /\ 32 <= output_size /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_count_separate >> disch_then assume_tac >>
  drule_all abi_scratch_array_count_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >> qexists_tac `actual` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_COUNT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch array count not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayCount");
