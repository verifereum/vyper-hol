(* Recursive encoder interface with physical scratch ownership.
   TOP-LEVEL: abi_scratch_input describes complete source data and actual
   disjoint regions; abi_scratch_effect records the owned writes and allocation
   evolution; abi_scratch_encoder requires execution of the actual compiler.
   Constructor proofs are separate: defining this interface proves no encoder. *)
Theory abiScratchEncoderContract
Ancestors
  abiScratchFootprint abiDecoderFootprint abiDecoderAllocation abiDecoderFrame
  abiDecoderReentry abiDecoderLoop abiDecoderContract abiEncoderInput abiEncoder
  compileEnv valueEncoding contractABI instIdxIndep venomState finite_map words list arithmetic

Definition abi_scratch_input_def:
  abi_scratch_input ei at av st src dst sb source_cap d output_size first last b cap s <=>
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    LENGTH (enc at av) <= output_size /\
    sb+source_cap < dimword (:256) /\ d+output_size < dimword (:256) /\
    (sb+source_cap <= d \/ d+output_size <= sb) /\
    abi_footprint_disjoint sb source_cap
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) /\
    abi_footprint_disjoint d output_size
      (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)
End

Definition abi_scratch_effect_def:
  abi_scratch_effect first last lo hi next limit_st d sz b cap s t <=>
    fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    abi_scratch_evolution (abi_decoder_ids first last) b cap s t /\
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_footprint_frame
      ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s) s t /\
    (!id. id < lo \/ hi <= id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted
End

Definition abi_scratch_encoder_def:
  abi_scratch_encoder ei <=>
    !dst src start end_st out func ctx first last b cap limit_st initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei start = (out,end_st) /\ fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_input ei at av start src dst sb source_cap d (LENGTH (enc at av))
      first last b cap initial /\
    abi_decoder_budget first last b cap initial /\
    first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?actual. mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (LENGTH (enc at av)) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
      ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
End

Theorem abi_scratch_effect_inst_idx[simp]:
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial
    (actual with vs_inst_idx := ix) <=>
  abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual
Proof
  simp[abi_scratch_effect_def, abi_scratch_evolution_def, fresh_vars_wrt_def,
    eval_op_inst_idx, abi_decode_footprint_frame_def, abi_decoder_budget_def,
    abi_decoder_missing_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ENCODER_CONTRACT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch encoder contract not kernel closed: " ^ n)
  end) (DB.thms "abiScratchEncoderContract");
