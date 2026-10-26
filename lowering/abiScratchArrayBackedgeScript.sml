(* Execute the actual ADD/MSTORE/JMP backedge with physical scratch ownership.
   TOP-LEVEL: abi_scratch_array_backedge reuses concrete CFG execution and
   charges the index update to its registered allocation site. *)
Theory abiScratchArrayBackedge
Ancestors
  abiScratchEncoderContract abiScratchEffectCompose abiEncoderArrayBackedge
  abiDecoderAllocation abiDecoderArrayBackedge abiDecoderFootprint abiDecoderLoop
  abiDecoderReentry compileEnv venomState venomInst words finite_map list arithmetic

Theorem abi_scratch_array_backedge:
  lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  initial.vs_inst_idx = LENGTH prefix /\ ~initial.vs_halted /\
  eval_operand (Var iv) initial = SOME (n2w j) /\ eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
  ?actual. mload slot actual = n2w (SUC j) /\
    actual.vs_current_bb = hdr /\ actual.vs_inst_idx = 0 /\ ~actual.vs_halted /\
    fresh_vars_wrt limit_st actual /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    abi_decode_footprint_frame [(slot,32)] initial actual /\
    abi_scratch_effect first last lo hi next limit_st d sz b cap initial actual /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`] abi_encoder_array_backedge_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac abi_scratch_single_write >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ARRAY_BACKEDGE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch actual array backedge not kernel closed: " ^ n)
  end) (DB.thms "abiScratchArrayBackedge");
