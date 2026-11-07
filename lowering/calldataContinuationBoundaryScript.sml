(* Continuation boundary for the iterative (not bulk) array compiler branch.
   Complex member propagation is already exported by abiDecoderMemberCons:
   abi_decoder_members_child_phi and abi_decoder_members_tail_phi.
   Loop body/backedge propagation is already abi_decoder_loop_phase_cfg.
   These are reused, not restated. *)
Theory calldataContinuationBoundary
Ancestors
  abiDecoderRecursiveArray abiDecoderMemberCons abiDecoderRecursiveLoopLayout
  calldataRecursiveProducers

(* The same-blocks alternative is impossible in the iterative branch.  Thus
   the proposed public boundary supplies the exit hypothesis of the existing
   loop layout theorem without strengthening the recursive contract. *)
Theorem calldata_iterative_array_exit_boundary:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei asz msz dyn maxn)
    st = ((),final) /\
  (dyn \/ dec_info_needs_clamp ei) /\ abi_decode_source_opcode opc /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  metis_tac[abi_decoder_recursive_array_adds_blocks]
QED
