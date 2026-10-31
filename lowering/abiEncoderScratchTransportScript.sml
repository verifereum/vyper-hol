(* Allocation-observation transport, independent of source and execution. *)
Theory abiEncoderScratchTransport
Ancestors
  abiDecoderFootprint abiDecoderDynamicLoopSetup abiScratchFootprint venomState

Theorem abi_encoder_child_scratch_allocations:
  s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next ==>
  abi_decoder_child_scratch ids b cap s = abi_decoder_child_scratch ids b cap t
Proof
  simp[abi_decoder_child_scratch_def]
QED

Theorem abi_encoder_address_scratch_disjoint:
  abi_decoder_address_frame next s t /\
  abi_footprint_disjoint d sz (abi_decoder_child_scratch ids b cap s) ==>
  abi_footprint_disjoint d sz (abi_decoder_child_scratch ids b cap t)
Proof
  strip_tac >>
  `abi_decoder_child_scratch ids b cap s = abi_decoder_child_scratch ids b cap t` by
    (irule abi_encoder_child_scratch_allocations >> fs[abi_decoder_address_frame_def]) >>
  metis_tac[]
QED
