(* Register-only execution preserves precise scratch ownership and its budget.
   TOP-LEVEL: abi_scratch_address connects the existing address-frame interface
   to scratch evolution and arbitrary observational memory frames. *)
Theory abiScratchAddress
Ancestors
  abiScratchFootprint abiDecoderDynamicLoopSetup abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame venomState pred_set arithmetic

Theorem abi_scratch_address:
  abi_decoder_address_frame next s t /\ abi_decoder_budget first last b cap s ==>
  abi_scratch_evolution ids b cap s t /\ abi_decode_footprint_frame fp s t /\
  abi_decoder_budget first last b cap t /\
  abi_decoder_child_scratch ids b cap t = abi_decoder_child_scratch ids b cap s
Proof
  strip_tac >>
  qpat_x_assum `abi_decoder_address_frame _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `s.vs_alloca_next <= b+cap` by
    (drule abi_decoder_budget_frontier >> simp[]) >>
  `abi_scratch_evolution ids b cap s t` by
    (rw[abi_scratch_evolution_def] >> gvs[]) >>
  `(abi_decoder_budget first last b cap t <=> abi_decoder_budget first last b cap s)` by
    (irule abi_decoder_budget_transport >> simp[]) >>
  simp[abi_decode_footprint_frame_def, abi_decoder_child_scratch_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_ADDRESS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch address not kernel closed: " ^ n)
  end) (DB.thms "abiScratchAddress");
