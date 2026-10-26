(* Compose precise scratch frames while the allocator frontier advances.
   TOP-LEVEL: abi_scratch_frame_trans preserves the original footprint across
   sequential execution without allowing writes to unrelated live allocations. *)
Theory abiScratchCompose
Ancestors
  abiScratchFootprint abiDecoderFootprint abiDecoderFrame venomState pred_set list arithmetic

Theorem abi_scratch_frame_advance_plain:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap t) t u ==>
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) t u
Proof
  strip_tac >> qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p n. _` irule >>
  drule_all abi_scratch_disjoint_advance >> simp[]
QED

Theorem abi_scratch_frame_trans:
  abi_scratch_evolution ids b cap s t /\ FINITE ids /\
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s t /\
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap t) t u ==>
  abi_decode_footprint_frame (abi_decoder_child_scratch ids b cap s) s u
Proof
  strip_tac >> drule_all abi_scratch_frame_advance_plain >> disch_then assume_tac >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `t` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_COMPOSE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch composition not kernel closed: " ^ n)
  end) (DB.thms "abiScratchCompose");
