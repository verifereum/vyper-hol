(* Account for a newly allocated or reused index inside the original physical footprint. *)
Theory abiScratchDecoderInitEffect
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract abiScratchFootprint abiScratchSequence
  abiDecoderArrayInitReach abiDecoderAllocation abiDecoderFootprint abiDecoderFrame
  abiDecoderContract abiDecoderReentry compileEnv venomState words list arithmetic pred_set

Theorem abi_scratch_frame_origin:
  abi_scratch_evolution ids b cap entry prepared /\ FINITE ids /\
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap prepared) before after ==>
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap entry) before after
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
  asm_simp_tac (srw_ss()) [] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!p n. _` irule >>
  qpat_x_assum `abi_footprint_disjoint _ _ (_::_)`
    (strip_assume_tac o REWRITE_RULE [abi_scratch_disjoint_cons]) >>
  simp_tac bool_ss [abi_scratch_disjoint_cons] >> asm_rewrite_tac[] >>
  drule_all abi_scratch_disjoint_advance >> simp[]
QED

Theorem abi_scratch_output_final_slot_frame:
  abi_scratch_evolution ids b cap initial actual /\ FINITE ids /\ site IN ids /\
  FLOOKUP actual.vs_allocas site = SOME (slot,n) /\
  abi_decode_footprint_frame [(d,sz);(slot,n)] initial actual ==>
  abi_decode_footprint_frame ((d,sz)::abi_decoder_child_scratch ids b cap initial) initial actual
Proof
  strip_tac >>
  `MEM (slot,n) (abi_decoder_child_scratch ids b cap actual)` by
    (irule abi_scratch_registered_member >> asm_simp_tac bool_ss [] >>
     qexists_tac `site` >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch ids b cap actual) initial actual` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(d,sz);(slot,n)]` >>
     asm_simp_tac bool_ss [] >> simp[] >> qx_genl_tac [`p`, `k`] >> strip_tac >|
     [qexistsl_tac [`d`, `sz`] >> simp[], qexistsl_tac [`slot`, `n`] >> simp[]]) >>
  mp_tac (Q.INST [`entry` |-> `initial:venom_state`, `prepared` |-> `actual:venom_state`,
    `before` |-> `initial:venom_state`, `after` |-> `actual:venom_state`] abi_scratch_frame_origin) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_init_effect:
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial actual /\
  run_inst_seq insts initial = OK actual /\ lo <= site /\ site < hi ==>
  abi_scratch_effect first last lo hi next limit_st d 32 b cap initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  disch_then (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule abi_decoder_budget_frontier >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    (mp_tac (Q.SPECL [`insts`, `initial`, `actual`, `abi_decoder_ids first last`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> asm_simp_tac bool_ss []) >>
  `abi_scratch_evolution (abi_decoder_ids lo hi) b cap initial actual` by
    (mp_tac (Q.SPECL [`insts`, `initial`, `actual`, `abi_decoder_ids lo hi`, `b`, `cap`]
      abi_scratch_sequence_evolution) >> asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame
    ((d,32)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap initial) initial actual` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids lo hi`, `sz` |-> `32:num`, `n` |-> `32:num`]
      abi_scratch_output_final_slot_frame) >>
     impl_tac >- asm_simp_tac (srw_ss()) [abi_decoder_ids_def] >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_effect_def] >>
  rpt gen_tac >> strip_tac >> `id <> site` by decide_tac >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_INIT_EFFECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical decoder initializer effect not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderInitEffect");
