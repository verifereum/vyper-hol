(* A child's private allocation site cannot overwrite another loop's scratch slot. *)
Theory abiDecoderProtectedScratch
Ancestors
  abiDecoderAllocation abiDecoderTypedContract abiDecoderArrayInitExec
  abiDecoderFrame abiDecoderFrameCompose compileEnv venomState finite_map words arithmetic pred_set

Theorem abi_decoder_budget_site_bounds:
  abi_decoder_budget first last b cap s /\ site IN abi_decoder_ids first last /\
  FLOOKUP s.vs_allocas site = SOME (p,32) ==>
  b <= p /\ p + 32 <= b + cap
Proof
  strip_tac >> drule abi_decoder_budget_reservation >>
  simp_tac bool_ss [abi_decoder_reservation_def] >> strip_tac >>
  qpat_x_assum `!id off sz. _` (qspecl_then [`site`, `p`, `32`] mp_tac) >>
  impl_tac >- gvs[abi_decoder_ids_def] >> simp[]
QED

Theorem abi_decoder_budget_sites_disjoint:
  abi_decoder_budget first last b cap s /\
  i IN abi_decoder_ids first last /\ j IN abi_decoder_ids first last /\ i <> j /\
  FLOOKUP s.vs_allocas i = SOME (p,32) /\ FLOOKUP s.vs_allocas j = SOME (q,32) ==>
  p + 32 <= q \/ q + 32 <= p
Proof
  strip_tac >> qpat_x_assum `abi_decoder_budget _ _ _ _ _`
    (qspecl_then [`i`, `j`, `p`, `q`] mp_tac o List.last o CONJUNCTS o
      PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]
QED

Theorem abi_decoder_private_scratch_preserves_slot:
  abi_decoder_budget first last b cap t /\
  site IN abi_decoder_ids first last /\ other IN abi_decoder_ids first last /\ site <> other /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\
  FLOOKUP t.vs_allocas other = SOME (protected,32) /\
  abi_decode_footprint_frame [(d,outsz);(slot,32)] s t /\
  (d + outsz <= b \/ b + cap <= d) ==>
  mload protected t = mload protected s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `b <= protected /\ protected + 32 <= b + cap` by
    (mp_tac (Q.INST [`s` |-> `t:venom_state`, `site` |-> `other:num`,
       `p` |-> `protected:num`] abi_decoder_budget_site_bounds) >> simp[]) >>
  irule abi_decode_footprint_frame_mload >> qexists_tac `[(d,outsz);(slot,32)]` >>
  simp[abi_footprint_disjoint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  mp_tac (Q.INST [`s` |-> `t:venom_state`, `i` |-> `site:num`, `j` |-> `other:num`,
    `p` |-> `slot:num`, `q` |-> `protected:num`] abi_decoder_budget_sites_disjoint) >>
  impl_tac >- simp[] >> metis_tac[]
QED

Theorem abi_decoder_private_scratch_preserves_other_site:
  abi_decoder_budget first last b cap t /\
  site IN abi_decoder_ids first last /\ other IN abi_decoder_ids first last /\ site <> other /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\
  FLOOKUP s.vs_allocas other = SOME (protected,32) /\
  (!id. id <> site ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  abi_decode_footprint_frame [(d,outsz);(slot,32)] s t /\
  (d + outsz <= b \/ b + cap <= d) ==>
  FLOOKUP t.vs_allocas other = SOME (protected,32) /\ mload protected t = mload protected s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `FLOOKUP t.vs_allocas other = SOME (protected,32)` by metis_tac[] >>
  asm_simp_tac bool_ss [] >> drule_all abi_decoder_private_scratch_preserves_slot >> simp[]
QED

Theorem abi_decoder_pre_output_separated:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap s ==>
  d + type_memory_bytes ce ty <= b \/ b + cap <= d
Proof
  simp_tac bool_ss [abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC
QED

Theorem abi_decoder_child_scratch_preservation:
  abi_decoder_budget first last b cap t /\ first <= child_first /\ child_last <= last /\
  child_first <= site /\ site < child_last /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\
  (!id. id <> site ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  abi_decode_footprint_frame [(d,outsz);(slot,32)] s t /\ (d + outsz <= b \/ b + cap <= d) ==>
  !other protected.
    other IN abi_decoder_ids first last /\ (other < child_first \/ child_last <= other) /\
    FLOOKUP s.vs_allocas other = SOME (protected,32) ==>
    FLOOKUP t.vs_allocas other = SOME (protected,32) /\ mload protected t = mload protected s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  `site <> other` by decide_tac >>
  drule_all abi_decoder_private_scratch_preserves_other_site >> simp[]
QED

Theorem abi_decoder_bulk_scratch_preservation:
  abi_decoder_budget first last b cap s /\ t.vs_allocas = s.vs_allocas /\
  abi_decode_frame d outsz s t /\ (d + outsz <= b \/ b + cap <= d) ==>
  !other protected. other IN abi_decoder_ids first last /\
    FLOOKUP s.vs_allocas other = SOME (protected,32) ==>
    FLOOKUP t.vs_allocas other = SOME (protected,32) /\ mload protected t = mload protected s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `b <= protected /\ protected + 32 <= b + cap` by
    (mp_tac (Q.INST [`site` |-> `other:num`, `p` |-> `protected:num`]
       abi_decoder_budget_site_bounds) >> simp[]) >>
  asm_simp_tac bool_ss [] >> irule abi_decode_footprint_frame_mload >>
  qexists_tac `[(d,outsz)]` >>
  simp[GSYM abi_decode_frame_footprint, abi_footprint_disjoint_def] >>
  irule abi_decoder_arena_disjoint >> qexistsl_tac [`b`, `cap`] >> simp[]
QED
