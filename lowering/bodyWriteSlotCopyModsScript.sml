(* Endpoint facts for an aggregate write at a selected slot. *)
Theory bodyWriteSlotCopyMods
Ancestors
  bodyFullPostsMods exprLoweringProps loweringSlice placeStoreStorage
  bodyFullStoreSlotsPath bodyFullStoreSlotsFrame placeStoreSlots bodyPtrDefs
  stateRelProj bodyFullShadowBodyInv vyperStorageBackend finite_map list
  loweringStateRelDefs bodySimFull bodyMemoryDefs bodyInvSplit

Theorem slot_copy_linked_immutable_preserved[local]:
  immutable_frame_mods func cenv cx ee s /\
  ef.immutables = ee.immutables /\ ef.scopes = ee.scopes /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  immutable_frame_mods func cenv cx ef t
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _` (drule_then mp_tac) >>
      pure_asm_rewrite_tac[immutables_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`, `ee`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]
QED
