(* Immutable observations at the selected external-call success state. *)
Theory bodyExtStatusWriteFrameMods
Ancestors
  bodyFullPostsMods bodyInvSplit exprLoweringProps loweringSlice
  loweringStateRelDefs valueEncodingProps valueEncodingProofs immutableMemoryFrame
  regularCallEmitSim codegenRel venomState

Theorem extcall_status_write_immutable_frame_mods:
  immutable_frame_mods func cenv cx ee s /\
  local_ptrs_reserved cenv sp /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x s) /\
  ea.immutables = ee.immutables /\ ea.scopes = ee.scopes /\
  z.vs_data_section = s.vs_data_section /\ z.vs_allocas = s.vs_allocas /\
  z.vs_alloca_next = s.vs_alloca_next /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) s).vs_memory /\
  (cenv.ce_is_ctor /\ TAKE cap rd <> [] ==>
   !src tops name tv v off.
     ALOOKUP cenv.ce_modules src = SOME tops /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
                | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
     regions_disjoint (w2n ro) (LENGTH (TAKE cap rd)) off (type_memory_size tv)) ==>
  immutable_frame_mods func cenv cx ea z
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def] >> rpt gen_tac >> disch_tac >>
      `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor ee z` suffices_by
        simp[immutables_rel_def] >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >>
      simp[immutable_write_memory_capacity, arithmeticTheory.MAX_DEF] >>
      rpt strip_tac >> Cases_on `TAKE cap rd = []`
      >- (fs[] >> irule listTheory.LIST_EQ >>
          simp[valueEncodingProofsTheory.LENGTH_mem_bytes_at_proof] >>
          rpt strip_tac >>
          simp[valueEncodingProofsTheory.EL_mem_bytes_at, GSYM read_byte_def,
               read_byte_write_memory_with_expansion]) >>
      irule write_memory_mem_bytes_at_disjoint >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
      qpat_x_assum `!src tops name tv v off. _ ==> _` (drule_all_then mp_tac) >>
      simp[DISJ_COMM]) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `ee`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  `local_region (cenv with ce_module := src) ee.scopes z id b sz <=>
   local_region (cenv with ce_module := src) ee.scopes s id b sz` by
    (irule local_region_lookup_cong >> simp[] >>
     metis_tac[local_ptrs_reserved_def]) >>
  gs[]
QED
