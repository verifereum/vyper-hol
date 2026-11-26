(* The immutable frame of a copy into a selected live local region. *)
Theory bodyLocalCopyWritesMods
Ancestors
  bodyFullPostsMods bodyInvSplit exprLoweringProps loweringSlice typedMemoryCopy
  vyperTypeEnvPreservation loweringStateRelDefs venomState

Theorem local_copy_immutable_frame_mods:
  immutable_frame_mods func cenv cx es s /\
  local_region cenv es.scopes s id b0 cap /\
  b0 <= dest /\ dest + bytes <= b0 + cap /\
  typed_copy_state_frame st dest bytes s t /\
  local_ptrs_reserved cenv st /\
  ee.immutables = es.immutables /\ MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  immutable_frame_mods func cenv cx ee t
Proof
  strip_tac >>
  `t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!name b sz. local_region cenv ee.scopes t name b sz ==>
               local_region cenv es.scopes s name b sz` by
    (rw[local_region_def] >>
     `not_fresh_at st p` by metis_tac[local_ptrs_reserved_def] >>
     fs[typed_copy_state_frame_def] >>
     `IS_SOME (lookup_scopes name es.scopes)` by
       metis_tac[lookup_scopes_same_fdoms_some] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es t` suffices_by
        simp[immutables_rel_def] >>
      irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
      conj_tac >- fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      rpt strip_tac >>
      `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by metis_tac[] >>
      `local_region (cenv with ce_module := src) es.scopes s id b0 cap` by
        fs[local_region_def] >>
      `regions_disjoint off (type_memory_size tv) b0 cap` by
        (qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
           (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
         simp[] >>
         disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
         simp[] >> strip_tac >> first_x_assum drule >> simp[]) >>
      fs[regions_disjoint_def, typed_copy_state_frame_def, typed_copy_frame_def] >>
      first_x_assum irule >> decide_tac) >>
  rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >>
  simp[] >>
  qx_genl_tac [`name`,`b`,`sz`] >> disch_tac >> qexists_tac `name` >>
  first_x_assum (qspecl_then [`name`,`b`,`sz`] mp_tac) >>
  fs[local_region_def]
QED
