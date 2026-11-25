(* A typed store into a registered allocation preserves every owner's immutables. *)
Theory bodyIfExpTypedImmFrameMods
Ancestors
  bodyFullPostsMods bodyInvSplit exprLoweringProps loweringSlice typedMemoryCopy
  loweringStateRelDefs venomState compileEnv

Theorem ifexp_typed_immutable_frame_mods:
  immutable_frame_mods func ce cx ee q /\ local_ptrs_reserved ce k /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP q.vs_allocas inst.inst_id = SOME (dst,n) /\
  typed_copy_state_frame k dst n q f ==>
  immutable_frame_mods func ce cx ee f
Proof
  strip_tac >>
  `f.vs_data_section = q.vs_data_section /\ f.vs_allocas = q.vs_allocas /\
   f.vs_alloca_next = q.vs_alloca_next` by
    fs[typed_copy_state_frame_def, venom_state_component_equality] >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >> conj_tac
  >- (qx_genl_tac [`src`,`tops`] >> disch_tac >>
      irule immutables_rel_mem_agree >> qexists_tac `q` >> simp[] >>
      conj_tac >- fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      rpt strip_tac >>
      `immutable_alloca_sep func (ce with ce_module := src) cx ee q` by
        (first_x_assum irule >> qexists_tac `tops` >> simp[]) >>
      `regions_disjoint off (type_memory_size tv) dst n` by
        (pop_assum (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
         simp[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
         simp[] >> strip_tac >>
         qpat_assum `!i b sz. MEM i _ /\ _ ==> regions_disjoint _ _ b sz`
           (qspecl_then [`inst`,`dst`,`n`] mp_tac) >> simp[]) >>
      fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      first_x_assum irule >> fs[regions_disjoint_def]) >>
  qx_genl_tac [`src`,`tops`] >> disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`q`,`ee`] >> simp[] >>
  qx_genl_tac [`name`,`b`,`sz`] >> disch_tac >> qexists_tac `name` >>
  qpat_x_assum `local_region _ _ f _ _ _` mp_tac >>
  simp[local_region_def] >> rpt strip_tac >>
  `not_fresh_at k p` by metis_tac[local_ptrs_reserved_def] >>
  fs[typed_copy_state_frame_def] >>
  qpat_assum `!x. not_fresh_at k x ==> _` (qspec_then `p` mp_tac) >> simp[]
QED
