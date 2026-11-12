Theory lowerDloadNormalEntry
Ancestors
  lowerDloadNonopaqueEntry lowerDloadNormalTransport lowerDloadMaskBounds
  lowerDloadNormalData lowerDloadCoverageInvariant lowerDloadPairedBoundary
  lowerDloadOwnership ptrDiscipline venomState lowerDloadSharedState
  lowerDloadFrameCertificate lowerDloadAllocation venomExecSemantics

Theorem ld_normal_data_entry_backward:
  lower_dload_function_supply a fn = (gn,b) /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  (!bb i v. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
    MEM (Var v) i.inst_operands ==> v IN V) /\
  enters_block gn t t1 ==>
  ?s1. enters_block fn s s1 /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_entry_prov fn s AG) (ld_entry_prov gn t BH)
      (entry_taint_vars fn s tn) (entry_taint_vars gn t un) s1 t1
      astk live keys d A suspended gstk f /\
    s1.vs_inst_idx = t1.vs_inst_idx /\
    s1.vs_current_bb = t1.vs_current_bb /\ s1.vs_prev_bb = t1.vs_prev_bb /\
    s1 = s with <|vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx|> /\
    t1 = t with <|vs_vars := t1.vs_vars; vs_inst_idx := t1.vs_inst_idx|>
Proof
  strip_tac >> gvs[] >>
  `ld_frame_data V {v | v IN V /\ ~retpc_var fn v} E L H AP BP AG BH tn un s t` by
    metis_tac[ld_normal_data_frame] >>
  `ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
   (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE))` by
    fs[ld_frame_data_def] >>
  drule_all ld_nonopaque_block_entry_backward >> strip_tac >>
  qexists_tac `s1` >> simp[] >>
  `ld_entry_prov gn t BH = ld_entry_prov fn t BH` by
    metis_tac[ld_lowered_entry_prov] >>
  `entry_taint_vars gn t un = entry_taint_vars fn t un` by
    metis_tac[ld_lowered_entry_taint] >>
  simp[] >>
  `!v. ld_owned_selection E (FLOOKUP (ld_entry_prov fn s AG) v)
      (FLOOKUP (ld_entry_prov fn t BH) v)` by
    (drule ld_frame_data_provenance >> strip_tac >>
     simp[ld_entry_prov_def] >>
     Cases_on `lookup_block t.vs_current_bb fn.fn_blocks` >> simp[] >>
     metis_tac[ld_owned_phis_selection]) >>
  `!v owner bs sz. FLOOKUP (ld_entry_prov fn s AG) v = SOME(owner,(bs,sz)) ==>
      owner IN live` by
    (drule ld_normal_data_geometry >> strip_tac >>
     metis_tac[ld_entry_prov_selected]) >>
  `!owner bs sz. ld_live astk L AP (ld_entry_prov fn s AG) (owner,(bs,sz)) ==>
      owner IN live /\ lo <= bs` by
    (drule ld_normal_data_geometry >> strip_tac >>
     simp[ld_live_def] >> rpt strip_tac >>
     metis_tac[ld_entry_selected, ld_live_def]) >>
  `ld_frame_bound t.vs_alloca_next H BP (ld_entry_prov fn t BH)` by
    (drule ld_normal_data_geometry >> strip_tac >>
     metis_tac[ld_frame_bound_entry]) >>
  `(!v. op_taint (entry_taint_vars fn s tn) (Var v) SUBSET count 32) /\
   (!v. op_taint (entry_taint_vars fn t un) (Var v) SUBSET count 32)` by
    (drule ld_normal_data_masks >> strip_tac >>
     metis_tac[ld_entry_taint_vars_bound]) >>
  `!AG BH tn un sx tx n m.
    ld_normal_data CS fn V {v | v IN V /\ ~retpc_var fn v} lo E L H AP BP AG BH tn un
      (sx with vs_inst_idx := n) (tx with vs_inst_idx := m)
      astk live keys d A suspended gstk f =
    ld_normal_data CS fn V {v | v IN V /\ ~retpc_var fn v} lo E L H AP BP AG BH tn un
      sx tx astk live keys d A suspended gstk f` by
    simp[NoAsms, ld_normal_data_def, ld_frame_data_def,
      ld_frame_embedding_def, ld_shared_state_def, ld_owned_vars_def,
      lookup_var_def, ld_alloc_account_def, allocas_from_def, read_memory_def] >>
  qsuff_tac `ld_normal_data CS fn V {v | v IN V /\ ~retpc_var fn v} lo E L H AP BP
    (ld_entry_prov fn s AG) (ld_entry_prov fn t BH)
    (entry_taint_vars fn s tn) (entry_taint_vars fn t un)
    (s1 with vs_inst_idx := s.vs_inst_idx) (t1 with vs_inst_idx := t.vs_inst_idx)
    astk live keys d A suspended gstk f`
  >- simp[] >>
  irule ld_normal_data_vars_complete >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- fs[lookup_var_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `t1 = t with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- gvs[ld_owned_vars_def, lookup_var_def] >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `s1 = s with <|vs_vars := _; vs_inst_idx := _|>`
    (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `t1 = t with <|vs_vars := _; vs_inst_idx := _|>`
    (fn th => once_rewrite_tac[th]) >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  Cases_on `lookup_block t.vs_current_bb fn.fn_blocks` >>
  simp[entry_taint_vars_def]
QED
