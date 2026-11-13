Theory lowerDloadPairedEntry
Ancestors
  lowerDloadOpaqueExecution lowerDloadControlPosition lowerDloadPairedBoundary
  lowerDloadCoverageInvariant lowerDloadFrameCertificate lowerDloadSharedState
  o1PassContract venomInst venomExecProps venomExecProofs venomState contextCodegenRel list pred_set

Theorem lower_dload_paired_enters_block:
  lower_dload_function_supply a fn = (gn,b) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG AH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!i v. MEM i (fn_insts fn) /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  enters_block gn t t1 ==>
  ?bb s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    enters_block fn s s1 /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_phis_prov s.vs_prev_bb AG bb.bb_instructions)
      (ld_phis_prov t.vs_prev_bb AH bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb.bb_instructions) s1 t1 /\
    (!v. v IN V ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    t1.vs_inst_idx = phi_prefix_length bb.bb_instructions
Proof
  strip_tac >>
  `enters_block fn t t1` by
    metis_tac[lower_dload_function_supply_enters_block] >>
  qpat_x_assum `enters_block fn t t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by
    (rpt strip_tac >> simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists_tac `bb` >> simp[] >> metis_tac[lookup_block_MEM]) >>
  `!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V` by
    metis_tac[] >>
  drule_all ld_nonopaque_phis_backward >> strip_tac >>
  qexistsl_tac [`bb`, `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  qpat_x_assum `enters_block gn t t1` kall_tac >>
  gvs[ld_owned_vars_def, lookup_var_def, enters_block_def] >> metis_tac[]
QED

Theorem ld_enters_block_restore[local]:
  enters_block fn s s1 ==>
  (s1 with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem lower_dload_paired_entry_data:
  lower_dload_function_supply a fn = (gn,b) /\
  ld_frame_data V {v | v IN V /\ ~retpc_var fn v}
    E L H AP BP AG BH tn un s t /\
  (!i v. MEM i (fn_insts fn) /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  enters_block gn t t1 ==>
  ?bb s1. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    enters_block fn s s1 /\
    ld_frame_data V {v | v IN V /\ ~retpc_var fn v} E L H AP BP
      (ld_phis_prov s.vs_prev_bb AG bb.bb_instructions)
      (ld_phis_prov t.vs_prev_bb BH bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb.bb_instructions) s1 t1 /\
    s1.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    t1.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    (s1 with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (t1 with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) = t
Proof
  strip_tac >>
  qpat_x_assum `ld_frame_data _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ld_frame_data_def] >> strip_tac >>
  drule_all lower_dload_paired_enters_block >> strip_tac >>
  qexistsl_tac [`bb`, `s1`] >> simp[] >>
  `s1 with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` by
    metis_tac[ld_enters_block_restore] >>
  `t1 with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> = t` by
    metis_tac[ld_enters_block_restore] >>
  `!v. ld_owned_selection E
      (FLOOKUP (ld_phis_prov s.vs_prev_bb AG bb.bb_instructions) v)
      (FLOOKUP (ld_phis_prov t.vs_prev_bb BH bb.bb_instructions) v)` by
    (simp[] >> irule ld_owned_phis_selection >> simp[]) >>
  simp[ld_frame_data_def] >>
  qpat_x_assum `s1 with <|vs_vars := _; vs_inst_idx := _|> = s` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `t1 with <|vs_vars := _; vs_inst_idx := _|> = t` (SUBST_ALL_TAC o SYM) >>
  gvs[ld_frame_embedding_def, ld_shared_state_def]
QED
