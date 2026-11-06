Theory lowerDloadNonopaqueEntry
Ancestors
  lowerDloadOpaqueExecution lowerDloadControlPosition lowerDloadOwnership
  contextCodegenRel ptrDiscipline venomExecProofs venomInst
  unitShapeDefs lowerDloadPairedBoundary venomState list pred_set

Theorem ld_nonopaque_block_entry_backward:
  lower_dload_function_supply a fn = (gn,b) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  (!bb i v. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
     MEM (Var v) i.inst_operands ==> v IN V) /\
  enters_block gn t t1 ==>
  ?s1. enters_block fn s s1 /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_entry_prov fn s AG) (ld_entry_prov fn t BH)
      (entry_taint_vars fn s tn) (entry_taint_vars fn t un) s1 t1 /\
    (!v. v IN V ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_inst_idx = t1.vs_inst_idx /\
    s1.vs_current_bb = t1.vs_current_bb /\ s1.vs_prev_bb = t1.vs_prev_bb /\
    s1 = s with <|vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx|> /\
    t1 = t with <|vs_vars := t1.vs_vars; vs_inst_idx := t1.vs_inst_idx|>
Proof
  strip_tac >>
  `enters_block fn t t1` by metis_tac[lower_dload_function_supply_enters_block] >>
  qpat_x_assum `enters_block fn t t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  `!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V` by
    metis_tac[] >>
  drule_all ld_nonopaque_phis_backward >> strip_tac >>
  `s' = s with vs_vars := s'.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  `s_phi = t with vs_vars := s_phi.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  qexists_tac `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  conj_tac >- (qexistsl_tac [`bb`, `s'`] >> simp[]) >>
  simp[ld_entry_prov_def, entry_taint_vars_def] >>
  conj_tac >- gvs[ld_owned_vars_def, lookup_var_def] >>
  simp[lookup_var_def] >>
  qpat_x_assum `s' = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `s_phi = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
  fs[lookup_var_def]
QED
