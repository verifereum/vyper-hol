Theory makeSsaCurrentSourceEntryRuntime
Ancestors
  makeSsaCurrentPhiBatchRuntime makeSsaCurrentPrefixRuntime
  makeSsaCurrentWfSsa makeSsaCurrentDemand
  makeSsaCurrentEdgeTransport makeSsaCurrentPrefixEffect
  makeSsaCurrentPrefixSuffixOwner
  venomExecSemantics venomExecProps venomExecProofs venomState venomWf venomInst
  list alist finite_map simplifyCfgRetpc
Theorem current_source_phi_entry_success:
  current_wf_phi_context s fn renamed s' A H events /\
  fn_cfg_edge fn p h /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block p fn.fn_blocks = SOME pred /\ t.vs_prev_bb = SOME p /\
  (!v. current_demand fn v p (LENGTH pred.bb_instructions) ==>
    IS_SOME (lookup_var v t)) ==>
  ?post. eval_phis t old.bb_instructions = OK post
Proof
  strip_tac >> irule current_phi_batch_success_all >> rpt strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ fn_phis_cover_preds fn` by
    fs[current_wf_phi_context_def] >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed inst.inst_operands /\ ?out. inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `?v. MEM (p,v) (phi_pairs inst.inst_operands)` by
    metis_tac[fn_phis_cover_preds_def] >>
  `ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))` by
    (fs[current_wf_phi_context_def] >> metis_tac[]) >>
  `resolve_phi p inst.inst_operands = SOME (Var v)` by
    (irule retpc_phi_pair_selected >> simp[]) >>
  `?k. k < LENGTH old.bb_instructions /\ inst = EL k old.bb_instructions` by
    metis_tac[MEM_EL] >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_original_phi_demand >> metis_tac[]) >>
  `IS_SOME (lookup_var v t)` by metis_tac[] >>
  simp[eval_one_phi_def, eval_operand_def] >>
  Cases_on `lookup_var v t` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem current_source_phi_post_defined:
  wf_function fn /\
  fn_cfg_edge fn p h /\ lookup_block h fn.fn_blocks = SOME old /\
  lookup_block p fn.fn_blocks = SOME pred /\
  (!v. current_demand fn v p (LENGTH pred.bb_instructions) ==>
    IS_SOME (lookup_var v t)) /\
  eval_phis t old.bb_instructions = OK post /\
  current_demand fn v h (LENGTH (collect_phis old.bb_instructions)) ==>
  IS_SOME (lookup_var v post)
Proof
  strip_tac >>
  `!xs. collect_phis xs = TAKE (phi_prefix_length xs) xs` by
    (Induct >> simp[livenessDefsTheory.collect_phis_def, phi_prefix_length_def] >>
     qx_gen_tac `inst` >> Cases_on `inst.inst_opcode = PHI` >> simp[]) >>
  Cases_on `?inst. MEM inst (collect_phis old.bb_instructions) /\
    MEM v inst.inst_outputs`
  >- (gvs[] >>
      `v IN FDOM post.vs_vars` by metis_tac[eval_phis_outputs_in_fdom_mem] >>
      fs[lookup_var_def, FLOOKUP_DEF]) >>
  `EVERY (\j. ~MEM v j.inst_outputs) (collect_phis old.bb_instructions)` by
    (rewrite_tac[EVERY_MEM] >> metis_tac[]) >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_demand_edge_no_phi_defs >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`old`, `h`] >>
     reverse conj_tac >- metis_tac[] >> rpt strip_tac >>
     `j < phi_prefix_length old.bb_instructions` by
       metis_tac[current_prefix_collect_length] >>
     `MEM (EL j old.bb_instructions) (collect_phis old.bb_instructions)` by
       (simp[] >> irule (iffRL MEM_EL) >> qexists_tac `j` >>
        conj_tac >- metis_tac[] >> simp[EL_TAKE]) >>
     fs[EVERY_MEM, inst_defs_def] >> metis_tac[]) >>
  `phi_eff t.vs_prev_bb v old.bb_instructions = SOME (Var v)` by
    metis_tac[current_prefix_phi_eff_absent] >>
  drule current_phi_batch_lookup >> simp[eval_operand_def, lookup_var_def] >>
  metis_tac[lookup_var_def]
QED
