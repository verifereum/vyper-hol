Theory makeSsaCurrentSourceEntryRuntime
Ancestors
  makeSsaCurrentPhiBatchRuntime makeSsaCurrentPrefixRuntime
  makeSsaCurrentWfSsa makeSsaCurrentDemand makeSsaHelper
  venomExecSemantics venomExecProps venomState venomWf venomInst
  list alist finite_map

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
    (irule current_prefix_resolve_phi_selected >> simp[]) >>
  `?k. k < LENGTH old.bb_instructions /\ inst = EL k old.bb_instructions` by
    metis_tac[MEM_EL] >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    (irule current_wf_original_phi_demand >> metis_tac[]) >>
  `IS_SOME (lookup_var v t)` by metis_tac[] >>
  simp[eval_one_phi_def, eval_operand_def] >>
  Cases_on `lookup_var v t` >> gvs[eval_operand_def, lookup_var_def]
QED
