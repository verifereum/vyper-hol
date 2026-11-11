(* Entry-to-function assembly of the concrete block simulation. *)
Theory acFunctionSimulationProofs
Ancestors
  acBlockSimulationProofs acBlockTransformProofs invariantBlockSimulationProps
  acRuntimeInvariantDefs acMergeRuntimeDefs acAbortRelProofs
  assertCombinerDefs venomWf venomExecProps venomExecProofs
  stateEquiv stateEquivProps passSimulationDefs venomInst list pred_set

Theorem ac_run_blocks_simulation:
  !fuel ctx fn su s.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    ir_supply_covers_fn su fn /\
    (!inst l. MEM inst (fn_insts fn) /\ ac_is_safe_between inst /\
              MEM (Label l) inst.inst_operands ==> l IN FDOM s.vs_labels) /\
    s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV)
      ac_abort_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (FST (ac_transform_function su fn)) s)
Proof
  rpt gen_tac >> strip_tac >>
  `ac_merge_safe_labels fn s` by
    (rewrite_tac[ac_merge_safe_labels_def] >> rpt strip_tac >> metis_tac[]) >>
  `!bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
        ac_cursor_inv fn bb 0 s` by
    (rpt strip_tac >> irule ac_cursor_inv_entry >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  irule run_blocks_lookup_invariant_simulation >>
  reverse conj_tac
  >- (simp[state_equiv_refl] >> rpt strip_tac >>
      gvs[state_equiv_def, execution_equiv_def]) >>
  qexistsl [`\bb. THE (lookup_block bb.bb_label
      (FST (ac_transform_function su fn)).fn_blocks)`,
    `\u. ac_merge_safe_labels fn u /\
      !bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb ==>
           ac_cursor_inv fn bb 0 u`] >>
  BETA_TAC >> simp[] >>
  conj_tac >- metis_tac[ac_transform_function_lookup_map] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `ac_cursor_inv fn bb 0 u` by metis_tac[] >>
      drule_all ac_transform_function_run_block >>
      disch_then (qspecl_then [`k`, `ctx`] strip_assume_tac) >>
      `bb.bb_label = u.vs_current_bb` by metis_tac[lookup_block_label] >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `ac_cursor_inv fn bb 0 u` by metis_tac[] >>
  conj_tac
  >- (drule run_block_preserves_labels >>
      metis_tac[ac_merge_safe_labels_frame]) >>
  rpt strip_tac >> irule (cj 1 ac_run_block_successor) >>
  `bb'.bb_label = u'.vs_current_bb /\ MEM bb' fn.fn_blocks` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  simp[] >> qexistsl [`bb`, `ctx`, `k`, `u`] >> simp[]
QED
