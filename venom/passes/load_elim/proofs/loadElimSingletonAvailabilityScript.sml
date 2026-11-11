Theory loadElimSingletonAvailability
Ancestors
  loadElimActualGeneration loadElimLastWriter loadElimOccurrence
  loadElimTransferProvenance loadElimKeyShapeInvariant
  loadElimDefs venomInst venomWf venomState dfAnalyzeDefs cfgDefs finite_map list

(* Recover a genuine earlier active prefix, not a solver witness. *)
Theorem le_occ_prefix_step_before:
  !C fn s0 es i s. le_occ_prefix C fn s0 es i s ==>
  !bb n fuel pre post. MEM (StepOcc bb n fuel pre post) es ==>
  ?before. le_occ_prefix C fn s0 before (EL n bb.bb_instructions) pre /\
    (!e. MEM e before ==> MEM e es)
Proof
  ho_match_mp_tac le_occ_prefix_strongind >> rpt conj_tac
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[] >> strip_tac
      >- (first_x_assum drule >> strip_tac >>
          qexists `before` >> simp[] >> metis_tac[]) >>
      gvs[] >> qexists `es` >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[] >> strip_tac
  >- (first_x_assum drule >> strip_tac >>
      qexists `before` >> simp[] >> metis_tac[]) >>
  gvs[] >> qexists `es` >> simp[]
QED

Theorem le_occ_generated_variable_writer:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\
  MEM (StepOcc bb n fuel pre post) es /\
  le_transfer_generates ctx (EL n bb.bb_instructions) key (Var v) ==>
  ?e. MEM e es /\ v IN le_occ_writes e
Proof
  strip_tac >>
  qpat_x_assum `le_transfer_generates _ _ _ _` mp_tac >>
  simp[le_transfer_generates_def] >> strip_tac
  >- (qexists `StepOcc bb n fuel pre post` >>
      simp[le_occ_writes_def]) >>
  `?before. le_occ_prefix C fn s0 before (EL n bb.bb_instructions) pre /\
     (!e. MEM e before ==> MEM e es)` by
    metis_tac[le_occ_prefix_step_before] >>
  `(EL n bb.bb_instructions).inst_opcode <> PHI` by
    (gvs[le_configured_context_def, memory_config_def, storage_config_def,
       transient_config_def, dload_config_def, calldataload_config_def]) >>
  `MEM (Var v) (EL n bb.bb_instructions).inst_operands` by simp[] >>
  drule_all le_occ_ssa_use_writer >> metis_tac[]
QED

Theorem le_occ_singleton_variable_writer:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [Var v] ==>
  ?e. MEM e es /\ v IN le_occ_writes e
Proof
  strip_tac >>
  drule_all le_occ_prefix_singleton_generation >> strip_tac >>
  irule le_occ_generated_variable_writer >> metis_tac[]
QED

Theorem le_occ_singleton_variable_last_writer:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  le_occ_prefix C fn s0 es i s /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME [Var v] ==>
  ?before e suffix.
    es = before ++ e::suffix /\ v IN le_occ_writes e /\
    EVERY (\q. v NOTIN le_occ_writes q) suffix /\
    le_occ_valid C fn e /\ IS_SOME (lookup_var v (le_occ_post e)) /\
    lookup_var v s = lookup_var v (le_occ_post e)
Proof
  strip_tac >> drule_all le_occ_singleton_variable_writer >> strip_tac >>
  drule le_occ_prefix_last_writer >>
  disch_then (qspec_then `v` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  rename1 `es = before ++ last::suffix` >>
  qexistsl [`before`, `last`, `suffix`] >> simp[] >>
  metis_tac[le_occ_valid_writer_defined]
QED
