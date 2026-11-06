Theory makeSsaCurrentCarrierExternal
Ancestors
  makeSsaCurrentEntryProvenance makeSsaCurrentExternalExclusion
  makeSsaCurrentDominanceBridge makeSsaCurrentAnalysis makeSsaCurrentWfSsa
  dominatorAnalysisProps venomExecProps cfgWf

Theorem current_wf_ancestor_output_external:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ lookup_block h renamed = SOME new /\
  MEM d (fn_labels fn) /\ MEM h (fn_labels fn) /\
  d <> h /\ fn_dominates fn d h /\
  MEM db renamed /\ MEM di db.bb_instructions /\ MEM src di.inst_outputs /\
  (db.bb_label = d \/ fn_dominates fn db.bb_label d) ==>
  db.bb_label <> h /\
  !ni. MEM ni new.bb_instructions ==> ~MEM src ni.inst_outputs
Proof
  strip_tac >>
  `wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  `db.bb_label <> h` by
    (strip_tac >> gvs[] >>
     `dominates (dom_analyze (cfg_analyze fn) fn) d db.bb_label /\
      dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label d` by
       metis_tac[current_semantic_dominates] >>
     `cfg_reachable_of (cfg_analyze fn) d /\
      cfg_reachable_of (cfg_analyze fn) db.bb_label` by
       metis_tac[current_cfg_reachable, venomWfTheory.fn_dominates_def] >>
     metis_tac[dominates_antisym]) >>
  simp[] >>
  `new.bb_label = h` by metis_tac[lookup_block_label] >>
  metis_tac[current_wf_external_output_disjoint]
QED

Theorem current_wf_inherited_collapsed_source_external:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME oldh /\
  lookup_block d fn.fn_blocks = SOME oldd /\
  lookup_block h renamed = SOME newh /\ lookup_block d renamed = SOME newd /\
  d <> h /\ fn_dominates fn d h /\
  q < LENGTH newd.bb_instructions /\
  (EL q newd.bb_instructions).inst_opcode = PHI /\
  simplify_current_phi (EL q newd.bb_instructions) =
    (EL q newd.bb_instructions) with
      <|inst_opcode := ASSIGN; inst_operands := [Var src]|> ==>
  !ni. MEM ni newh.bb_instructions ==> ~MEM src ni.inst_outputs
Proof
  strip_tac >>
  `MEM d (fn_labels fn) /\ MEM h (fn_labels fn)` by
    (simp[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
     metis_tac[lookup_block_MEM, lookup_block_label]) >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn` by fs[current_wf_phi_context_def] >>
  drule_all current_wf_phi_occurrence_cleanup_cases >> strip_tac
  >- fs[venomInstTheory.instruction_component_equality]
  >- (`src' = src` by fs[venomInstTheory.instruction_component_equality] >>
      `newd.bb_label = d` by metis_tac[lookup_block_label] >>
      `fn_dominates fn db.bb_label d` by
        metis_tac[current_wf_precleanup_dominance] >>
      metis_tac[current_wf_ancestor_output_external]) >>
  `n = src` by fs[venomInstTheory.instruction_component_equality] >>
  `r < LENGTH newd.bb_instructions` by
    (fs[current_wf_original_phi_at_def] >> gvs[]) >>
  `MEM newd renamed /\ newd.bb_label = d /\
   MEM (EL r newd.bb_instructions) newd.bb_instructions` by
    metis_tac[lookup_block_MEM, lookup_block_label, listTheory.EL_MEM] >>
  metis_tac[current_wf_ancestor_output_external]
QED
