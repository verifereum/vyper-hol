Theory makeSsaCurrentDominanceAvailability
Ancestors
  venomWfProps cfgNormSupplySim makeSsaCurrentOutputSurvival
  makeSsaCurrentWfSsa makeSsaCurrentDefs venomState finite_map

Theorem current_strict_dom_producer_lookup:
  strict_dom_vars_defined f st /\ MEM b f.fn_blocks /\
  MEM i b.bb_instructions /\ MEM x i.inst_outputs /\
  fn_dominates f b.bb_label st.vs_current_bb /\
  b.bb_label <> st.vs_current_bb ==>
  ?v. lookup_var x st = SOME v
Proof
  rw[strict_dom_vars_defined_def, lookup_var_def] >>
  metis_tac[FLOOKUP_DEF, optionTheory.option_nchotomy]
QED

Theorem current_final_producer_lookup_probe[local]:
  strict_dom_vars_defined final st /\ st.vs_current_bb = h /\
  (?b i. MEM b final.fn_blocks /\ MEM i b.bb_instructions /\
    MEM x i.inst_outputs /\ fn_dominates final b.bb_label h /\
    b.bb_label <> h) ==>
  ?v. lookup_var x st = SOME v
Proof
  metis_tac[current_strict_dom_producer_lookup]
QED

Theorem current_conditional_cleanup_dominance:
  g = f with fn_blocks := simplify_current_phis_if enabled f.fn_blocks ==>
  (fn_reachable g l <=> fn_reachable f l) /\
  (fn_dominates g d n <=> fn_dominates f d n)
Proof
  strip_tac >> irule current_wf_cfg_dominance >>
  Cases_on `enabled` >>
  simp[simplify_current_phis_if_def, simplify_current_phis_def] >>
  Cases_on `blocks_have_leading_phi f.fn_blocks` >> simp[] >>
  `fn_entry_label (f with fn_blocks := MAP simplify_current_phi_block f.fn_blocks) =
     fn_entry_label f /\
   (!a b. fn_cfg_edge (f with fn_blocks := MAP simplify_current_phi_block f.fn_blocks) a b <=>
          fn_cfg_edge f a b)` by
    (irule current_wf_cleanup_cfg >> simp[]) >>
  simp[]
QED

Theorem current_context_external_producer_lookup:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  final = fn with fn_blocks := simplify_current_phis_if enabled renamed /\
  strict_dom_vars_defined final st /\
  MEM db renamed /\ MEM di db.bb_instructions /\ MEM src di.inst_outputs /\
  db.bb_label <> st.vs_current_bb /\
  fn_dominates (fn with fn_blocks := renamed) db.bb_label st.vs_current_bb ==>
  ?v. lookup_var src st = SOME v
Proof
  strip_tac >>
  drule_all current_wf_phi_context_lookup >> strip_tac >>
  drule_all current_context_conditional_producer >>
  disch_then (qspec_then `enabled` strip_assume_tac) >>
  `fn_dominates final db.bb_label st.vs_current_bb` by
    (mp_tac (Q.INST [`f` |-> `fn with fn_blocks := renamed`, `g` |-> `final`,
       `d` |-> `db.bb_label`, `n` |-> `st.vs_current_bb`]
      current_conditional_cleanup_dominance) >> gvs[]) >>
  irule current_strict_dom_producer_lookup >>
  qexistsl [`b`, `final`, `j`] >> gvs[]
QED
