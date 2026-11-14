(* The runner records selected copies as it crosses their source positions. *)
Theory readonlyInvokeCopyFwdExecutionCoverage
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdPlan rangeAnalysisProofs contextCodegenRel
  venomWf venomExecProofs venomExecSemantics venomInst venomState list arithmetic

Definition ricf_copy_coverage_def:
  ricf_copy_coverage ctx0 fn log a ledger s <=>
    !round b es prefix e current dst sv z.
      ricf_located_event ctx0 fn log round b es prefix e current /\
      b < LENGTH fn.fn_blocks /\
      (EL b fn.fn_blocks).bb_label = s.vs_current_bb /\
      (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY /\
      (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands =
        [Var dst; Var sv; Lit z] /\
      0 < w2n z /\ e.rfe_index < s.vs_inst_idx ==>
      ?p. MEM (p,[]) ledger /\ p.rpe_event = e /\ p.rpe_fn = fn /\
        p.rpe_block = EL b fn.fn_blocks /\ p.rpe_owner = a
End

Theorem ricf_copy_coverage_entry:
  wf_function fn /\ enters_block fn s s1 ==>
  ricf_copy_coverage ctx0 fn log a ledger s1
Proof
  strip_tac >> qpat_x_assum `enters_block fn s s1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  qpat_assum `eval_phis s _ = OK _`
    (mp_tac o MATCH_MP eval_phis_only_updates_vs_vars) >>
  disch_then SUBST_ALL_TAC >> rw[ricf_copy_coverage_def] >>
  `lookup_block (EL b fn.fn_blocks).bb_label fn.fn_blocks =
    SOME (EL b fn.fn_blocks)` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def] >>
     simp[EL_MEM]) >>
  `EL b fn.fn_blocks = bb` by metis_tac[optionTheory.SOME_11] >>
  gvs[ricf_event_copy_def] >>
  drule venomExecProofsTheory.phi_prefix_length_el_phi >> simp[]
QED

Theorem ricf_copy_coverage_before:
  ricf_copy_coverage ctx0 fn log a ledger s /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx <= s.vs_inst_idx ==>
  ricf_copy_coverage ctx0 fn log a ledger u
Proof
  rw[ricf_copy_coverage_def] >> first_x_assum irule >>
  simp[] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem ricf_copy_coverage_next:
  ricf_copy_coverage ctx0 fn log a ledger s /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
  (!round b es prefix e current dst sv z.
    ricf_located_event ctx0 fn log round b es prefix e current /\
    b < LENGTH fn.fn_blocks /\
    (EL b fn.fn_blocks).bb_label = s.vs_current_bb /\
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY /\
    (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands =
      [Var dst; Var sv; Lit z] /\ 0 < w2n z ==>
    e.rfe_index <> s.vs_inst_idx) ==>
  ricf_copy_coverage ctx0 fn log a ledger u
Proof
  rw[ricf_copy_coverage_def] >>
  `e.rfe_index < s.vs_inst_idx` by metis_tac[prim_recTheory.LESS_THM] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem ricf_copy_coverage_activate:
  ricf_copy_coverage ctx0 fn log a ledger s /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx /\
  p.rpe_event = e /\ p.rpe_fn = fn /\ p.rpe_block = bb /\ p.rpe_owner = a /\
  (!round b es prefix other current.
    ricf_located_event ctx0 fn log round b es prefix other current /\
    b < LENGTH fn.fn_blocks /\
    (EL b fn.fn_blocks).bb_label = s.vs_current_bb /\
    other.rfe_index = s.vs_inst_idx ==>
    other = e /\ EL b fn.fn_blocks = bb) ==>
  ricf_copy_coverage ctx0 fn log a ((p,[])::ledger) u
Proof
  strip_tac >> rewrite_tac[ricf_copy_coverage_def] >>
  qx_genl_tac [`round`,`b`,`es`,`prefix`,`other`,`current`,`dst`,`sv`,`z`] >>
  strip_tac >>
  `other.rfe_index < SUC s.vs_inst_idx /\
   (EL b fn.fn_blocks).bb_label = s.vs_current_bb` by fs[] >>
  Cases_on `other.rfe_index = s.vs_inst_idx`
  >- (qpat_x_assum `!round b es prefix other current. _`
        (qspecl_then [`round`,`b`,`es`,`prefix`,`other`,`current`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `p` >> simp[]) >>
  `other.rfe_index < s.vs_inst_idx` by decide_tac >>
  `?q. MEM (q,[]) ledger /\ q.rpe_event = other /\ q.rpe_fn = fn /\
    q.rpe_block = EL b fn.fn_blocks /\ q.rpe_owner = a` by
    (qpat_x_assum `ricf_copy_coverage _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ricf_copy_coverage_def]) >>
     disch_then (qspecl_then
       [`round`,`b`,`es`,`prefix`,`other`,`current`,`dst`,`sv`,`z`] mp_tac) >>
     simp[]) >>
  qexists_tac `q` >> simp[]
QED

Theorem ricf_copy_coverage_ordinary:
  ricf_copy_coverage ctx0 fn log a ledger s /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode <> MCOPY /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx ==>
  ricf_copy_coverage ctx0 fn log a ledger u
Proof
  strip_tac >> irule ricf_copy_coverage_next >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst` by
    (fs[active_inst_def] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks)` by
    (conj_tac >> irule MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def] >> simp[EL_MEM]) >>
  `bb = EL b fn.fn_blocks` by metis_tac[optionTheory.SOME_11] >>
  gvs[ricf_event_copy_def]
QED
