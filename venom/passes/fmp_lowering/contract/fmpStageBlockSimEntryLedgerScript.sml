Theory fmpStageBlockSimEntryLedger
Ancestors
  fmpStageRel fmpStageReclaimFresh fmpStepAnalysis fmpStepStack
  fmpLedgerProps fmpLowerReclaimPlan fmpReclaimDefs dfAnalyzeDefs
  venomState venomInst venomWf venomWfProps fmpAnalysisDefs
  rich_list list arithmetic finite_map

Theorem fmp_ledger_prefix:
  !ps ks top. fmp_ledger_ok insts env s top (ps ++ ks) ==>
    fmp_ledger_ok insts env s top ps
Proof
  Induct >> simp[fmp_ledger_ok_def] >> metis_tac[]
QED

Theorem fmp_ledger_prefix_frame:
  fmp_ledger_ok insts env s top regions /\
  (!r. MEM r (TAKE n regions) ==>
    lookup_var r.fr_mark t = lookup_var r.fr_mark s) ==>
  fmp_ledger_ok insts env t top (TAKE n regions)
Proof
  strip_tac >> irule fmp_ledger_frame >> qexists `s` >> simp[] >>
  irule fmp_ledger_prefix >> qexists `DROP n regions` >> simp[]
QED

Theorem fmp_ledger_link_prefix:
  fmp_ledger_ok insts env s lo (ps ++ ks) /\
  fmp_ledger_link sm eb lo (ps ++ ks) /\
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp ==>
  fmp_ledger_link sm eb lo ps
Proof
  strip_tac >> Cases_on `ps = []`
  >- (gvs[fmp_ledger_link_def, fmp_sites_ok_def] >> metis_tac[]) >>
  drule_all fmp_ledger_split >> strip_tac >>
  drule fmp_ledger_bounds >> strip_tac >>
  `EVERY (\r. (LAST ps).fr_lo <= r.fr_lo) ps` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\r. r.fr_hi <= (LAST ps).fr_lo) ks` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `((if ps ++ ks = [] then lo else (LAST (ps ++ ks)).fr_lo)
       <= (LAST ps).fr_lo)` by
    (Cases_on `ks = []` >- gvs[] >>
     simp[LAST_APPEND_NOT_NIL] >>
     `MEM (LAST ks) ks` by simp[MEM_LAST_NOT_NIL] >>
     qpat_x_assum `EVERY (\r. r.fr_hi <= _) ks` kall_tac >>
     fs[EVERY_MEM] >>
     first_x_assum drule >> strip_tac >> decide_tac) >>
  `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==> 0 < z` by
    metis_tac[fmp_sites_ok_def] >>
  qpat_x_assum `fmp_sites_ok _ _ _ _ _` kall_tac >>
  fs[fmp_ledger_link_def, EVERY_MEM] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b z c id. _ /\ _ /\ _ ==> _`
    (qspecl_then [`b`,`z`,`c`,`id`] mp_tac) >> simp[] >>
  strip_tac >> conj_tac
  >- (strip_tac >>
      `?r. (MEM r ps \/ MEM r ks) /\ r.fr_lo = c /\
         r.fr_hi = c + z /\ r.fr_site = id` by
        (first_x_assum irule >> gvs[] >> decide_tac) >>
      `0 < z` by metis_tac[] >>
      `~MEM r ks` by (strip_tac >> res_tac >> decide_tac) >>
      qexists `r` >> gvs[]) >>
  strip_tac >> Cases_on `c < (LAST (ps ++ ks)).fr_lo`
  >- (gvs[] >> decide_tac) >>
  `?r. (MEM r ps \/ MEM r ks) /\ r.fr_lo = c /\
     r.fr_hi = c + z /\ r.fr_site = id` by
    (first_x_assum irule >> decide_tac) >>
  gvs[] >> res_tac >> decide_tac
QED

Theorem fmp_ledger_link_take:
  fmp_ledger_ok insts env s lo regions /\
  fmp_ledger_link sm eb lo regions /\
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp ==>
  fmp_ledger_link sm eb lo (TAKE n regions)
Proof
  strip_tac >> irule fmp_ledger_link_prefix >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl [`env`,`insts`,`DROP n regions`,`s`] >> simp[]
QED

Theorem fmp_transfer_phi_stack:
  inst.inst_opcode = PHI ==>
  ?st'. fmp_transfer infos fn live env p inst (SOME st) = SOME st' /\
        st'.frs_stack = st.frs_stack
Proof
  simp[fmp_transfer_def, fmp_reclaim_step_def, fmp_pop_at_def,
       fmp_is_reclaim_point_def, fmp_clears_marks_def,
       fmp_callee_info_def, fmp_invoke_target_def, fmp_apply_effect_def]
QED

Theorem fmp_analysis_phi_stack:
  !k st. fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\ wf_function fn /\
  MEM bb fn.fn_blocks /\ k <= LENGTH bb.bb_instructions /\
  (!j. j < k ==> (EL j bb.bb_instructions).inst_opcode = PHI) /\
  df_at NONE states bb.bb_label 0 = SOME st ==>
  ?st'. df_at NONE states bb.bb_label k = SOME st' /\
        st'.frs_stack = st.frs_stack
Proof
  Induct >- (rpt strip_tac >> qexists `st` >> simp[]) >>
  rpt strip_tac >>
  `k <= LENGTH bb.bb_instructions /\ k < LENGTH bb.bb_instructions` by simp[] >>
  `?sk. df_at NONE states bb.bb_label k = SOME sk /\
        sk.frs_stack = st.frs_stack` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  drule_all fmp_reclaim_states_df_at_suc >> simp[] >>
  disch_then SUBST1_TAC >>
  qpat_x_assum `sk.frs_stack = _` (SUBST1_TAC o SYM) >>
  irule fmp_transfer_phi_stack >> simp[]
QED

Theorem fmp_transfer_jump_stack:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] ==>
  ?st'. fmp_transfer infos fn live env p inst (SOME st) = SOME st' /\
    st'.frs_stack = SND (fmp_pop_at infos fn live env p inst st)
Proof
  simp[fmp_transfer_def, fmp_reclaim_step_def] >> strip_tac >>
  pairarg_tac >> gvs[] >>
  simp[fmp_apply_effect_def, fmp_clears_marks_def,
       fmp_callee_info_def, fmp_invoke_target_def] >>
  gvs[]
QED

Theorem fmp_analysis_jump_phi_prefix:
  wf_function fn /\ fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  MEM pb fn.fn_blocks /\ MEM bb fn.fn_blocks /\
  MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
  LENGTH pb.bb_instructions = SUC idx /\
  MEM (EL idx pb.bb_instructions).inst_opcode [JMP; JNZ; DJMP] /\
  df_at NONE states pb.bb_label idx = SOME st /\
  k <= LENGTH bb.bb_instructions /\
  (!j. j < k ==> (EL j bb.bb_instructions).inst_opcode = PHI) ==>
  ?st' ks. df_at NONE states bb.bb_label k = SOME st' /\
    SND (fmp_pop_at infos fn (liveness_analyze fn) env (pb.bb_label,idx)
      (EL idx pb.bb_instructions) st) = st'.frs_stack ++ ks
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `idx < LENGTH pb.bb_instructions` by simp[] >>
  drule_all fmp_reclaim_states_df_at_suc >> simp[] >>
  strip_tac >>
  `?se. fmp_transfer infos fn (liveness_analyze fn) env (pb.bb_label,idx)
      (EL idx pb.bb_instructions) (SOME st) = SOME se /\
    se.frs_stack = SND (fmp_pop_at infos fn (liveness_analyze fn) env
      (pb.bb_label,idx) (EL idx pb.bb_instructions) st)` by
    (irule fmp_transfer_jump_stack >> simp[]) >>
  `df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME se` by
    metis_tac[] >>
  drule_all reclaim_fresh_edge >> strip_tac >>
  drule_all fmp_analysis_phi_stack >> strip_tac >>
  metis_tac[]
QED

Theorem fmp_dalloca_not_phi_output:
  ssa_form fn /\ fmp_dalloca_output fn v /\
  MEM phi (fn_insts fn) /\ phi.inst_opcode = PHI ==>
  ~MEM v phi.inst_outputs
Proof
  simp[fmp_dalloca_output_def] >> rpt strip_tac >>
  `inst = phi` by
    (irule ssa_outputs_same_inst >>
     gvs[fn_insts_def] >> metis_tac[]) >> gvs[]
QED

Theorem fmp_analysis_stack_not_phi_output:
  ssa_form fn /\ fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states lbl idx = SOME st /\ MEM v st.frs_stack /\
  MEM phi (fn_insts fn) /\ phi.inst_opcode = PHI ==>
  ~MEM v phi.inst_outputs
Proof
  strip_tac >> drule_all fmp_reclaim_states_stack >>
  simp[EVERY_MEM] >> strip_tac >>
  irule fmp_dalloca_not_phi_output >> metis_tac[]
QED

Theorem fmp_ledger_restrict_stack:
  fmp_ledger_ok insts env s lo regions /\
  MAP (\r. r.fr_mark) regions = stack ++ ks /\
  EVERY (\r. elo <= r.fr_lo) regions /\
  fmp_ledger_link sm eb lo regions /\
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp /\
  (!r. MEM r (TAKE (LENGTH stack) regions) ==>
    lookup_var r.fr_mark t = lookup_var r.fr_mark s) ==>
  fmp_ledger_ok insts env t lo (TAKE (LENGTH stack) regions) /\
  MAP (\r. r.fr_mark) (TAKE (LENGTH stack) regions) = stack /\
  EVERY (\r. elo <= r.fr_lo) (TAKE (LENGTH stack) regions) /\
  fmp_ledger_link sm eb lo (TAKE (LENGTH stack) regions)
Proof
  strip_tac >> conj_tac
  >- (irule fmp_ledger_prefix_frame >> metis_tac[]) >>
  conj_tac >- simp[MAP_TAKE, TAKE_LENGTH_APPEND] >>
  conj_tac >- metis_tac[EVERY_TAKE] >>
  irule fmp_ledger_link_take >> metis_tac[]
QED
