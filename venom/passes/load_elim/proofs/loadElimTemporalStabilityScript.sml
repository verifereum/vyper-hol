Theory loadElimTemporalStability
Ancestors
  loadElimOccurrence loadElimOccurrenceIntervals loadElimTemporalDominance loadElimLastWriter
  loadElimNormalizeAvailability simplifyCfgPhiRepair simplifyCfgStruct
  simplifyCfgWfssa venomExecProofs venomWf venomInst list rich_list
  loadElimActionPlacement loadElimOccurrenceCoverage mem2varBlockSimHelpers

Theorem le_occ_assign_crossing:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME cb /\
  def_available_at fn cb (SOME i) v /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
  di.inst_opcode = ASSIGN /\ di.inst_operands = [Var w] /\
  di.inst_outputs = [v] /\ w IN le_occ_writes e ==>
  le_occ_wrote suffix v
Proof
  rpt strip_tac >>
  `def_available_at fn db (SOME di) w` by
    (gvs[wf_ssa_def, def_dominates_uses_def] >>
     first_x_assum (qspecl_then [`db`, `di`] mp_tac) >> simp[]) >>
  qpat_x_assum `def_available_at fn cb (SOME i) v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  `MEM v di.inst_outputs` by simp[] >>
  `def_inst = di` by
    (fs[wf_ssa_def] >> metis_tac[ssa_form_output_unique, MEM]) >>
  `def_bb = db` by metis_tac[wf_function_instruction_block] >> gvs[] >>
  `le_occ_valid C fn e` by
    (drule le_occ_prefix_valid >> simp[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `def_available_at fn db (SOME def_inst) w` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  rename1 `MEM src sb.bb_instructions` >>
  `lookup_block (le_occ_pre e).vs_current_bb fn.fn_blocks = SOME sb` by
    (drule_all le_occ_writer_instruction >>
     Cases_on `e` >> simp[le_occ_pre_def] >> strip_tac
     >- (`src = EL n b.bb_instructions` by
           (fs[wf_ssa_def] >> metis_tac[ssa_form_output_unique]) >>
         `sb = b` by metis_tac[wf_function_instruction_block] >>
         gvs[le_occ_valid_def]) >>
     `MEM inst b.bb_instructions` by metis_tac[MEM_TAKE] >>
     `src = inst` by (fs[wf_ssa_def] >> metis_tac[ssa_form_output_unique]) >>
     `sb = b` by metis_tac[wf_function_instruction_block] >>
     gvs[le_occ_valid_def]) >>
  `active_inst fn i s` by metis_tac[le_occ_prefix_active] >>
  `s.vs_inst_idx < LENGTH cb.bb_instructions /\
   EL s.vs_inst_idx cb.bb_instructions = i` by
    (drule_all le_active_inst_lookup >> strip_tac >> gvs[]) >>
  `!j. j < LENGTH db.bb_instructions /\ EL j db.bb_instructions = def_inst /\
       db = cb ==> j < s.vs_inst_idx` by
    (rpt strip_tac >> gvs[] >>
     `j' = s.vs_inst_idx` by metis_tac[wf_bb_EL_inj, lookup_block_MEM] >>
     `i' = j` by metis_tac[wf_bb_EL_inj, lookup_block_MEM, arithmeticTheory.LESS_TRANS] >>
     gvs[]) >>
  drule le_occ_interval_route >> simp[] >>
  disch_then (qspecl_then [`pre`, `e`, `suffix`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `sb = db`
  >- (gvs[] >>
      `phi_prefix_length db.bb_instructions <= j` by
        (spose_not_then assume_tac >>
         `j < phi_prefix_length db.bb_instructions` by decide_tac >>
         mp_tac (Q.SPEC `db.bb_instructions` analysisSimProofsBaseTheory.phi_prefix_all_phi) >>
         pure_rewrite_tac[EVERY_EL] >>
         disch_then (qspec_then `j` mp_tac) >> simp[LENGTH_TAKE, EL_TAKE, phi_prefix_length_le]) >>
      `case e of StepOcc eb n k u t => n < j
               | PhiOcc eb u t => phi_prefix_length db.bb_instructions <= j` by
        (Cases_on `e` >> simp[] >>
         gvs[le_occ_valid_def, le_occ_pre_def, le_occ_writes_def] >>
         rename1 `step_inst fuel C (EL u.vs_inst_idx b.bb_instructions) u = OK t` >>
         `EL i' b.bb_instructions = EL u.vs_inst_idx b.bb_instructions` by
           (fs[wf_ssa_def] >> metis_tac[ssa_form_output_unique, EL_MEM]) >>
         `i' = u.vs_inst_idx` by
           metis_tac[wf_bb_EL_inj, arithmeticTheory.LESS_TRANS] >> simp[]) >>
      drule le_occ_interval_initial_coverage >> simp[] >> disch_then irule >>
      qexistsl_tac [`db`, `e`, `j`, `pre`] >> simp[] >>
      strip_tac >> gvs[] >>
      `db = cb` by metis_tac[] >> metis_tac[]) >>
  `sb.bb_label <> db.bb_label` by metis_tac[codegenReadyComputeTheory.wf_function_blocks_same_label] >>
  `(le_occ_pre e).vs_current_bb = sb.bb_label /\
   s.vs_current_bb = cb.bb_label` by metis_tac[lookup_block_label] >>
  `MEM db.bb_label (le_occ_route suffix)` by
    (fs[] >> drule_all le_dominating_separator >> simp[]) >>
  drule le_route_phi_split >> strip_tac >> gvs[] >>
  rename1 `le_occ_prefix C fn s0 (pre ++ e::(before ++ [PhiOcc bb u p] ++ after)) i s` >>
  `le_occ_valid C fn (PhiOcc bb u p)` by
    (drule le_occ_prefix_valid >> simp[EVERY_MEM] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks` by (fs[le_occ_valid_def] >> metis_tac[lookup_block_MEM]) >>
  `bb = db` by metis_tac[codegenReadyComputeTheory.wf_function_blocks_same_label] >>
  gvs[] >> rename1 `MEM def_inst db.bb_instructions` >>
  `?j. j < LENGTH db.bb_instructions /\ EL j db.bb_instructions = def_inst` by
    metis_tac[MEM_EL] >>
  `le_occ_wrote (before ++ PhiOcc db u p::after) v` suffices_by (simp[le_occ_wrote_def] >> metis_tac[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `le_occ_route after = [] ==> j < s.vs_inst_idx` by
   (strip_tac >>
  `le_occ_prefix C fn s0 ((pre ++ e::before) ++ PhiOcc db u p::after) i s` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  drule le_occ_interval_route >> simp[] >>
  disch_then (qspecl_then [`pre ++ e::before`, `PhiOcc db u p`, `after`] mp_tac) >>
  simp[le_occ_pre_def] >> strip_tac >>
  `db = cb` by (gvs[le_occ_valid_def] >> metis_tac[]) >> metis_tac[]) >>
  `MEM v (EL j db.bb_instructions).inst_outputs` by simp[] >>
  drule_all le_occ_interval_later_phi_coverage >> simp[]
QED

Theorem le_occ_assign_source_no_write:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 (pre ++ StepOcc db n k u t::suffix) i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  def_available_at fn bb (SOME i) v /\ i.inst_opcode <> PHI /\
  (EL n db.bb_instructions).inst_opcode = ASSIGN /\
  (EL n db.bb_instructions).inst_operands = [Var w] /\
  (EL n db.bb_instructions).inst_outputs = [v] /\
  EVERY (\q. v NOTIN le_occ_writes q) suffix ==>
  EVERY (\q. w NOTIN le_occ_writes q) suffix
Proof
  rpt strip_tac >>
  `le_occ_valid C fn (StepOcc db n k u t)` by
    (drule le_occ_prefix_valid >> simp[EVERY_MEM] >> metis_tac[]) >>
  `MEM db fn.fn_blocks /\ MEM (EL n db.bb_instructions) db.bb_instructions` by
    (fs[le_occ_valid_def] >> metis_tac[lookup_block_MEM, EL_MEM]) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM q suffix` >>
  drule (iffLR MEM_SPLIT) >> strip_tac >> gvs[] >>
  `le_occ_prefix C fn s0 ((pre ++ StepOcc db n k u t::l1) ++ q::l2) i s` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  drule_all le_occ_assign_crossing >>
  fs[le_occ_wrote_def, EVERY_MEM] >> metis_tac[]
QED

Theorem le_occ_assign_source_lookup:
  wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 (pre ++ StepOcc db n k u t::suffix) i s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  def_available_at fn bb (SOME i) v /\ i.inst_opcode <> PHI /\
  (EL n db.bb_instructions).inst_opcode = ASSIGN /\
  (EL n db.bb_instructions).inst_operands = [Var w] /\
  (EL n db.bb_instructions).inst_outputs = [v] /\
  EVERY (\q. v NOTIN le_occ_writes q) suffix ==>
  lookup_var w s = lookup_var w t
Proof
  rpt strip_tac >>
  `EVERY (\q. w NOTIN le_occ_writes q) suffix` by
    (drule_all le_occ_assign_source_no_write >> simp[]) >>
  drule_all le_occ_prefix_suffix_lookup >> simp[le_occ_post_def]
QED
