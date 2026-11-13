Theory makeSsaCurrentSelectedLive
Ancestors
  makeSsaCurrentDemandDominance makeSsaDefs livenessDefs
  venomInst venomWf list alist

Theorem current_live_in_after_phis_member:
  !bbs l bb vs v live.
    lookup_block l bbs = SOME bb /\
    ALOOKUP (current_live_in_after_phis live bbs) l = SOME vs /\ MEM v vs ==>
    MEM v (live_vars_at live l (LENGTH (collect_phis bb.bb_instructions)))
Proof
  Induct >> simp[lookup_block_def, current_live_in_after_phis_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = l` >> simp[]
  >- (strip_tac >> gvs[] >> Cases_on `bb.bb_instructions` >>
      gvs[collect_phis_def] >>
      rename1 `inst::rest` >>
      Cases_on `inst.inst_opcode = PHI` >> gvs[collect_phis_def]) >>
  strip_tac >> first_x_assum irule >>
  simp[lookup_block_def] >> goal_assum (drule_at Any)
QED

Theorem current_selected_live_phi_cut:
  lookup_block l fn.fn_blocks = SOME bb /\
  ALOOKUP (select_current_live_in T live fn) l = SOME vs /\ MEM v vs ==>
  MEM v (live_vars_at live l (LENGTH (collect_phis bb.bb_instructions)))
Proof
  simp[select_current_live_in_def] >>
  metis_tac[current_live_in_after_phis_member]
QED

Theorem current_selected_live_single_definition:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  ALOOKUP (select_current_live_in T (liveness_analyze fn) fn) l = SOME vs /\
  MEM v vs /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\ fn_dominates fn db.bb_label l /\
    (db = bb ==> ?j. j < LENGTH (collect_phis bb.bb_instructions) /\
      MEM v (EL j bb.bb_instructions).inst_outputs)
Proof
  strip_tac >> irule current_live_phi_cut_single_definition >> simp[] >>
  irule current_selected_live_phi_cut >> goal_assum (drule_at Any) >>
  qexists_tac `fn` >> simp[]
QED
