Theory makeSsaCurrentDemand
Ancestors
  makeSsaCurrentDefs venomWf livenessLocalProofs livenessTransferProofs
  livenessDefs cfgDefs venomInst list alist

Definition current_phi_operand_def:
  current_phi_operand fn v <=>
    ?bb inst pred. MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
      MEM (pred,v) (phi_pairs inst.inst_operands)
End

Definition current_phi_cut_def:
  current_phi_cut bb = LENGTH (collect_phis bb.bb_instructions)
End

Theorem current_phi_operand_single_def:
  fn_phi_operands_single_def fn /\ current_phi_operand fn v ==>
  LENGTH (FILTER (\i. MEM v i.inst_outputs) (fn_insts fn)) <= 1
Proof
  simp[fn_phi_operands_single_def_def, current_phi_operand_def] >>
  metis_tac[]
QED

Theorem current_non_phi_operand:
  ~current_phi_operand fn v /\ MEM bb fn.fn_blocks ==>
  !inst. MEM inst (collect_phis bb.bb_instructions) ==>
    ~MEM v (MAP SND (phi_pairs inst.inst_operands))
Proof
  simp[current_phi_operand_def, MEM_MAP] >> rpt strip_tac >>
  drule collect_phis_mem >> strip_tac >>
  PairCases_on `y` >> gvs[] >> metis_tac[]
QED

Theorem current_selected_live_in_false:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  ALOOKUP (select_current_live_in F (liveness_recompute fn) fn) bb.bb_label =
    SOME (live_vars_at (liveness_recompute fn) bb.bb_label 0)
Proof
  strip_tac >> simp[select_current_live_in_def] >>
  `MEM bb.bb_label (fn_labels fn)` by (simp[fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  simp[ALOOKUP_current_query_map, liveness_recompute_boundary_entry]
QED

Theorem current_live_in_after_phis_lookup:
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\ MEM bb bbs ==>
  ALOOKUP (current_live_in_after_phis live bbs) bb.bb_label =
    SOME (if bb.bb_instructions = [] then []
          else live_vars_at live bb.bb_label (current_phi_cut bb))
Proof
  Induct_on `bbs` >> simp[current_live_in_after_phis_def] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `bb.bb_instructions` >>
      simp[current_phi_cut_def, collect_phis_def] >>
      Cases_on `h.inst_opcode = PHI` >> simp[collect_phis_def]) >>
  `bb.bb_label <> h.bb_label` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

Theorem current_selected_live_in_true:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  ALOOKUP (select_current_live_in T (liveness_recompute fn) fn) bb.bb_label =
    SOME (if bb.bb_instructions = [] then [] else
      live_vars_at (liveness_recompute fn) bb.bb_label (current_phi_cut bb))
Proof
  strip_tac >> simp[select_current_live_in_def] >>
  irule current_live_in_after_phis_lookup >> gvs[wf_function_def, fn_labels_def]
QED
