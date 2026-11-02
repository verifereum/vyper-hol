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

Theorem current_demand_cross_block:
  wf_function fn /\
  MEM p (cfg_analyze fn).cfg_dfs_pre /\
  MEM q (cfg_analyze fn).cfg_dfs_pre /\
  MEM q (cfg_succs_of (cfg_analyze fn) p) /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  ~current_phi_operand fn v /\
  MEM v (live_vars_at (liveness_recompute fn) q 0) ==>
  MEM v (live_vars_at (liveness_recompute fn) p (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `MEM qb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `!inst. MEM inst (collect_phis qb.bb_instructions) ==>
     ~MEM v (MAP SND (phi_pairs inst.inst_operands))` by
    metis_tac[current_non_phi_operand] >>
  drule liveness_recompute_cross_block >> simp[] >> metis_tac[]
QED

Theorem current_demand_at_phi_cut:
  wf_function fn /\
  MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  current_phi_cut bb <= j /\ j <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_recompute fn) bb.bb_label j) /\
  (!k. current_phi_cut bb <= k /\ k < j ==>
    ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_recompute fn) bb.bb_label (current_phi_cut bb))
Proof
  strip_tac >> drule liveness_recompute_propagate_range >>
  simp[] >> metis_tac[]
QED

Theorem current_demand_path:
  wf_function fn /\ path <> [] /\
  EVERY (\l. MEM l (cfg_analyze fn).cfg_dfs_pre /\
    ?bb. lookup_block l fn.fn_blocks = SOME bb) path /\
  (!k. SUC k < LENGTH path ==>
    MEM (EL (SUC k) path) (cfg_succs_of (cfg_analyze fn) (EL k path))) /\
  (!k bb inst. SUC k < LENGTH path /\
    lookup_block (EL k path) fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions ==> ~MEM v (inst_defs inst)) /\
  ~current_phi_operand fn v /\
  MEM v (live_vars_at (liveness_recompute fn) (LAST path) 0) ==>
  MEM v (live_vars_at (liveness_recompute fn) (HD path) 0)
Proof
  Induct_on `path` >- simp[] >>
  qx_gen_tac `h` >> namedCases_on `path` ["", "q rest"] >- simp[] >>
  simp[] >> strip_tac >>
  `MEM v (live_vars_at (liveness_recompute fn) q 0)` by
    (qpat_x_assum `_ ==> MEM _ _` mp_tac >>
     (impl_tac >-
       (simp[] >> conj_tac
        >- (rpt strip_tac >> qpat_x_assum `!k. _ ==> MEM _ _`
              (qspec_then `SUC k` mp_tac) >> simp[]) >>
        rpt strip_tac >> qpat_x_assum `!k bb inst. _`
          (qspec_then `SUC k` mp_tac) >> simp[] >> metis_tac[])) >>
     simp[]) >>
  `MEM q (cfg_succs_of (cfg_analyze fn) h)` by
    (qpat_x_assum `!k. _ ==> MEM _ _` (qspec_then `0` mp_tac) >> simp[]) >>
  `MEM v (live_vars_at (liveness_recompute fn) h (LENGTH bb.bb_instructions))` by
    (irule current_demand_cross_block >> metis_tac[]) >>
  drule liveness_recompute_propagate_range >> simp[] >>
  disch_then irule >> simp[] >>
  qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!k bb inst. _` (qspecl_then [`0`, `bb`, `EL k bb.bb_instructions`] mp_tac) >>
  simp[EL_MEM]
QED
