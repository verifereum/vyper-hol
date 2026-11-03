Theory simplifyCfgWfssa
Ancestors
  simplifyCfgPhiRepair simplifyCfgDataflow simplifyCfgStruct
  venomWf venomExecProofs cfgWf list rich_list relation

Theorem is_fn_path_first_arrival:
  !path. path <> [] /\ is_fn_path fn path /\ LAST path = b ==>
  ?pre. is_fn_path fn (pre ++ [b]) /\ HD (pre ++ [b]) = HD path /\
        ~MEM b pre
Proof
  Induct >> simp[] >> qx_gen_tac `a` >> strip_tac >>
  Cases_on `a = b`
  >- (qexists `[]` >> simp[is_fn_path_def]) >>
  Cases_on `path` >- gvs[] >>
  fs[is_fn_path_def] >>
  qexists `a::pre` >> simp[is_fn_path_prepend] >>
  Cases_on `pre` >> gvs[]
QED

Theorem def_on_all_paths_first_witness:
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  def_on_all_paths fn bb use_opt v ==>
  ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
    MEM v di.inst_outputs /\
    (db = bb ==> case use_opt of NONE => T | SOME use =>
      ?i j. i < j /\ j < LENGTH bb.bb_instructions /\
            EL i bb.bb_instructions = di /\ EL j bb.bb_instructions = use)
Proof
  strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `?pre. is_fn_path fn (pre ++ [bb.bb_label]) /\
     HD (pre ++ [bb.bb_label]) = entry /\ ~MEM bb.bb_label pre` by
    metis_tac[is_fn_path_first_arrival] >>
  qpat_x_assum `def_on_all_paths fn bb use_opt v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `pre ++ [bb.bb_label]` mp_tac) >>
  simp[] >> strip_tac
  >- (qexistsl [`def_bb`, `def_inst`] >> simp[] >>
      `MEM def_bb.bb_label pre` by
        (simp[MEM_EL] >> qexists `k` >> fs[EL_APPEND1]) >>
      `def_bb <> bb` by metis_tac[] >> simp[]) >>
  qexistsl [`bb`, `EL i bb.bb_instructions`] >> simp[EL_MEM] >>
  Cases_on `use_opt` >> gvs[] >> metis_tac[]
QED

Theorem def_on_all_paths_dominating_witness:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ def_on_all_paths fn bb use_opt v /\
  MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs ==>
  fn_dominates fn db.bb_label bb.bb_label
Proof
  strip_tac >> simp[fn_dominates_def] >> rpt strip_tac >>
  qpat_x_assum `def_on_all_paths fn bb use_opt v` mp_tac >>
  simp[def_on_all_paths_def] >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> strip_tac
  >- (`def_inst = di` by metis_tac[ssa_form_output_unique] >>
      `def_bb = db` by metis_tac[wf_function_instruction_block] >>
      gvs[] >> simp[MEM_EL] >> qexists `k` >> simp[]) >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions` by simp[EL_MEM] >>
  `EL i bb.bb_instructions = di` by metis_tac[ssa_form_output_unique] >>
  `bb = db` by metis_tac[wf_function_instruction_block] >>
  metis_tac[LAST_MEM]
QED

Theorem def_on_all_paths_available:
  wf_function fn /\ ssa_form fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\ def_on_all_paths fn bb use_opt v ==>
  def_available_at fn bb use_opt v
Proof
  strip_tac >> drule_all def_on_all_paths_first_witness >> strip_tac >>
  simp[def_available_at_def] >> qexistsl [`db`, `di`] >> simp[] >>
  irule def_on_all_paths_dominating_witness >> metis_tac[]
QED

Theorem reachable_defs_reach_uses_wf_ssa:
  wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  fn_defs_reach_uses fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     phi_well_formed inst.inst_operands /\
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     (!pred. fn_cfg_edge fn pred bb.bb_label <=>
       ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)) ==>
  wf_ssa fn
Proof
  strip_tac >> simp[wf_ssa_def, def_dominates_uses_def] >>
  qx_gen_tac `bb` >> qx_gen_tac `inst` >> strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (`phi_well_formed inst.inst_operands /\
       ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
       (!pred. fn_cfg_edge fn pred bb.bb_label <=>
         ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred)` by
        metis_tac[] >>
      simp[phi_edge_uses_wf_def] >> rpt strip_tac >>
      `fn_cfg_edge fn pred bb.bb_label` by metis_tac[pairTheory.FST] >>
      `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred` by
        (fs[fn_cfg_edge_def] >> metis_tac[]) >>
      qexists `pred_bb` >> simp[] >>
      conj_tac >- metis_tac[pairTheory.FST] >>
      irule def_on_all_paths_available >>
      fs[all_reachable_def, fn_defs_reach_uses_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> irule def_on_all_paths_available >>
  fs[all_reachable_def, fn_defs_reach_uses_def] >> metis_tac[]
QED
