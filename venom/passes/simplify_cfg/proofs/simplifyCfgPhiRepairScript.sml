Theory simplifyCfgPhiRepair
Ancestors
  simplifyCfgDataflow simplifyCfgLabelProps simplifyCfgStruct simplifyCfgDefs
  venomWf venomInst venomExecSemantics venomExecProofs cfgTransform list rich_list relation

Theorem is_fn_path_first_predecessor:
  (!q. fn_cfg_edge fn q b ==> q = p) ==>
  !path. path <> [] /\ is_fn_path fn path /\ HD path <> b /\ LAST path = b ==>
  ?pre. pre <> [] /\ is_fn_path fn pre /\ HD pre = HD path /\
        LAST pre = p /\ ~MEM b pre
Proof
  strip_tac >> Induct >> simp[] >> qx_gen_tac `x` >>
  Cases_on `path` >> simp[is_fn_path_def] >> rpt strip_tac >>
  rename1 `fn_cfg_edge fn x y` >>
  Cases_on `y = b`
  >- (`x = p` by metis_tac[] >> qexists `[x]` >> simp[is_fn_path_def]) >>
  qpat_x_assum `_ ==> ?pre. _` mp_tac >> simp[] >>
  disch_then (qx_choose_then `pre` strip_assume_tac) >>
  qexists `x::pre` >> simp[is_fn_path_prepend] >>
  Cases_on `pre` >> gvs[]
QED

Theorem unique_predecessor_avoiding_path:
  fn_entry_label fn = SOME entry /\ fn_reachable fn b /\ b <> entry /\
  (!q. fn_cfg_edge fn q b ==> q = p) ==>
  ?path. path <> [] /\ is_fn_path fn path /\ HD path = entry /\
         LAST path = p /\ ~MEM b path
Proof
  strip_tac >> fs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >> gvs[] >>
  drule is_fn_path_first_predecessor >>
  disch_then (qspec_then `path` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem unique_predecessor_external_def:
  fn_entry_label fn = SOME entry /\ fn_reachable fn b /\ b <> entry /\
  (!q. fn_cfg_edge fn q b ==> q = pred_bb.bb_label) /\
  MEM pred_bb fn.fn_blocks /\ def_on_all_paths fn pred_bb NONE v ==>
  ?db di. MEM db fn.fn_blocks /\ fn_reachable fn db.bb_label /\
          db.bb_label <> b /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs
Proof
  strip_tac >> drule_all unique_predecessor_avoiding_path >>
  disch_then (qx_choose_then `path` strip_assume_tac) >>
  qpat_x_assum `def_on_all_paths fn pred_bb NONE v` mp_tac >>
  simp[def_on_all_paths_def] >> disch_then (qspec_then `path` mp_tac) >>
  simp[] >> strip_tac
  >- (`MEM def_bb.bb_label path` by
        (simp[MEM_EL] >> qexists `k` >> simp[]) >>
      qexistsl [`def_bb`, `def_inst`] >> simp[] >> conj_tac
      >- (irule entry_path_member_reachable >> metis_tac[]) >> metis_tac[]) >>
  qexistsl [`pred_bb`, `EL i pred_bb.bb_instructions`] >> simp[] >>
  `MEM pred_bb.bb_label path` by metis_tac[LAST_MEM] >>
  conj_tac
  >- (irule entry_path_member_reachable >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> simp[MEM_EL] >> qexists `i` >> simp[]
QED

Definition scfg_phi_safe_def:
  scfg_phi_safe fn <=>
    EVERY (\inst. inst.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions /\
    (!bb inst bb' inst' v.
       MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
       MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
       MEM v inst.inst_outputs /\
       MEM bb' fn.fn_blocks /\ fn_reachable fn bb'.bb_label /\
       MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs ==>
       inst' = inst) /\
    (!bb inst pred_bb.
       MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
       MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
       MEM pred_bb fn.fn_blocks /\ fn_reachable fn pred_bb.bb_label /\
       MEM bb.bb_label (bb_succs pred_bb) ==>
       ?op. resolve_phi pred_bb.bb_label inst.inst_operands = SOME op)
End

Theorem simplify_cfg_fn_ok_phi_safe:
  simplify_cfg_fn_ok fn <=> scfg_phi_safe fn /\ fn_defs_reach_uses fn
Proof
  simp[simplify_cfg_fn_ok_def, scfg_phi_safe_def] >> metis_tac[]
QED

Theorem scfg_phi_safe_entry:
  scfg_phi_safe fn ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions
Proof
  simp[scfg_phi_safe_def]
QED

Theorem scfg_phi_safe_unique_output:
  scfg_phi_safe fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\ MEM v inst.inst_outputs /\
  MEM bb' fn.fn_blocks /\ fn_reachable fn bb'.bb_label /\
  MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs ==>
  inst' = inst
Proof
  simp[scfg_phi_safe_def] >> metis_tac[]
QED

Theorem scfg_phi_safe_coverage:
  scfg_phi_safe fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  MEM pred_bb fn.fn_blocks /\ fn_reachable fn pred_bb.bb_label /\
  MEM bb.bb_label (bb_succs pred_bb) ==>
  ?op. resolve_phi pred_bb.bb_label inst.inst_operands = SOME op
Proof
  simp[scfg_phi_safe_def] >> metis_tac[]
QED

Theorem distinct_projection_member_eq:
  !xs. ALL_DISTINCT (FLAT (MAP f xs)) ==>
  !x y v. MEM x xs /\ MEM y xs /\ MEM v (f x) /\ MEM v (f y) ==> x = y
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  fs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem wf_function_instruction_block:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  MEM inst a.bb_instructions /\ MEM inst b.bb_instructions ==> a = b
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     fn.fn_blocks))` by fs[wf_function_def, fn_inst_ids_distinct_def] >>
  drule distinct_projection_member_eq >>
  disch_then (qspecl_then [`a`, `b`, `inst.inst_id`] mp_tac) >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem ssa_form_output_unique:
  ssa_form fn /\ MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM bb' fn.fn_blocks /\ MEM inst' bb'.bb_instructions /\
  MEM v inst.inst_outputs /\ MEM v inst'.inst_outputs ==> inst' = inst
Proof
  strip_tac >> fs[ssa_form_def] >>
  drule distinct_projection_member_eq >>
  disch_then (qspecl_then [`inst'`, `inst`, `v`] mp_tac) >>
  simp[] >> fs[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[]
QED

Theorem pred_labels_edge:
  MEM p (pred_labels fn b) <=> fn_cfg_edge fn p b
Proof
  simp[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
  metis_tac[]
QED

Theorem single_predecessor_phi_input_external:
  wf_function fn /\ scfg_phi_safe fn /\ fn_defs_reach_uses fn /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
  fn_reachable fn bb.bb_label /\ fn_entry_label fn = SOME entry /\ bb.bb_label <> entry /\
  pred_labels fn bb.bb_label = [p] /\ MEM (p,v) (phi_pairs inst.inst_operands) ==>
  !j. MEM j bb.bb_instructions /\ j.inst_opcode = PHI ==> ~MEM v j.inst_outputs
Proof
  strip_tac >>
  `fn_cfg_edge fn p bb.bb_label` by metis_tac[pred_labels_edge, MEM] >>
  `!q. fn_cfg_edge fn q bb.bb_label ==> q = p` by
    metis_tac[pred_labels_edge, MEM] >>
  `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = p` by
    (fs[fn_cfg_edge_def] >> metis_tac[]) >>
  `def_on_all_paths fn pred_bb NONE v` by
    (fs[fn_defs_reach_uses_def] >> metis_tac[]) >>
  `?db di. MEM db fn.fn_blocks /\ fn_reachable fn db.bb_label /\
     db.bb_label <> bb.bb_label /\ MEM di db.bb_instructions /\ MEM v di.inst_outputs` by
    (irule unique_predecessor_external_def >> simp[] >> qexists `pred_bb` >> simp[]) >>
  rpt strip_tac >>
  `di = j` by (irule scfg_phi_safe_unique_output >> simp[] >> metis_tac[]) >>
  `db = bb` by (irule wf_function_instruction_block >> metis_tac[]) >>
  gvs[]
QED

Theorem wf_ssa_phi_safe:
  wf_ssa fn /\
  EVERY (\inst. inst.inst_opcode <> PHI) (HD fn.fn_blocks).bb_instructions ==>
  scfg_phi_safe fn
Proof
  strip_tac >> simp[scfg_phi_safe_def] >> conj_tac
  >- (rpt strip_tac >> irule ssa_form_output_unique >>
      fs[wf_ssa_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `phi_edge_uses_wf fn bb inst` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[]) >>
  `fn_cfg_edge fn pred_bb.bb_label bb.bb_label` by
    (simp[fn_cfg_edge_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands /\
   ?p. MEM p (phi_pairs inst.inst_operands) /\ FST p = pred_bb.bb_label` by
    (fs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  qpat_x_assum `phi_edge_uses_wf _ _ _` kall_tac >>
  `!ops l. phi_well_formed ops /\ MEM l (MAP FST (phi_pairs ops)) ==>
     ?op. resolve_phi l ops = SOME op` suffices_by
    (disch_then (qspecl_then [`inst.inst_operands`, `pred_bb.bb_label`] mp_tac) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, phi_pairs_def, resolve_phi_def] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED
