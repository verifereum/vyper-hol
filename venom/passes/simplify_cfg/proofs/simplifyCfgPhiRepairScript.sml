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

Theorem stable_partition_order_split:
  ~P y ==>
  ?pre' mid' post'.
    FILTER P (pre ++ x::mid ++ y::post) ++
    FILTER (\z. ~P z) (pre ++ x::mid ++ y::post) =
    pre' ++ x::mid' ++ y::post'
Proof
  strip_tac >> Cases_on `P x`
  >- (qexistsl [`FILTER P pre`,
        `FILTER P mid ++ FILTER P post ++ FILTER (\z. ~P z) pre ++
         FILTER (\z. ~P z) mid`, `FILTER (\z. ~P z) post`] >>
      simp[FILTER_APPEND, APPEND_ASSOC]) >>
  qexistsl [`FILTER P pre ++ FILTER P mid ++ FILTER P post ++ FILTER (\z. ~P z) pre`,
             `FILTER (\z. ~P z) mid`, `FILTER (\z. ~P z) post`] >>
  simp[FILTER_APPEND, APPEND_ASSOC]
QED

Theorem strict_indices_split:
  !xs i j. i < j /\ j < LENGTH xs ==>
    ?pre mid post. xs = pre ++ EL i xs::mid ++ EL j xs::post
Proof
  Induct >> simp[] >> qx_gen_tac `x` >>
  Cases_on `i` >> Cases_on `j` >> simp[] >> rpt strip_tac
  >- (qexists `[]` >> simp[] >>
      qexistsl [`TAKE n xs`, `DROP (SUC n) xs`] >> simp[TAKE_DROP_SUC]) >>
  rename [`a < b`, `b < LENGTH xs`] >>
  first_x_assum (qspecl_then [`a`, `b`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`x::pre`, `mid`, `post`] >> simp[]
QED

Theorem split_strict_indices:
  xs = pre ++ x::mid ++ y::post ==>
  ?i j. i < j /\ j < LENGTH xs /\ EL i xs = x /\ EL j xs = y
Proof
  strip_tac >> qexistsl [`LENGTH pre`, `LENGTH pre + SUC (LENGTH mid)`] >>
  simp[EL_APPEND_EQN]
QED

Theorem fix_phis_in_block_strict_order:
  i < j /\ j < LENGTH bb.bb_instructions /\
  (EL j bb.bb_instructions).inst_opcode <> PHI ==>
  ?i' j'. i' < j' /\
    j' < LENGTH (fix_phis_in_block actual_preds bb).bb_instructions /\
    EL i' (fix_phis_in_block actual_preds bb).bb_instructions =
      fix_phi_inst actual_preds (EL i bb.bb_instructions) /\
    EL j' (fix_phis_in_block actual_preds bb).bb_instructions =
      EL j bb.bb_instructions
Proof
  strip_tac >> drule_all strict_indices_split >> strip_tac >>
  qabbrev_tac `x = EL i bb.bb_instructions` >>
  qabbrev_tac `y = EL j bb.bb_instructions` >>
  irule split_strict_indices >>
  simp[fix_phis_in_block_def] >>
  qpat_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
  simp[MAP_APPEND, fix_phi_inst_non_phi] >>
  qabbrev_tac `A = MAP (fix_phi_inst actual_preds) pre` >>
  qabbrev_tac `B = MAP (fix_phi_inst actual_preds) mid` >>
  qabbrev_tac `C = MAP (fix_phi_inst actual_preds) post` >>
  qabbrev_tac `u = fix_phi_inst actual_preds x` >>
  Cases_on `u.inst_opcode = PHI`
  >- (qexistsl [`FILTER (\z. z.inst_opcode = PHI) B ++
        FILTER (\z. z.inst_opcode = PHI) C ++
        FILTER (\z. z.inst_opcode <> PHI) A ++
        FILTER (\z. z.inst_opcode <> PHI) B`,
        `FILTER (\z. z.inst_opcode <> PHI) C`,
        `FILTER (\z. z.inst_opcode = PHI) A`] >>
      simp[FILTER_APPEND, APPEND_ASSOC]) >>
  qexistsl [`FILTER (\z. z.inst_opcode <> PHI) B`,
    `FILTER (\z. z.inst_opcode <> PHI) C`,
    `FILTER (\z. z.inst_opcode = PHI) A ++
     FILTER (\z. z.inst_opcode = PHI) B ++
     FILTER (\z. z.inst_opcode = PHI) C ++
     FILTER (\z. z.inst_opcode <> PHI) A`] >>
  simp[FILTER_APPEND, APPEND_ASSOC]
QED

Theorem fix_phi_inst_nonempty_outputs:
  filter_phi_ops actual_preds inst.inst_operands <> [] ==>
  (fix_phi_inst actual_preds inst).inst_outputs = inst.inst_outputs
Proof
  Cases_on `inst.inst_opcode = PHI` >> simp[fix_phi_inst_def] >> strip_tac >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
  rename1 `h::t` >> Cases_on `t` >> simp[] >>
  rename1 `h'::t'` >> Cases_on `t'` >> simp[]
QED

Theorem filter_phi_ops_resolve_nonempty:
  phi_well_formed ops /\ MEM p actual_preds /\
  resolve_phi p ops = SOME v ==>
  filter_phi_ops actual_preds ops <> []
Proof
  qid_spec_tac `v` >> qid_spec_tac `p` >> qid_spec_tac `actual_preds` >>
  qid_spec_tac `ops` >> recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def, filter_phi_ops_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fn_reachable_nonentry_predecessor:
  fn_reachable fn b /\ fn_entry_label fn <> SOME b ==>
  ?pb. MEM pb fn.fn_blocks /\ fn_reachable fn pb.bb_label /\
       MEM b (bb_succs pb)
Proof
  simp[fn_reachable_def] >> rpt strip_tac >>
  drule (iffLR RTC_CASES2) >> strip_tac >> gvs[] >>
  fs[fn_cfg_edge_def] >> metis_tac[]
QED

Theorem fix_phi_inst_reachable_outputs:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ scfg_phi_safe fn /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
  (fix_phi_inst (pred_labels fn bb.bb_label) inst).inst_outputs = inst.inst_outputs
Proof
  strip_tac >> Cases_on `inst.inst_opcode = PHI`
  >- (irule fix_phi_inst_nonempty_outputs >>
      `fn_reachable fn bb.bb_label` by fs[cfgWfTheory.all_reachable_def] >>
      `fn_entry_label fn <> SOME bb.bb_label` by
        (spose_not_then assume_tac >>
         `bb = HD fn.fn_blocks` by
           (irule same_label_same_block >> conj_tac
            >- (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def]) >>
            qexists `fn` >> Cases_on `fn.fn_blocks` >> gvs[]) >>
         fs[scfg_phi_safe_def, EVERY_MEM] >> metis_tac[]) >>
      drule_all fn_reachable_nonentry_predecessor >> strip_tac >>
      drule_all scfg_phi_safe_coverage >> strip_tac >>
      irule filter_phi_ops_resolve_nonempty >> conj_tac
      >- (`inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
          gvs[inst_wf_def]) >>
      qexistsl [`pb.bb_label`, `op`] >>
      simp[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
      metis_tac[]) >>
  simp[fix_phi_inst_non_phi]
QED

Theorem filter_phi_ops_pairs:
  !ops. phi_well_formed ops ==>
  phi_pairs (filter_phi_ops actual_preds ops) =
  FILTER (\p. MEM (FST p) actual_preds) (phi_pairs ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, filter_phi_ops_def, phi_pairs_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[phi_pairs_def]
QED

Theorem fix_phi_inst_surviving_pairs:
  phi_well_formed inst.inst_operands /\
  (fix_phi_inst actual_preds inst).inst_opcode = PHI ==>
  phi_pairs (fix_phi_inst actual_preds inst).inst_operands =
  FILTER (\p. MEM (FST p) actual_preds) (phi_pairs inst.inst_operands)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[fix_phi_inst_def] >>
  Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
  rename1 `h::t` >> Cases_on `t` >> gvs[] >>
  rename1 `h'::t'` >> Cases_on `t'` >> gvs[] >>
  metis_tac[filter_phi_ops_pairs]
QED

Theorem fix_phi_inst_ordinary_use:
  (inst.inst_opcode = PHI ==> phi_well_formed inst.inst_operands) /\
  (fix_phi_inst actual_preds inst).inst_opcode <> PHI /\
  MEM (Var v) (fix_phi_inst actual_preds inst).inst_operands ==>
  (inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands) \/
  (inst.inst_opcode = PHI /\ ?p.
    filter_phi_ops actual_preds inst.inst_operands = [Label p; Var v])
Proof
  Cases_on `inst.inst_opcode = PHI`
  >- (strip_tac >> gvs[] >>
      `phi_well_formed (filter_phi_ops actual_preds inst.inst_operands)` by
        simp[filter_phi_ops_well_formed] >>
      gvs[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops actual_preds inst.inst_operands` >> gvs[] >>
      rename1 `h::t` >> Cases_on `t` >> gvs[phi_well_formed_def] >>
      rename1 `h'::t'` >> Cases_on `t'` >> gvs[] >>
      Cases_on `h` >> gvs[phi_well_formed_def]) >>
  simp[fix_phi_inst_non_phi]
QED

Theorem fix_phis_in_block_member:
  MEM repaired (fix_phis_in_block actual_preds bb).bb_instructions <=>
  ?inst. MEM inst bb.bb_instructions /\ repaired = fix_phi_inst actual_preds inst
Proof
  simp[fix_phis_in_block_def, MEM_FILTER, MEM_MAP] >> metis_tac[]
QED

Theorem fix_phis_in_block_ordinary_use:
  fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  MEM repaired (fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions /\
  repaired.inst_opcode <> PHI /\ MEM (Var v) repaired.inst_operands ==>
  ?inst. MEM inst bb.bb_instructions /\
    repaired = fix_phi_inst (pred_labels fn bb.bb_label) inst /\
    ((inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands) \/
     (inst.inst_opcode = PHI /\ ?p.
       filter_phi_ops (pred_labels fn bb.bb_label) inst.inst_operands = [Label p; Var v]))
Proof
  strip_tac >> fs[fix_phis_in_block_member] >>
  qexists `inst` >> simp[] >> irule fix_phi_inst_ordinary_use >>
  simp[] >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[inst_wf_def]
QED

Theorem fix_phi_inst_single_pair:
  inst.inst_opcode = PHI /\
  filter_phi_ops actual_preds inst.inst_operands = [Label p; Var v] ==>
  fix_phi_inst actual_preds inst =
    inst with <| inst_opcode := ASSIGN; inst_operands := [Var v] |>
Proof
  simp[fix_phi_inst_def]
QED

Theorem fix_phis_in_block_phi_pair:
  fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  MEM repaired (fix_phis_in_block (pred_labels fn bb.bb_label) bb).bb_instructions /\
  repaired.inst_opcode = PHI /\ MEM (p,v) (phi_pairs repaired.inst_operands) ==>
  ?inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    repaired = fix_phi_inst (pred_labels fn bb.bb_label) inst /\
    MEM (p,v) (phi_pairs inst.inst_operands) /\ fn_cfg_edge fn p bb.bb_label
Proof
  strip_tac >> fs[fix_phis_in_block_member] >>
  `inst.inst_opcode = PHI` by
    (spose_not_then assume_tac >> gvs[fix_phi_inst_non_phi]) >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  `phi_well_formed inst.inst_operands` by gvs[inst_wf_def] >>
  gvs[] >> drule_all fix_phi_inst_surviving_pairs >> strip_tac >>
  qexists `inst` >> simp[] >>
  gvs[MEM_FILTER, pred_labels_edge]
QED

Theorem filter_phi_ops_single_pair_source:
  phi_well_formed ops /\
  filter_phi_ops actual_preds ops = [Label p; Var v] ==>
  MEM (p,v) (phi_pairs ops) /\ MEM p actual_preds
Proof
  strip_tac >> drule filter_phi_ops_pairs >>
  disch_then (qspec_then `actual_preds` mp_tac) >>
  simp[phi_pairs_def] >>
  disch_then (mp_tac o Q.AP_TERM `MEM (p,v)`) >>
  simp[MEM_FILTER]
QED
