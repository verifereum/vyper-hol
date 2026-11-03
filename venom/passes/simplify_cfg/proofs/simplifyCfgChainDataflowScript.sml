Theory simplifyCfgChainDataflow
Ancestors
  simplifyCfgRepairDataflow simplifyCfgPhiRepair simplifyCfgDataflow
  simplifyCfgLabelProps simplifyCfgStruct simplifyCfgDefs
  venomWf venomInst venomExecSemantics venomExecProofs cfgTransform cfgWf list rich_list

Theorem bb_output_in_front:
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  MEM inst (FRONT bb.bb_instructions)
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\ is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `MEM (LAST bb.bb_instructions) bb.bb_instructions` by metis_tac[LAST_MEM] >>
  `inst_wf (LAST bb.bb_instructions)` by fs[EVERY_MEM] >>
  `(LAST bb.bb_instructions).inst_outputs = []` by simp[terminator_no_outputs] >>
  `inst <> LAST bb.bb_instructions` by metis_tac[MEM] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    simp[APPEND_FRONT_LAST] >>
  metis_tac[MEM_APPEND, MEM]
QED

Theorem merge_blocks_output_member:
  wf_function fn /\ fn_inst_wf fn /\ MEM a fn.fn_blocks /\
  (MEM inst a.bb_instructions \/ MEM inst b.bb_instructions) /\
  MEM v inst.inst_outputs ==>
  MEM inst (merge_blocks a b).bb_instructions
Proof
  strip_tac >> simp[merge_blocks_def] >> disj1_tac >>
  irule bb_output_in_front >>
  fs[wf_function_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem inst_wf_subst_phi_label:
  inst_wf inst /\ inst.inst_opcode = PHI ==>
  inst_wf (subst_label_inst old_lbl new_lbl inst)
Proof
  strip_tac >>
  fs[inst_wf_def, subst_label_inst_def, phi_well_formed_subst_label_ops]
QED

Theorem chain_merge_fn_inst_wf:
  fn_inst_wf fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks ==>
  fn_inst_wf (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))
Proof
  strip_tac >>
  rewrite_tac[fn_inst_wf_def] >> simp[] >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions)
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label fn.fn_blocks)) (bb_succs (merge_blocks a b)))` by
    (irule chain_merge_every_inst >>
     fs[fn_inst_wf_def, EVERY_MEM, inst_wf_subst_phi_label] >> metis_tac[]) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem update_succ_phi_labels_block_correspondence:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!inst. inst.inst_opcode = PHI ==>
    project (subst_label_inst old_lbl new_lbl inst) = project inst) ==>
  (!bb'. MEM bb' (update_succ_phi_labels old_lbl new_lbl bbs succs) ==>
    ?bb. MEM bb bbs /\ bb'.bb_label = bb.bb_label /\
         MAP project bb'.bb_instructions = MAP project bb.bb_instructions) /\
  (!bb. MEM bb bbs ==>
    ?bb'. MEM bb' (update_succ_phi_labels old_lbl new_lbl bbs succs) /\
         bb'.bb_label = bb.bb_label /\
         MAP project bb'.bb_instructions = MAP project bb.bb_instructions)
Proof
  strip_tac >>
  `MAP (\bb. (bb.bb_label, MAP project bb.bb_instructions))
     (update_succ_phi_labels old_lbl new_lbl bbs succs) =
   MAP (\bb. (bb.bb_label, MAP project bb.bb_instructions)) bbs` by
    (irule update_succ_phi_labels_block_projection >> simp[]) >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  qpat_x_assum `!inst. _` kall_tac >>
  conj_tac >> rpt strip_tac
  >- (`MEM (bb'.bb_label, MAP project bb'.bb_instructions)
        (MAP (\bb. (bb.bb_label, MAP project bb.bb_instructions))
          (update_succ_phi_labels old_lbl new_lbl bbs succs))` by
        (simp[MEM_MAP] >> metis_tac[]) >>
      qpat_x_assum `MEM (_,_) (MAP _ _)` mp_tac >>
      asm_rewrite_tac[] >> simp[MEM_MAP] >> metis_tac[]) >>
  `MEM (bb.bb_label, MAP project bb.bb_instructions)
     (MAP (\bb. (bb.bb_label, MAP project bb.bb_instructions)) bbs)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MAP _ _ = MAP _ _` (assume_tac o GSYM) >>
  qpat_x_assum `MEM (_,_) (MAP _ _)` mp_tac >>
  asm_rewrite_tac[] >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem update_succ_phi_labels_output_witness:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM bb bbs /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  ?bb' inst'. MEM bb' (update_succ_phi_labels old_lbl new_lbl bbs succs) /\
    bb'.bb_label = bb.bb_label /\ MEM inst' bb'.bb_instructions /\
    MEM v inst'.inst_outputs
Proof
  strip_tac >>
  `?bb'. MEM bb' (update_succ_phi_labels old_lbl new_lbl bbs succs) /\
    bb'.bb_label = bb.bb_label /\
    MAP (\i. i.inst_outputs) bb'.bb_instructions =
    MAP (\i. i.inst_outputs) bb.bb_instructions` by
    (irule (cj 2 update_succ_phi_labels_block_correspondence) >>
     simp[subst_label_inst_def] >> metis_tac[]) >>
  qexists `bb'` >> simp[] >>
  `MEM inst.inst_outputs (MAP (\i. i.inst_outputs) bb.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qpat_x_assum `MEM _ (MAP _ _)` mp_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem chain_merge_base_output_witness:
  wf_function fn /\ fn_inst_wf fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  a.bb_label <> b.bb_label /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  ?bb'. MEM bb'
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks)) /\
    bb'.bb_label = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label) /\
    MEM inst bb'.bb_instructions
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  Cases_on `bb.bb_label = b.bb_label`
  >- (`bb = b` by metis_tac[same_label_same_block] >> gvs[] >>
      qexists `merge_blocks a b` >> simp[merge_blocks_def] >>
      simp[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
      qexists `a` >> simp[merge_blocks_def]) >>
  Cases_on `bb.bb_label = a.bb_label`
  >- (`bb = a` by metis_tac[same_label_same_block] >> gvs[] >>
      qexists `merge_blocks a b` >>
      `MEM inst (merge_blocks a b).bb_instructions` by
        (irule merge_blocks_output_member >> metis_tac[]) >>
      simp[merge_blocks_def] >>
      simp[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
      qexists `a` >> simp[merge_blocks_def]) >>
  qexists `bb` >> simp[] >>
  simp[replace_block_def, remove_block_def, MEM_MAP, MEM_FILTER] >>
  qexists `bb` >> simp[]
QED

Theorem chain_merge_output_witness:
  wf_function fn /\ fn_inst_wf fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  ?bb' inst'. MEM bb'
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
    bb'.bb_label = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label) /\
    MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs
Proof
  strip_tac >>
  `a.bb_label <> b.bb_label` by fs[can_merge_blocks_def] >>
  drule_all chain_merge_base_output_witness >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks)))` by
    (irule chain_merge_base_labels >> fs[wf_function_def]) >>
  drule_all update_succ_phi_labels_output_witness >>
  disch_then (qspecl_then [`bb_succs (merge_blocks a b)`, `b.bb_label`, `a.bb_label`]
    mp_tac) >>
  metis_tac[]
QED

Theorem chain_merge_earlier_output_witness:
  wf_function fn /\ fn_inst_wf fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs /\ ~MEM b.bb_label p /\
  MEM bb.bb_label (FRONT (chain_prefix a.bb_label b.bb_label p ++ [z])) ==>
  ?bb' inst'. MEM bb'
    (update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
    MEM bb'.bb_label (FRONT p) /\
    MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs
Proof
  strip_tac >> drule_all chain_merge_output_witness >> strip_tac >>
  qexistsl [`bb'`, `inst'`] >> simp[] >>
  fs[chain_prefix_earlier] >> IF_CASES_TAC >> gvs[] >>
  Cases_on `p` >> fs[] >> drule MEM_FRONT >> simp[]
QED

Theorem def_on_all_paths_endpoint_witnesses:
  wf_function fn /\ MEM bb fn.fn_blocks ==>
  (def_on_all_paths fn bb NONE v <=>
   !p. is_fn_path fn p /\ p <> [] /\
       (?entry. fn_entry_label fn = SOME entry /\ HD p = entry) /\
       LAST p = bb.bb_label ==>
       ?db di. MEM db fn.fn_blocks /\ MEM db.bb_label p /\
               MEM di db.bb_instructions /\ MEM v di.inst_outputs)
Proof
  strip_tac >> eq_tac
  >- (simp[def_on_all_paths_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `p` mp_tac) >> simp[] >> strip_tac
      >- (qexistsl [`def_bb`, `def_inst`] >> simp[] >>
          irule EL_MEM >> simp[]) >>
      qexistsl [`bb`, `EL i bb.bb_instructions`] >> simp[EL_MEM] >>
      metis_tac[LAST_MEM]) >>
  strip_tac >> simp[def_on_all_paths_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `path` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `db.bb_label = bb.bb_label`
  >- (`db = bb` by metis_tac[same_label_same_block] >>
      gvs[] >> disj2_tac >> metis_tac[MEM_EL]) >>
  disj1_tac >>
  `path = FRONT path ++ [LAST path]` by simp[APPEND_FRONT_LAST] >>
  `MEM db.bb_label (FRONT path)` by metis_tac[MEM_APPEND, MEM] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  qexistsl [`n`, `db`, `di`] >> simp[] >>
  conj_tac >- (Cases_on `path` >> fs[LENGTH_FRONT, arithmeticTheory.PRE_SUB1]) >>
  Cases_on `path` >> fs[EL_FRONT, LENGTH_FRONT, arithmeticTheory.PRE_SUB1]
QED

Theorem chain_endpoint_path_member:
  p <> [] /\ ~MEM b p /\ LAST p = (if z = b then a else z) /\
  MEM d (chain_prefix a b p ++ (if z = b then [a;b] else [z])) ==>
  MEM (if d = b then a else d) p
Proof
  strip_tac >>
  `!x. MEM x (FRONT p) ==> MEM x p` by
    (Cases_on `p` >> fs[] >> rpt strip_tac >> drule MEM_FRONT >> simp[]) >>
  Cases_on `z = b` >> Cases_on `d = b` >>
  gvs[chain_prefix_mem] >> metis_tac[LAST_MEM]
QED

Theorem chain_merge_entry:
  wf_function fn /\ first_block_no_preds fn /\ MEM a fn.fn_blocks /\
  MEM b fn.fn_blocks /\ can_merge_blocks fn a b ==>
  fn_entry_label (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) = fn_entry_label fn
Proof
  strip_tac >> drule_all chain_merge_entry_label >> strip_tac >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  qmatch_goalsub_abbrev_tac `fn with fn_blocks := bbs` >>
  `MAP (\bb. bb.bb_label) bbs =
    FILTER (\lbl. lbl <> b.bb_label) (fn_labels fn)` by
    (mp_tac chain_merge_fn_labels >> simp[Abbr `bbs`, fn_labels_def]) >>
  `MEM a.bb_label (MAP (\bb. bb.bb_label) bbs)` by
    (asm_rewrite_tac[] >> simp[MEM_FILTER, fn_labels_def, MEM_MAP] >>
     fs[can_merge_blocks_def] >> metis_tac[]) >>
  `bbs <> []` by (strip_tac >> gvs[]) >>
  Cases_on `fn.fn_blocks` >> Cases_on `bbs` >>
  gvs[fn_entry_label_def, entry_block_def]
QED

Theorem chain_merge_endpoint_path_input:
  wf_function fn /\ MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
  can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  p <> [] /\ is_fn_path fn' p /\ MEM (LAST p) (fn_labels fn') /\
  LAST p = (if z = b.bb_label then a.bb_label else z) ==>
  ~MEM b.bb_label p /\
  is_fn_path fn (chain_prefix a.bb_label b.bb_label p ++
    (if z = b.bb_label then [a.bb_label;b.bb_label] else [z])) /\
  HD (chain_prefix a.bb_label b.bb_label p ++
    (if z = b.bb_label then [a.bb_label;b.bb_label] else [z])) = HD p
Proof
  strip_tac >> drule_all chain_merge_path_input >> strip_tac >> simp[] >>
  Cases_on `z = b.bb_label` >> gvs[]
  >- (conj_tac
      >- (irule chain_prefix_path_last_pair >> simp[] >>
          simp[fn_cfg_edge_def] >> qexists `a` >> fs[can_merge_blocks_def]) >>
      irule chain_prefix_head_pair >> simp[]) >>
  simp[chain_prefix_head]
QED

Theorem chain_merge_def_on_all_paths_endpoint:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\ can_merge_blocks fn a b /\
  fn' = (fn with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label fn.fn_blocks))
      (bb_succs (merge_blocks a b))) /\
  MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks /\
  bb'.bb_label = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label) /\
  def_on_all_paths fn bb NONE v ==>
  def_on_all_paths fn' bb' NONE v
Proof
  strip_tac >>
  `lookup_block a.bb_label fn.fn_blocks = SOME a /\
   lookup_block b.bb_label fn.fn_blocks = SOME b` by
    (fs[wf_function_def, fn_labels_def] >> metis_tac[MEM_lookup_block]) >>
  `wf_function fn'` by
    (qpat_assum `fn' = _` SUBST1_TAC >> irule chain_merge_wf >> simp[]) >>
  `fn_entry_label fn' = fn_entry_label fn` by
    (qpat_assum `fn' = _` SUBST1_TAC >> irule chain_merge_entry >> simp[]) >>
  drule_all def_on_all_paths_endpoint_witnesses >> strip_tac >>
  `!p. is_fn_path fn' p /\ p <> [] /\
    (?entry. fn_entry_label fn' = SOME entry /\ HD p = entry) /\
    LAST p = bb'.bb_label ==>
    ?db di. MEM db fn'.fn_blocks /\ MEM db.bb_label p /\
      MEM di db.bb_instructions /\ MEM v di.inst_outputs` suffices_by
    metis_tac[def_on_all_paths_endpoint_witnesses] >>
  rpt strip_tac >>
  `MEM (LAST p) (fn_labels fn')` by
    (pure_rewrite_tac[fn_labels_def, MEM_MAP] >> qexists `bb'` >> simp[]) >>
  `LAST p = (if bb.bb_label = b.bb_label then a.bb_label else bb.bb_label)` by
    metis_tac[] >>
  drule_all chain_merge_endpoint_path_input >> strip_tac >>
  qmatch_asmsub_abbrev_tac `is_fn_path fn expanded` >>
  `expanded <> [] /\ LAST expanded = bb.bb_label` by
    (Cases_on `bb.bb_label = b.bb_label` >> simp[Abbr `expanded`]) >>
  `?db di. MEM db fn.fn_blocks /\ MEM db.bb_label expanded /\
     MEM di db.bb_instructions /\ MEM v di.inst_outputs` by
    (qpat_x_assum `wf_function fn'` kall_tac >>
     drule_all def_on_all_paths_endpoint_witnesses >>
     disch_then (qspec_then `v` mp_tac) >> simp[] >>
     disch_then (qspec_then `expanded` mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all chain_merge_output_witness >> strip_tac >>
  qexistsl [`bb''`, `inst'`] >> simp[] >>
  irule chain_endpoint_path_member >> simp[] >> qexists `bb.bb_label` >>
  fs[Abbr `expanded`]
QED

Theorem update_succ_phi_labels_index_correspondence:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  MEM bb' (update_succ_phi_labels old_lbl new_lbl bbs succs) ==>
  ?bb. MEM bb bbs /\ bb'.bb_label = bb.bb_label /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions ==>
      (EL i bb'.bb_instructions).inst_outputs = (EL i bb.bb_instructions).inst_outputs /\
      ((EL i bb'.bb_instructions).inst_opcode = PHI <=>
       (EL i bb.bb_instructions).inst_opcode = PHI) /\
      ((EL i bb.bb_instructions).inst_opcode <> PHI ==>
       EL i bb'.bb_instructions = EL i bb.bb_instructions))
Proof
  strip_tac >>
  `?bb. MEM bb bbs /\ bb'.bb_label = bb.bb_label /\
    MAP (\i. (i.inst_outputs, if i.inst_opcode = PHI then NONE else SOME i))
      bb'.bb_instructions =
    MAP (\i. (i.inst_outputs, if i.inst_opcode = PHI then NONE else SOME i))
      bb.bb_instructions` by
    (irule (cj 1 update_succ_phi_labels_block_correspondence) >>
     simp[subst_label_inst_def] >> metis_tac[]) >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  qexists `bb` >> simp[] >> gen_tac >> strip_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL i`) >>
  simp[EL_MAP] >> rpt IF_CASES_TAC >> gvs[]
QED
