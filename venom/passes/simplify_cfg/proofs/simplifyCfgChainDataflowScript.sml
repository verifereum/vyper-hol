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

Theorem update_succ_phi_labels_block_projection:
  !succs bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!inst. project (subst_label_inst old_lbl new_lbl inst) = project inst) ==>
  MAP (\bb. (bb.bb_label, MAP project bb.bb_instructions))
    (update_succ_phi_labels old_lbl new_lbl bbs succs) =
  MAP (\bb. (bb.bb_label, MAP project bb.bb_instructions)) bbs
Proof
  Induct_on `succs` >> fs[update_succ_phi_labels_def] >>
  rpt strip_tac >> Cases_on `lookup_block h bbs` >> simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  `bb.bb_label = h` by metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `FOLDL stepfn bs succs` >>
  `MAP (\b. (b.bb_label, MAP project b.bb_instructions)) bs =
   MAP (\b. (b.bb_label, MAP project b.bb_instructions)) bbs` by
    (simp[Abbr `bs`] >> irule replace_block_projection >>
     simp[MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bs)` by
    simp[Abbr `bs`, cfgTransformPropsTheory.fn_labels_replace_block] >>
  first_x_assum (qspec_then `bs` mp_tac) >>
  simp[Abbr `stepfn`]
QED

Theorem update_succ_phi_labels_block_correspondence:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!inst. project (subst_label_inst old_lbl new_lbl inst) = project inst) ==>
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
