(* PHI predecessor support and coverage after guarded bypass. *)
Theory simplifyCfgBypassPhiClosure
Ancestors
  simplifyCfgBypassClosure simplifyCfgBypassPhi
  simplifyCfgBypassStatic simplifyCfgBypassPaths simplifyCfgStaticInterface simplifyCfgMergeAvailability
  simplifyCfgDefs venomWf venomInst venomExecSemantics venomExecProps
  cfgTransform list rich_list
  simplifyCfgBypassDataflow
  simplifyCfgDataflow
  simplifyCfgWfssa

Theorem scfg_update_phi_bypass_pairs:
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\ A <> B ==>
  (MEM (p,v) (phi_pairs (update_phi_bypass A B i).inst_operands) <=>
    if MEM (Label A) i.inst_operands then
      p <> B /\ MEM (p,v) (phi_pairs i.inst_operands)
    else
      ?q. MEM (q,v) (phi_pairs i.inst_operands) /\
        p = if q = B then A else q)
Proof
  strip_tac >> simp[scfg_update_phi_bypass_ops] >>
  Cases_on `MEM (Label A) i.inst_operands` >>
  simp[phi_pairs_remove_phi_label, MEM_FILTER, phi_pairs_subst_label_ops, MEM_MAP] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (rename1 `MEM pr (phi_pairs _)` >> qexists_tac `FST pr` >> simp[]) >>
  qexists_tac `(q,v)` >> simp[]
QED

Theorem scfg_bypass_image_phi:
  i.inst_opcode = PHI ==>
  scfg_bypass_image A B target l i =
    if l = target then update_phi_bypass A B i else i
Proof
  simp[scfg_bypass_image_def, scfg_bypass_term_def, is_terminator_def] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem scfg_bypass_image_pair_origin:
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\ A <> B /\
  MEM (p,v) (phi_pairs (scfg_bypass_image A B target l i).inst_operands) ==>
  MEM (p,v) (phi_pairs i.inst_operands) \/
    l = target /\ p = A /\ MEM (B,v) (phi_pairs i.inst_operands)
Proof
  strip_tac >>
  qpat_x_assum `MEM (p,v) _` mp_tac >> simp[scfg_bypass_image_phi] >>
  Cases_on `l = target` >> simp[] >>
  simp[scfg_update_phi_bypass_pairs] >>
  Cases_on `MEM (Label A) i.inst_operands` >> simp[] >>
  strip_tac >> gvs[] >> Cases_on `q = B` >> gvs[]
QED

Theorem scfg_bypass_phi_origin:
  scfg_bypass_hyp fn a b fn' /\ MEM bb fn'.fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
  ?old_bb old. MEM old_bb fn.fn_blocks /\ old_bb.bb_label <> b.bb_label /\
    bb = scfg_bypass_block a b old_bb /\ MEM old old_bb.bb_instructions /\
    old.inst_opcode = PHI /\ inst_wf old /\
    i = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) old_bb.bb_label old
Proof
  strip_tac >> drule_all (iffLR scfg_bypass_mem) >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM i _` mp_tac >> simp[scfg_bypass_block_def, MEM_MAP] >>
  strip_tac >> gvs[] >> rename1 `MEM old bb'.bb_instructions` >>
  qexistsl [`bb'`, `old`] >> simp[] >>
  `fn_inst_wf fn` by metis_tac[scfg_bypass_old_static, scfg_static_inst_wf] >>
  fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

Theorem scfg_bypass_old_phi_edge:
  scfg_bypass_hyp fn a b fn' /\ MEM bb fn.fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
  MEM (p,v) (phi_pairs i.inst_operands) ==>
  fn_cfg_edge fn p bb.bb_label
Proof
  strip_tac >> `MEM (Label p) i.inst_operands` by
    metis_tac[scfg_phi_pair_label] >>
  `MEM p (pred_labels fn bb.bb_label)` by
    metis_tac[scfg_bypass_hyp_def, scfg_normalized_phi_support] >>
  fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
  metis_tac[]
QED

Theorem scfg_bypass_phi_pair_edge:
  scfg_bypass_hyp fn a b fn' /\ MEM bb fn.fn_blocks /\ bb.bb_label <> b.bb_label /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\ inst_wf i /\
  MEM (p,v) (phi_pairs (scfg_bypass_image a.bb_label b.bb_label
    (HD (bb_succs b)) bb.bb_label i).inst_operands) ==>
  fn_cfg_edge fn' p bb.bb_label
Proof
  strip_tac >>
  `phi_well_formed i.inst_operands` by
    (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def]) >>
  `a.bb_label <> b.bb_label` by
    metis_tac[scfg_bypass_hyp_def, can_bypass_jump_labels_distinct] >>
  drule scfg_bypass_edge_eq >> strip_tac >>
  `HD (bb_succs b) = target` by simp[] >>
  `p <> b.bb_label` by
    (Cases_on `bb.bb_label = target`
     >- (qpat_x_assum `MEM (p,v) _` mp_tac >>
         simp[scfg_bypass_image_phi, scfg_update_phi_bypass_pairs] >>
         Cases_on `MEM (Label a.bb_label) i.inst_operands` >> simp[] >>
         strip_tac >> Cases_on `q = b.bb_label` >> gvs[]) >>
     `MEM (p,v) (phi_pairs i.inst_operands)` by
       (qpat_x_assum `MEM (p,v) _` mp_tac >> simp[scfg_bypass_image_phi]) >>
     drule_all scfg_bypass_old_phi_edge >> strip_tac >>
     strip_tac >> gvs[] >>
     `wf_function fn` by metis_tac[scfg_bypass_old_static, scfg_static_wf] >>
     fs[scfg_bypass_hyp_def] >>
     metis_tac[scfg_bypass_outgoing, wf_function_def]) >>
  simp[] >>
  drule_all scfg_bypass_image_pair_origin >> strip_tac
  >- (disj1_tac >> irule scfg_bypass_old_phi_edge >> metis_tac[]) >>
  simp[]
QED

Theorem scfg_bypass_phi_support:
  scfg_bypass_hyp fn a b fn' /\ MEM bb fn'.fn_blocks /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\ MEM (Label l) i.inst_operands ==>
  MEM l (pred_labels fn' bb.bb_label)
Proof
  strip_tac >>
  `inst_wf i` by
    (`fn_inst_wf fn'` by
       (drule scfg_bypass_base_hyp >> strip_tac >>
        metis_tac[simplifyCfgReachusesTheory.do_merge_jump_fn_inst_wf]) >>
     fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `phi_well_formed i.inst_operands` by
    (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def]) >>
  `MEM l (MAP FST (phi_pairs i.inst_operands))` by metis_tac[phi_pair_label_mem] >>
  `?v. MEM (l,v) (phi_pairs i.inst_operands)` by
    (fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  drule_all scfg_bypass_phi_origin >> strip_tac >> gvs[] >>
  drule_all scfg_bypass_phi_pair_edge >> strip_tac >>
  fs[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER, fn_cfg_edge_def] >>
  metis_tac[]
QED
