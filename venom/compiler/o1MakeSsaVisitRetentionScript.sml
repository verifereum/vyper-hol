Theory o1MakeSsaVisitRetention
Ancestors
  o1MakeSsaVisitTrace o1MakeSsaReaching makeSsaCurrentDefs
  makeSsaCurrentInduct venomInst list pair alist

Theorem retention_inst_phi:
  rename_current_inst s rs i = (rt,t,out) /\ i.inst_opcode = PHI ==>
  out.inst_opcode = PHI /\ out.inst_operands = i.inst_operands
Proof
  simp[rename_current_inst_def] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[]
QED

Theorem retention_block_phi:
  !insts s rs rt t outs n.
  rename_current_block_insts s rs insts = (rt,t,outs) /\
  n < LENGTH insts /\ (EL n insts).inst_opcode = PHI ==>
  n < LENGTH outs /\ (EL n outs).inst_opcode = PHI /\
  (EL n outs).inst_operands = (EL n insts).inst_operands
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on `n` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[retention_inst_phi]
QED

Theorem retention_pairs_index:
  j < LENGTH (phi_pairs ops) /\ EL j (phi_pairs ops) = (p,x) ==>
  j < LENGTH (phi_pairs (update_current_phi_for_pred rs pred ops)) /\
  EL j (phi_pairs (update_current_phi_for_pred rs pred ops)) =
    (p,if p = pred then latest_current_name rs x else x)
Proof
  simp[reaching_phi_pairs_update, EL_MAP]
QED

(* A slot includes both bounds, so no out-of-range EL fact is used. *)
Definition retained_slot_def:
  retained_slot n j p x insts <=>
    n < LENGTH insts /\ (EL n insts).inst_opcode = PHI /\
    j < LENGTH (phi_pairs (EL n insts).inst_operands) /\
    EL j (phi_pairs (EL n insts).inst_operands) = (p,x)
End

Definition block_slot_def:
  block_slot q n j p x bbs <=>
    ?bb. lookup_block q bbs = SOME bb /\
      retained_slot n j p x bb.bb_instructions
End

Theorem retention_rename_slot:
  rename_current_block_insts s rs insts = (rt,t,outs) /\
  retained_slot n j p x insts ==> retained_slot n j p x outs
Proof
  rw[retained_slot_def] >> drule_all retention_block_phi >> simp[]
QED

Theorem retention_patch_slot:
  retained_slot n j p x insts ==>
  retained_slot n j p
    (if p = pred then latest_current_name rs x else x)
    (MAP (\i. if i.inst_opcode <> PHI then i else
      i with inst_operands := update_current_phi_for_pred rs pred i.inst_operands) insts)
Proof
  simp[retained_slot_def, EL_MAP] >> strip_tac >> simp[] >>
  drule_all retention_pairs_index >> simp[]
QED

Theorem retention_lookup_replace:
  bb'.bb_label = lbl ==>
  lookup_block q (replace_block lbl bb' bbs) =
    if q = lbl /\ IS_SOME (lookup_block lbl bbs) then SOME bb'
    else lookup_block q bbs
Proof
  Induct_on `bbs` >> simp[cfgTransformTheory.replace_block_def,
    lookup_block_def, FIND_thm] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> Cases_on `h.bb_label = q` >>
  gvs[] >> Cases_on `q = lbl` >>
  gvs[lookup_block_def, cfgTransformTheory.replace_block_def]
QED

Theorem retention_replace_rename:
  lookup_block lbl bbs = SOME bb /\
  rename_current_block_insts s rs bb.bb_instructions = (rt,t,outs) /\
  block_slot q n j p x bbs ==>
  block_slot q n j p x (replace_block lbl (bb with bb_instructions := outs) bbs)
Proof
  rpt strip_tac >>
  `bb.bb_label = lbl` by metis_tac[makeSsaHelperTheory.lookup_block_label] >>
  fs[block_slot_def] >>
  simp[retention_lookup_replace] >> Cases_on `q = lbl` >> gvs[]
  >- (metis_tac[retention_rename_slot]) >>
  metis_tac[]
QED

Theorem retention_replace_patch:
  lookup_block lbl bbs = SOME bb /\ block_slot q n j p x bbs ==>
  block_slot q n j p
    (if q = lbl /\ p = pred then latest_current_name rs x else x)
    (replace_block lbl (bb with bb_instructions :=
      MAP (\i. if i.inst_opcode <> PHI then i else
        i with inst_operands := update_current_phi_for_pred rs pred i.inst_operands)
        bb.bb_instructions) bbs)
Proof
  rpt strip_tac >>
  `bb.bb_label = lbl` by metis_tac[makeSsaHelperTheory.lookup_block_label] >>
  fs[block_slot_def] >> simp[retention_lookup_replace] >>
  Cases_on `q = lbl` >> gvs[]
  >- (metis_tac[retention_patch_slot]) >>
  metis_tac[]
QED

Theorem retention_succ_slots:
  !succs bbs q n j p x rs pred.
  ALL_DISTINCT succs /\ block_slot q n j p x bbs ==>
  block_slot q n j p
    (if MEM q succs /\ p = pred then latest_current_name rs x else x)
    (update_current_succ_phis rs pred bbs succs)
Proof
  Induct >> simp[update_current_succ_phis_def] >> rpt gen_tac >>
  strip_tac >> Cases_on `lookup_block h bbs` >> simp[]
  >- (`q <> h` by (spose_not_then assume_tac >> gvs[block_slot_def]) >>
      fs[update_current_succ_phis_def] >> metis_tac[]) >>
  drule_all retention_replace_patch >>
  disch_then (qspecl_then [`rs`,`pred`] assume_tac) >>
  fs[update_current_succ_phis_def] >>
  Cases_on `q = h` >> Cases_on `p = pred` >> gvs[] >> metis_tac[]
QED

Definition slot_name_def:
  (slot_name q p x [] = x) /\
  (slot_name q p x (e::es) = slot_name q p
    (if e.sve_label = p /\ MEM q e.sve_succs
     then latest_current_name e.sve_out x else x) es)
End

Theorem slot_name_append:
  !es x fs. slot_name q p x (es ++ fs) =
    slot_name q p (slot_name q p x es) fs
Proof
  Induct >> simp[slot_name_def]
QED

Theorem retention_visit_slots:
  (!tree path s rs bbs sm ct t final events q n j p x.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
    block_slot q n j p x bbs ==>
    block_slot q n j p (slot_name q p x events) final) /\
  (!trees path s ctrs stacks bbs sm ct t final events q n j p x.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
    block_slot q n j p x bbs ==>
    block_slot q n j p (slot_name q p x events) final)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[]
      >- (rpt strip_tac >> gvs[slot_name_def]) >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      drule_all retention_replace_rename >> strip_tac >>
      `ALL_DISTINCT (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss)` by
        (Cases_on `ALOOKUP sm lbl` >> simp[] >> metis_tac[]) >>
      drule_all retention_succ_slots >>
      disch_then (qspecl_then [`rs1`,`lbl`] assume_tac) >>
      fs[slot_name_def] >> metis_tac[]) 
  >- simp[visit_blocks_def, slot_name_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[slot_name_append] >> metis_tac[]
QED

Theorem retention_event_labels:
  (!tree path s rs bbs sm result events.
    visit_blocks path s rs bbs sm tree = (result,events) ==>
    (!e. MEM e events ==> MEM e.sve_label (dom_tree_postorder tree)) /\
    (ALL_DISTINCT (dom_tree_postorder tree) ==>
      ALL_DISTINCT (MAP (\e. e.sve_label) events))) /\
  (!trees path s ctrs stacks bbs sm result events.
    visit_children path s ctrs stacks bbs sm trees = (result,events) ==>
    (!e. MEM e events ==> MEM e.sve_label (FLAT (MAP dom_tree_postorder trees))) /\
    (ALL_DISTINCT (FLAT (MAP dom_tree_postorder trees)) ==>
      ALL_DISTINCT (MAP (\e. e.sve_label) events)))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      fs[dom_tree_postorder_def, ALL_DISTINCT_APPEND, MEM_MAP] >>
      metis_tac[]) 
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def] >> rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  fs[ALL_DISTINCT_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem slot_name_absent:
  !es x. (!e. MEM e es ==> e.sve_label <> p \/ ~MEM q e.sve_succs) ==>
    slot_name q p x es = x
Proof
  Induct >> simp[slot_name_def] >> metis_tac[]
QED

Theorem slot_name_unique:
  !es x e. ALL_DISTINCT (MAP (\e. e.sve_label) es) /\ MEM e es /\
    e.sve_label = p /\ MEM q e.sve_succs ==>
    slot_name q p x es = latest_current_name e.sve_out x
Proof
  Induct >> simp[slot_name_def] >> rpt gen_tac >> strip_tac
  >- (gvs[] >> irule slot_name_absent >> fs[MEM_MAP] >> metis_tac[]) >>
  `h.sve_label <> p` by (fs[MEM_MAP] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem visit_slot_retained:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  block_slot q n j p x bbs /\ MEM e events /\
  e.sve_label = p /\ MEM q e.sve_succs ==>
  block_slot q n j p (latest_current_name e.sve_out x) final
Proof
  rpt strip_tac >>
  drule (cj 1 retention_event_labels) >> strip_tac >>
  `ALL_DISTINCT (MAP (\e. e.sve_label) events)` by simp[] >>
  drule_all (cj 1 retention_visit_slots) >>
  drule_all slot_name_unique >> simp[]
QED

Theorem visit_slot_unchanged:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  block_slot q n j p x bbs /\
  (!e. MEM e events ==> e.sve_label <> p \/ ~MEM q e.sve_succs) ==>
  block_slot q n j p x final
Proof
  rpt strip_tac >>
  drule_all (cj 1 retention_visit_slots) >>
  `slot_name q p x events = x` by metis_tac[slot_name_absent] >> simp[]
QED

(* Expanded consumer interface: instruction and pair positions remain in range. *)
Theorem visit_phi_index_retained:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  lookup_block q bbs = SOME bb /\ n < LENGTH bb.bb_instructions /\
  (EL n bb.bb_instructions).inst_opcode = PHI /\
  j < LENGTH (phi_pairs (EL n bb.bb_instructions).inst_operands) /\
  EL j (phi_pairs (EL n bb.bb_instructions).inst_operands) = (p,x) /\
  MEM e events /\ e.sve_label = p /\ MEM q e.sve_succs ==>
  ?bb'. lookup_block q final = SOME bb' /\
    n < LENGTH bb'.bb_instructions /\
    (EL n bb'.bb_instructions).inst_opcode = PHI /\
    j < LENGTH (phi_pairs (EL n bb'.bb_instructions).inst_operands) /\
    EL j (phi_pairs (EL n bb'.bb_instructions).inst_operands) =
      (p,latest_current_name e.sve_out x)
Proof
  rpt strip_tac >>
  `block_slot q n j p x bbs` by
    (simp[block_slot_def, retained_slot_def] >> metis_tac[]) >>
  drule_all visit_slot_retained >> simp[block_slot_def, retained_slot_def]
QED
