Theory o1LabelFlowMiddleOwnership
Ancestors
  o1MakeSsaEventOwnership o1MakeSsaCallOwnership o1MakeSsaOwnership
  o1MakeSsaVisitTrace makeSsaCurrentInduct makeSsaDefs list pair pred_set

Theorem owner_output_rel_mono:
  LIST_REL (\v n. (n,v) IN H) vs ns /\ H SUBSET Hf ==>
  LIST_REL (\v n. (n,v) IN Hf) vs ns
Proof
  simp[LIST_REL_EL_EQN, SUBSET_DEF] >> metis_tac[]
QED

Theorem owner_inst_rel_mono:
  LIST_REL (\i j. LIST_REL (\v n. (n,v) IN H)
    i.inst_outputs j.inst_outputs) is js /\ H SUBSET Hf ==>
  LIST_REL (\i j. LIST_REL (\v n. (n,v) IN Hf)
    i.inst_outputs j.inst_outputs) is js
Proof
  simp[LIST_REL_EL_EQN, SUBSET_DEF] >> metis_tac[]
QED

Theorem current_outputs_common_owner:
  !outs s rs rs' s' ns V H.
  rename_current_outputs s rs outs = (rs',s',ns) /\
  current_rename_owner V H s rs /\ set outs SUBSET V ==>
  ?Hf. H SUBSET Hf /\ current_rename_owner V Hf s' rs' /\
      LIST_REL (\v n. (n,v) IN Hf) outs ns
Proof
  Induct >- (simp[rename_current_outputs_def] >> metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[INSERT_SUBSET] >>
  drule_all current_rename_owner_push >> strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `Hf` >> simp[] >> gvs[SUBSET_DEF]
QED

Theorem current_inst_common_owner:
  rename_current_inst s rs inst = (rs',s',inst') /\
  current_rename_owner V H s rs /\ set inst.inst_outputs SUBSET V ==>
  ?Hf. H SUBSET Hf /\ current_rename_owner V Hf s' rs' /\
      LIST_REL (\v n. (n,v) IN Hf) inst.inst_outputs inst'.inst_outputs
Proof
  simp[rename_current_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule_all current_outputs_common_owner >> strip_tac >> gvs[] >>
  qexists_tac `Hf` >> simp[]
QED

Theorem current_block_common_owner:
  !insts s rs rs' s' insts' V H.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  current_rename_owner V H s rs /\
  EVERY (\i. set i.inst_outputs SUBSET V) insts ==>
  ?Hf. H SUBSET Hf /\ current_rename_owner V Hf s' rs' /\
    LIST_REL (\i j. LIST_REL (\v n. (n,v) IN Hf)
      i.inst_outputs j.inst_outputs) insts insts'
Proof
  Induct >- (simp[rename_current_block_insts_def] >> metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all current_inst_common_owner >> strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `Hf'` >> simp[] >>
  metis_tac[SUBSET_TRANS, owner_output_rel_mono]
QED

Theorem visit_common_rename_owner:
  (!tree path s rs bbs sm ct t final events V H.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    current_rename_owner V H s rs /\
    EVERY (\e. EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before) events ==>
    ?Hf. H SUBSET Hf /\ current_rename_owner V Hf t (ct,SND rs) /\
      (!e. MEM e events ==>
        current_stack_owner V Hf (SND e.sve_in) /\
        current_stack_owner V Hf (SND e.sve_out) /\
        LIST_REL (\i j. LIST_REL (\v n. (n,v) IN Hf)
          i.inst_outputs j.inst_outputs) e.sve_before e.sve_after)) /\
  (!trees path s ctrs stacks bbs sm ct t final events V H.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    current_rename_owner V H s (ctrs,stacks) /\
    EVERY (\e. EVERY (\i. set i.inst_outputs SUBSET V) e.sve_before) events ==>
    ?Hf. H SUBSET Hf /\ current_rename_owner V Hf t (ct,stacks) /\
      (!e. MEM e events ==>
        current_stack_owner V Hf (SND e.sve_in) /\
        current_stack_owner V Hf (SND e.sve_out) /\
        LIST_REL (\i j. LIST_REL (\v n. (n,v) IN Hf)
          i.inst_outputs j.inst_outputs) e.sve_before e.sve_after))
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[]
      >- (rpt strip_tac >> gvs[] >> PairCases_on `rs` >> gvs[] >>
          metis_tac[SUBSET_REFL]) >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      suspend "node")
  >- (simp[visit_blocks_def] >> rpt strip_tac >> gvs[] >>
      metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  suspend "children"
QED

Resume visit_common_rename_owner[node]:
  drule_all current_block_common_owner >> strip_tac >>
  PairCases_on `rs1` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `Hf'` >>
  `H SUBSET Hf'` by metis_tac[SUBSET_TRANS] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (PairCases_on `rs` >> gvs[] >>
      irule current_rename_owner_restore >>
      conj_tac >- (qexistsl_tac [`H`,`rs0`,`s`] >> simp[]) >>
      qexists_tac `rs11` >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `rs` >> gvs[current_rename_owner_def] >>
  metis_tac[current_stack_owner_mono, owner_inst_rel_mono]
QED

Resume visit_common_rename_owner[children]:
  qpat_x_assum `!path s rs bbs sm ct t final events V H. _` drule_all >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `Hf'` >> conj_tac >- metis_tac[SUBSET_TRANS] >>
  simp[] >> rpt strip_tac >>
  metis_tac[current_stack_owner_mono, owner_inst_rel_mono]
QED


Finalise visit_common_rename_owner

Theorem current_stack_latest_owner:
  current_name_owner V H s /\ current_stack_owner V H (SND rs) /\
  v IN V ==> (latest_current_name rs v,v) IN H
Proof
  PairCases_on `rs` >> simp[latest_current_name_def] >> strip_tac >>
  Cases_on `ALOOKUP rs1 v`
  >- (simp[] >> metis_tac[current_name_owner_identity]) >>
  rename1 `ALOOKUP rs1 v = SOME ns` >> Cases_on `ns` >> simp[]
  >- metis_tac[current_name_owner_identity] >>
  drule_all current_stack_owner_lookup >> simp[]
QED

Theorem current_rename_common_unique:
  current_rename_owner V H s rs /\ (n,v) IN H /\ (n,w) IN H ==>
  v = w
Proof
  PairCases_on `rs` >> simp[current_rename_owner_def] >>
  metis_tac[current_name_owner_unique]
QED
