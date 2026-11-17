Theory o1LabelFlowMiddlePhiOwners
Ancestors
  o1MakeSsaVisitRetention o1MakeSsaOwnership o1MakeSsaVisitTrace makeSsaDefs
  makeSsaCurrentInduct makeSsaCurrentNonDegShape makeSsaCurrentNonDegCleanup
  cfgNormBase venomWf list pair alist pred_set

Theorem visit_phi_slot_owner:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_out)) /\
  block_slot q k j p x bbs /\ x IN V ==>
  ?n. block_slot q k j p n final /\ (n,x) IN H
Proof
  rpt strip_tac >>
  Cases_on `?e. MEM e events /\ e.sve_label = p /\ MEM q e.sve_succs`
  >- (pop_assum strip_assume_tac >>
      qexists_tac `latest_current_name e.sve_out x` >>
      conj_tac >- metis_tac[visit_slot_retained] >>
      `current_stack_owner V H (SND e.sve_out)` by metis_tac[] >>
      Cases_on `e.sve_out` >>
      gvs[latest_current_name_def] >>
      rename1 `current_stack_owner V H stacks` >>
      Cases_on `ALOOKUP stacks x` >> simp[]
      >- metis_tac[current_name_owner_identity] >>
      rename1 `ALOOKUP stacks x = SOME ns` >> Cases_on `ns` >> simp[]
      >- metis_tac[current_name_owner_identity] >>
      drule_all current_stack_owner_lookup >> simp[]) >>
  qexists_tac `x` >> conj_tac
  >- (irule visit_slot_unchanged >> metis_tac[]) >>
  metis_tac[current_name_owner_identity]
QED

Theorem rename_slot_origin:
  !insts s rs rt t outs k j p n.
  rename_current_block_insts s rs insts = (rt,t,outs) /\
  retained_slot k j p n outs ==> retained_slot k j p n insts
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> Cases_on `k`
  >- (simp[retained_slot_def] >> strip_tac >>
      gvs[rename_current_inst_def] >>
      rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]) >>
  simp[retained_slot_def] >> strip_tac >>
  first_x_assum (drule_at Any) >> gvs[retained_slot_def] >> metis_tac[]
QED

Theorem patch_slot_origin:
  retained_slot k j p n
    (MAP (\i. if i.inst_opcode <> PHI then i else
      i with inst_operands := update_current_phi_for_pred rs pred i.inst_operands) insts)
  ==> ?x. retained_slot k j p x insts
Proof
  rw[retained_slot_def] >>
  gvs[EL_MAP] >>
  Cases_on `(EL k insts).inst_opcode = PHI` >>
  gvs[o1MakeSsaReachingTheory.reaching_phi_pairs_update, EL_MAP] >>
  Cases_on `EL j (phi_pairs (EL k insts).inst_operands)` >> gvs[] >>
  metis_tac[]
QED

Theorem replace_rename_slot_origin:
  lookup_block lbl bbs = SOME bb /\
  rename_current_block_insts s rs bb.bb_instructions = (rt,t,outs) /\
  block_slot q k j p n (replace_block lbl (bb with bb_instructions := outs) bbs)
  ==> block_slot q k j p n bbs
Proof
  rpt strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  Cases_on `q = lbl` >> gvs[block_slot_def, retention_lookup_replace]
  >- (drule_all rename_slot_origin >> simp[]) >>
  metis_tac[]
QED

Theorem replace_patch_slot_origin:
  lookup_block lbl bbs = SOME bb /\
  block_slot q k j p n
    (replace_block lbl (bb with bb_instructions :=
      MAP (\i. if i.inst_opcode <> PHI then i else
        i with inst_operands := update_current_phi_for_pred rs pred i.inst_operands)
        bb.bb_instructions) bbs)
  ==> ?x. block_slot q k j p x bbs
Proof
  rpt strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecProofsTheory.lookup_block_label] >>
  Cases_on `q = lbl` >> gvs[block_slot_def, retention_lookup_replace]
  >- (drule patch_slot_origin >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem succ_slot_origin:
  !succs bbs q k j p n rs pred.
  block_slot q k j p n (update_current_succ_phis rs pred bbs succs) ==>
  ?x. block_slot q k j p x bbs
Proof
  Induct >> simp[update_current_succ_phis_def] >> rpt gen_tac
  >- metis_tac[] >>
  Cases_on `lookup_block h bbs` >> simp[]
  >- (fs[update_current_succ_phis_def] >> metis_tac[]) >>
  strip_tac >> fs[update_current_succ_phis_def] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[replace_patch_slot_origin]
QED

Theorem visit_slot_origin:
  (!tree path s rs bbs sm ct t final events q k j p n.
    visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
    block_slot q k j p n final ==> ?x. block_slot q k j p x bbs) /\
  (!trees path s ctrs stacks bbs sm ct t final events q k j p n.
    visit_children path s ctrs stacks bbs sm trees = ((ct,t,final),events) /\
    block_slot q k j p n final ==> ?x. block_slot q k j p x bbs)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[]
      >- metis_tac[] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      drule succ_slot_origin >> strip_tac >>
      metis_tac[replace_rename_slot_origin])
  >- (simp[visit_blocks_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem block_slot_functional:
  block_slot q k j p n bbs /\ block_slot q k j p m bbs ==> n = m
Proof
  simp[block_slot_def, retained_slot_def] >> metis_tac[PAIR_EQ, optionTheory.SOME_11]
QED

Theorem visit_phi_slot_owner_origin:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_out)) /\
  (!q k j p x. block_slot q k j p x bbs ==> x IN V) /\
  block_slot q k j p n final ==>
  ?x. block_slot q k j p x bbs /\ (n,x) IN H
Proof
  rpt strip_tac >> drule_all (cj 1 visit_slot_origin) >> strip_tac >>
  `x IN V` by metis_tac[] >>
  drule_all visit_phi_slot_owner >> strip_tac >>
  `n' = n` by metis_tac[block_slot_functional] >> metis_tac[]
QED

Theorem visit_phi_slot_exclusion:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_out)) /\
  (!q k j p x. block_slot q k j p x bbs ==> x IN V) /\
  (!q k j p. ~block_slot q k j p x bbs) /\ (n,x) IN H ==>
  !q k j p. ~block_slot q k j p n final
Proof
  rpt strip_tac >> drule_all visit_phi_slot_owner_origin >> strip_tac >>
  metis_tac[current_name_owner_unique]
QED

Theorem visit_phi_format:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  EVERY current_nondeg_block_shape bbs /\ lookup_block q final = SOME bb /\
  MEM i bb.bb_instructions /\ i.inst_opcode = PHI ==>
  phi_well_formed i.inst_operands
Proof
  rpt strip_tac >>
  `rename_current_blocks s rs bbs sm tree = (ct,t,final)` by
    metis_tac[visit_erasure, FST] >>
  drule_all (cj 1 current_nondeg_rename_shape) >>
  drule livenessTransferProofsTheory.lookup_block_mem >>
  simp[EVERY_MEM, current_nondeg_block_shape_def] >> metis_tac[]
QED

Theorem block_phi_var_slot:
  lookup_block q bbs = SOME bb /\ MEM i bb.bb_instructions /\
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\
  MEM (Var n) i.inst_operands ==>
  ?k j p. block_slot q k j p n bbs
Proof
  rpt strip_tac >> drule_all phi_well_formed_var_pair >> strip_tac >>
  gvs[MEM_EL] >>
  simp[block_slot_def, retained_slot_def] >> metis_tac[]
QED

Theorem block_slot_operand:
  block_slot q k j p x bbs ==>
  ?bb i. lookup_block q bbs = SOME bb /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Var x) i.inst_operands
Proof
  simp[block_slot_def, retained_slot_def] >> rpt strip_tac >>
  `MEM (p,x) (phi_pairs (EL k bb.bb_instructions).inst_operands)` by
    metis_tac[MEM_EL] >>
  drule phi_pairs_mem_var >> strip_tac >> metis_tac[MEM_EL]
QED

Theorem visit_phi_operand_exclusion:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_out)) /\
  EVERY current_nondeg_block_shape bbs /\
  (!q bb i v. lookup_block q bbs = SOME bb /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!q bb i. lookup_block q bbs = SOME bb /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==> ~MEM (Var x) i.inst_operands) /\ (n,x) IN H ==>
  !q bb i. lookup_block q final = SOME bb /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==> ~MEM (Var n) i.inst_operands
Proof
  rpt strip_tac >>
  `phi_well_formed i.inst_operands` by metis_tac[visit_phi_format] >>
  drule_all block_phi_var_slot >> strip_tac >>
  `!q k j p v. block_slot q k j p v bbs ==> v IN V` by
    metis_tac[block_slot_operand] >>
  drule_all visit_phi_slot_owner_origin >> strip_tac >>
  metis_tac[current_name_owner_unique, block_slot_operand]
QED

(* The prepared PHI format includes leading-PHI shape; lookup-based
   boundaries above need no distinct-label assumption. This member-based
   consumer exposes the uniqueness premise required for lookup coverage. *)
Theorem visit_phi_member_exclusion:
  visit_blocks path s rs bbs sm tree = ((ct,t,final),events) /\
  ALL_DISTINCT (dom_tree_postorder tree) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  (!l ss. ALOOKUP sm l = SOME ss ==> ALL_DISTINCT ss) /\
  current_name_owner V H u /\
  (!e. MEM e events ==> current_stack_owner V H (SND e.sve_out)) /\
  EVERY current_nondeg_block_shape bbs /\
  (!bb i v. MEM bb bbs /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  (!bb i. MEM bb bbs /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==> ~MEM (Var x) i.inst_operands) /\ (n,x) IN H ==>
  !bb i. MEM bb final /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==> ~MEM (Var n) i.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  `rename_current_blocks s rs bbs sm tree = (ct,t,final)` by
    metis_tac[visit_erasure, FST] >>
  drule (cj 1 makeSsaCurrentPropsTheory.rename_current_blocks_labels) >>
  strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) final)` by metis_tac[] >>
  `!q bb i v. lookup_block q bbs = SOME bb /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI /\ MEM (Var v) i.inst_operands ==> v IN V` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `!q bb i. lookup_block q bbs = SOME bb /\ MEM i bb.bb_instructions /\
    i.inst_opcode = PHI ==> ~MEM (Var x) i.inst_operands` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  drule visit_phi_operand_exclusion >> simp[] >>
  disch_then (qspecl_then [`x`,`u`,`n`,`V`,`H`] mp_tac) >> simp[] >>
  metis_tac[venomExecProofsTheory.MEM_lookup_block]
QED
