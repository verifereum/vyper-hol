(* PHI-free preservation boundaries for SimplifyCFG. *)
Theory simplifyCfgPhiProps
Ancestors
  simplifyCfgDefs cfgTransform venomInst list rich_list

Theorem fix_phi_inst_no_phi:
  inst.inst_opcode <> PHI ==>
  (fix_phi_inst actual_preds inst).inst_opcode <> PHI
Proof
  simp[fix_phi_inst_def]
QED

Theorem update_phi_bypass_no_phi:
  inst.inst_opcode <> PHI ==>
  (update_phi_bypass a b inst).inst_opcode <> PHI
Proof
  simp[update_phi_bypass_def]
QED

Theorem canon_jnz_inst_no_phi:
  inst.inst_opcode <> PHI ==>
  (canon_jnz_inst inst).inst_opcode <> PHI
Proof
  simp[canon_jnz_inst_def] >> rpt CASE_TAC >> simp[]
QED

Theorem subst_label_inst_no_phi:
  inst.inst_opcode <> PHI ==>
  (subst_label_inst a b inst).inst_opcode <> PHI
Proof
  simp[subst_label_inst_def]
QED

Theorem subst_block_labels_inst_no_phi:
  inst.inst_opcode <> PHI ==>
  (subst_block_labels_inst lm inst).inst_opcode <> PHI
Proof
  Cases_on `inst.inst_opcode` >>
  simp[subst_block_labels_inst_def, subst_label_map_inst_def,
       is_block_label_opcode_def, is_terminator_def]
QED

Theorem fix_phis_in_block_no_phi:
  no_phis bb ==> no_phis (fix_phis_in_block actual_preds bb)
Proof
  simp[no_phis_def, fix_phis_in_block_def, EVERY_APPEND,
       EVERY_FILTER, EVERY_MAP, EVERY_MEM, MEM_FILTER, MEM_MAP] >>
  metis_tac[fix_phi_inst_no_phi]
QED

Theorem fix_all_phis_no_phi:
  EVERY no_phis fn.fn_blocks ==> EVERY no_phis (fix_all_phis fn).fn_blocks
Proof
  simp[fix_all_phis_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  metis_tac[fix_phis_in_block_no_phi]
QED

Theorem subst_block_labels_block_no_phi:
  no_phis bb ==> no_phis (subst_block_labels_block lm bb)
Proof
  simp[no_phis_def, subst_block_labels_block_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  metis_tac[subst_block_labels_inst_no_phi]
QED

Theorem subst_block_labels_fn_no_phi:
  EVERY no_phis fn.fn_blocks ==>
  EVERY no_phis (subst_block_labels_fn lm fn).fn_blocks
Proof
  simp[subst_block_labels_fn_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  metis_tac[subst_block_labels_block_no_phi]
QED

Theorem remove_block_no_phi:
  EVERY no_phis bbs ==> EVERY no_phis (remove_block lbl bbs)
Proof
  simp[remove_block_def, EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem replace_block_no_phi:
  EVERY no_phis bbs /\ no_phis bb ==>
  EVERY no_phis (replace_block lbl bb bbs)
Proof
  simp[replace_block_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[]
QED

Theorem no_phi_front[local]:
  !xs. EVERY P xs ==> EVERY P (FRONT xs)
Proof
  Induct >> simp[] >> Cases_on `xs` >> simp[]
QED

Theorem merge_blocks_no_phi:
  no_phis a /\ no_phis b ==> no_phis (merge_blocks a b)
Proof
  simp[no_phis_def, merge_blocks_def, EVERY_APPEND] >>
  metis_tac[no_phi_front]
QED

Theorem update_succ_phi_labels_no_phi:
  !succs bbs. EVERY no_phis bbs ==>
    EVERY no_phis (update_succ_phi_labels old new bbs succs)
Proof
  simp[update_succ_phi_labels_def] >>
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  Cases_on `lookup_block h bbs` >- simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >> simp[] >>
  irule replace_block_no_phi >> simp[] >>
  drule lookup_block_member_label >> strip_tac >>
  `no_phis bb` by metis_tac[EVERY_MEM] >>
  gvs[no_phis_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem bypass_source_inst_no_phi[local]:
  inst.inst_opcode <> PHI ==>
  (if ~is_terminator inst.inst_opcode then inst
   else canon_jnz_inst (subst_label_inst old new inst)).inst_opcode <> PHI
Proof
  strip_tac >> IF_CASES_TAC >> simp[] >>
  irule canon_jnz_inst_no_phi >> simp[subst_label_inst_no_phi]
QED

Theorem do_merge_jump_no_phi:
  EVERY no_phis fn.fn_blocks /\ no_phis a /\
  do_merge_jump fn a b lm = SOME (fn',lm') ==>
  EVERY no_phis fn'.fn_blocks
Proof
  simp[do_merge_jump_def] >>
  Cases_on `bb_succs b` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block h fn.fn_blocks = SOME target` >>
  rpt strip_tac >> gvs[] >>
  `no_phis target` by
    (drule lookup_block_member_label >> strip_tac >>
     gvs[EVERY_MEM]) >>
  irule replace_block_no_phi >> reverse conj_tac
  >- (irule replace_block_no_phi >>
      simp[remove_block_no_phi] >>
      gvs[no_phis_def, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
      metis_tac[update_phi_bypass_no_phi]) >>
  Cases_on `h = a.bb_label` >>
  gvs[no_phis_def, EVERY_MEM, MEM_MAP] >>
  metis_tac[update_phi_bypass_no_phi, bypass_source_inst_no_phi]
QED
