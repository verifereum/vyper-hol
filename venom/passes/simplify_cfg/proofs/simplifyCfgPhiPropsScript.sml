(* PHI-free preservation boundaries for SimplifyCFG. *)
Theory simplifyCfgPhiProps
Ancestors
  simplifyCfgDefs simplifyCfgLabelProps cfgTransform venomInst list rich_list

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

Theorem lookup_block_no_phi[local]:
  EVERY no_phis bbs /\ lookup_block lbl bbs = SOME bb ==> no_phis bb
Proof
  metis_tac[lookup_block_member_label, EVERY_MEM]
QED

Theorem try_bypass_no_phi[local]:
  !succs fn lm bb fn' lm' success.
    EVERY no_phis fn.fn_blocks /\ no_phis bb /\
    try_bypass fn lm bb succs = (fn',lm',success) ==>
    EVERY no_phis fn'.fn_blocks
Proof
  Induct >- simp[try_bypass_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `try_bypass _ _ _ _ = _` mp_tac >>
  simp[Once try_bypass_def] >>
  Cases_on `lookup_block h fn.fn_blocks` >> simp[]
  >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
  rename1 `lookup_block h fn.fn_blocks = SOME next` >>
  Cases_on `can_bypass_jump fn bb next` >> simp[]
  >- (Cases_on `lookup_block (HD (bb_succs next)) fn.fn_blocks` >> simp[]
      >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
      rename1 `lookup_block _ _ = SOME target` >>
      Cases_on `phi_values_agree bb.bb_label next.bb_label target.bb_instructions` >> simp[]
      >- (Cases_on `do_merge_jump fn bb next lm` >> simp[]
          >- (strip_tac >> first_x_assum drule_all >> simp[]) >>
          rename1 `do_merge_jump _ _ _ _ = SOME result` >>
          PairCases_on `result` >> simp[] >> strip_tac >> gvs[] >>
          drule_all do_merge_jump_no_phi >> simp[]) >>
      strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem chain_merge_no_phi[local]:
  EVERY no_phis fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block next_lbl fn.fn_blocks = SOME next ==>
  EVERY no_phis
    (update_succ_phi_labels next_lbl lbl
      (replace_block lbl (merge_blocks bb next)
        (remove_block next_lbl fn.fn_blocks))
      (bb_succs (merge_blocks bb next)))
Proof
  strip_tac >> irule update_succ_phi_labels_no_phi >>
  irule replace_block_no_phi >>
  simp[remove_block_no_phi] >> irule merge_blocks_no_phi >>
  metis_tac[lookup_block_no_phi]
QED

Theorem collapse_no_phi_joint[local]:
  (!fn lm vis lbl.
    collapse_dfs_result
      (\result. EVERY no_phis fn.fn_blocks ==>
                EVERY no_phis (FST result).fn_blocks) fn lm vis lbl) /\
  (!fn lm vis succs.
    collapse_dfs_succs_result
      (\result. EVERY no_phis fn.fn_blocks ==>
                EVERY no_phis (FST result).fn_blocks) fn lm vis succs)
Proof
  ho_match_mp_tac collapse_dfs_ind >> rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume collapse_no_phi_joint[nil]:
  simp[collapse_dfs_succs_result_def, collapse_dfs_def]
QED

Resume collapse_no_phi_joint[succs]:
  rpt strip_tac >>
  simp[collapse_dfs_succs_result_def, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs fn lm vis lbl` >> PairCases_on `r` >>
  gvs[collapse_dfs_result_def, collapse_dfs_succs_result_def]
QED

Resume collapse_no_phi_joint[dfs]:
  rpt strip_tac >>
  simp[NoAsms, collapse_dfs_result_def, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb`
  >- (Cases_on `MEM lbl vis` >>
      gvs[try_bypass_def, collapse_dfs_succs_result_def]) >>
  Cases_on `t`
  >- suspend "single"
  >> suspend "multiple"
QED

Resume collapse_no_phi_joint[single]:
  gvs[] >>
  Cases_on `lookup_block h fn.fn_blocks` >- (Cases_on `MEM lbl vis` >> simp[]) >>
  rename1 `lookup_block h fn.fn_blocks = SOME next` >>
  Cases_on `can_merge_blocks fn bb next` >>
  gvs[collapse_dfs_result_def]
  >- (strip_tac >> first_x_assum irule >>
      irule chain_merge_no_phi >> metis_tac[]) >>
  Cases_on `MEM lbl vis` >> simp[]
QED
Resume collapse_no_phi_joint[multiple]:
  gvs[] >>
  Cases_on `try_bypass fn lm bb (h::h'::t')` >>
  PairCases_on `r` >> gvs[] >>
  strip_tac >>
  `EVERY no_phis q.fn_blocks` by
    (irule try_bypass_no_phi >> metis_tac[lookup_block_no_phi]) >>
  Cases_on `r1` >> Cases_on `MEM lbl vis` >>
  gvs[collapse_dfs_result_def, collapse_dfs_succs_result_def]
QED

Finalise collapse_no_phi_joint

Theorem collapse_dfs_no_phi[local]:
  EVERY no_phis fn.fn_blocks ==>
  EVERY no_phis (FST (collapse_dfs fn lm vis lbl)).fn_blocks
Proof
  mp_tac (CONJUNCT1 collapse_no_phi_joint) >>
  simp[collapse_dfs_result_def]
QED

Theorem remove_unreachable_blocks_no_phi[local]:
  EVERY no_phis fn.fn_blocks ==>
  EVERY no_phis (remove_unreachable_blocks fn).fn_blocks
Proof
  Cases_on `fn_entry_label fn` >>
  simp[remove_unreachable_blocks_def, EVERY_MEM, MEM_FILTER]
QED

Theorem simplify_cfg_round_no_phi[local]:
  EVERY no_phis fn.fn_blocks ==>
  EVERY no_phis (FST (simplify_cfg_round_with_labels fn)).fn_blocks
Proof
  strip_tac >> Cases_on `fn_entry_label fn`
  >- simp[simplify_cfg_round_with_labels_def] >>
  rename1 `fn_entry_label fn = SOME entry` >>
  `EVERY no_phis (fix_all_phis (remove_unreachable_blocks fn)).fn_blocks` by
    simp[fix_all_phis_no_phi, remove_unreachable_blocks_no_phi] >>
  drule collapse_dfs_no_phi >>
  disch_then (qspecl_then [`[]`, `[]`, `entry`] mp_tac) >>
  Cases_on `collapse_dfs (fix_all_phis (remove_unreachable_blocks fn)) [] [] entry` >>
  PairCases_on `r` >> simp[] >> strip_tac >>
  simp[simplify_cfg_round_with_labels_def] >>
  irule fix_all_phis_no_phi >> irule remove_unreachable_blocks_no_phi >>
  IF_CASES_TAC >> simp[subst_block_labels_fn_no_phi]
QED

Theorem simplify_cfg_iter_no_phi[local]:
  !n fn. EVERY no_phis fn.fn_blocks ==>
    EVERY no_phis (FST (simplify_cfg_iter_with_labels n fn)).fn_blocks
Proof
  Induct >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  rename1 `simplify_cfg_round_with_labels fn = (next,lm)` >>
  `EVERY no_phis next.fn_blocks` by
    (drule simplify_cfg_round_no_phi >> simp[]) >>
  simp[Once simplify_cfg_iter_with_labels_def] >>
  IF_CASES_TAC >- simp[] >>
  first_x_assum drule >>
  Cases_on `simplify_cfg_iter_with_labels n next` >> simp[]
QED

Theorem simplify_cfg_fn_no_phi:
  EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts fn) ==>
  EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts (simplify_cfg_fn fn))
Proof
  `!bbs. EVERY (\inst. inst.inst_opcode <> PHI) (fn_insts_blocks bbs) =
          EVERY no_phis bbs` by
    (Induct >> simp[fn_insts_blocks_def, no_phis_def]) >>
  simp[fn_insts_def, simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def] >>
  metis_tac[simplify_cfg_iter_no_phi]
QED
