Theory o1ContractSimplifyCfgSrcStatic
Ancestors
  simplifyCfgDefs simplifyCfgPhiProps simplifyCfgStruct
  simplifyCfgGeneratedSubst cfgTransform venomInst
  list rich_list sorting pred_set venomWf venomExecProps passSimulationProofs
  ptrDiscipline memLocDefs pointerConfinedDefs simplifyCfgShape unitShapeDefs
  stackPlanTypes cfgTransformProps simplifyCfgInvariant simplifyCfgRoundSemantics
  simplifyCfgStaticInterface simplifyCfgLabelProps simplifyCfgCollapseSemantics
  simplifyCfgLocalShape ctxLookupAgreeHelpers pointerConfinedProps
  simplifyCfgCorrectness cfgWf o1PassContract

Theorem fix_phis_in_block_no_phi_identity:
  no_phis bb ==> fix_phis_in_block actual_preds bb = bb
Proof
  simp[no_phis_def, EVERY_EL] >> strip_tac >>
  `MAP (fix_phi_inst actual_preds) bb.bb_instructions = bb.bb_instructions` by
    (irule LIST_EQ >> simp[EL_MAP, fix_phi_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    simp[EVERY_EL] >>
  simp[fix_phis_in_block_def] >>
  `FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions = []` by
    (simp[FILTER_EQ_NIL] >> fs[no_phis_def, EVERY_MEM]) >>
  `FILTER (\i. i.inst_opcode <> PHI) bb.bb_instructions = bb.bb_instructions` by
    (simp[FILTER_EQ_ID] >> fs[no_phis_def]) >>
  simp[]
QED

Theorem fix_all_phis_no_phi_identity:
  EVERY no_phis f.fn_blocks ==> fix_all_phis f = f
Proof
  strip_tac >>
  `MAP (\bb. fix_phis_in_block (pred_labels f bb.bb_label) bb) f.fn_blocks =
   f.fn_blocks` by
    (irule LIST_EQ >> simp[EL_MAP] >>
     metis_tac[EVERY_EL, fix_phis_in_block_no_phi_identity]) >>
  simp[fix_all_phis_def]
QED

Theorem update_phi_bypass_no_phi_identity:
  i.inst_opcode <> PHI ==> update_phi_bypass a b i = i
Proof
  simp[update_phi_bypass_def]
QED

Theorem bypass_data_inst_identity:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> PHI ==>
  update_phi_bypass a b
    (if ~is_terminator i.inst_opcode then i
     else canon_jnz_inst (subst_label_inst b c i)) = i
Proof
  simp[update_phi_bypass_no_phi_identity]
QED

Theorem bb_data_insts_front:
  bb_well_formed bb ==>
  FILTER (\i. ~is_terminator i.inst_opcode) bb.bb_instructions =
  FRONT bb.bb_instructions
Proof
  strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `FILTER (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) =
   FRONT bb.bb_instructions` by
    (simp[FILTER_EQ_ID] >> irule bb_well_formed_front_nonterminators >> simp[]) >>
  qpat_assum `bb.bb_instructions <> []`
    (mp_tac o MATCH_MP APPEND_FRONT_LAST) >>
  disch_then (fn th => GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) empty_rewrites [GSYM th]) >>
  simp[FILTER_APPEND]
QED

Theorem merge_blocks_data_insts:
  bb_well_formed a ==>
  FILTER (\i. ~is_terminator i.inst_opcode) (merge_blocks a b).bb_instructions =
  FILTER (\i. ~is_terminator i.inst_opcode) a.bb_instructions ++
  FILTER (\i. ~is_terminator i.inst_opcode) b.bb_instructions
Proof
  strip_tac >> simp[merge_blocks_def, FILTER_APPEND, bb_data_insts_front] >>
  simp[FILTER_EQ_ID, bb_well_formed_front_nonterminators]
QED

Theorem blocks_data_insts_perm:
  PERM xs ys ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (FLAT (MAP (\bb. bb.bb_instructions) xs))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (FLAT (MAP (\bb. bb.bb_instructions) ys)))
Proof
  strip_tac >> irule PERM_LIST_TO_SET >> irule PERM_FILTER >>
  irule PERM_FLAT >> irule PERM_MAP >> simp[]
QED

Theorem chain_merge_data_insts:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM a bbs /\ MEM b bbs /\
  a.bb_label <> b.bb_label /\ bb_well_formed a ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (FLAT (MAP (\bb. bb.bb_instructions)
      (replace_block a.bb_label (merge_blocks a b) (remove_block b.bb_label bbs))))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (FLAT (MAP (\bb. bb.bb_instructions) bbs)))
Proof
  strip_tac >> drule_all blocks_extract_pair_perm >> strip_tac >>
  drule_all chain_merge_base_perm >> strip_tac >>
  qpat_x_assum `PERM (_::_::_) _`
    (mp_tac o MATCH_MP blocks_data_insts_perm) >> disch_tac >>
  drule blocks_data_insts_perm >> disch_tac >>
  fs[FILTER_APPEND, merge_blocks_data_insts, UNION_ASSOC]
QED

Theorem update_succ_phi_labels_no_phi_identity:
  !succs bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  EVERY no_phis bbs ==>
  update_succ_phi_labels old new bbs succs = bbs
Proof
  simp[update_succ_phi_labels_def] >> Induct >> simp[] >> rpt strip_tac >>
  Cases_on `lookup_block h bbs` >- simp[] >>
  rename1 `lookup_block h bbs = SOME bb` >>
  drule lookup_block_member_label >> strip_tac >>
  `no_phis bb` by metis_tac[EVERY_MEM] >>
  `MAP (\inst. if inst.inst_opcode <> PHI then inst
       else subst_label_inst old new inst) bb.bb_instructions =
   bb.bb_instructions` by
    (irule LIST_EQ >> simp[EL_MAP] >>
     fs[no_phis_def, EVERY_EL]) >>
  simp[] >>
  `replace_block h bb bbs = bbs` by
    (simp[replace_block_def] >>
     GEN_REWRITE_TAC RAND_CONV empty_rewrites [GSYM MAP_ID] >>
     irule MAP_CONG >> simp[] >> rpt strip_tac >>
     IF_CASES_TAC >> simp[] >>
     `lookup_block h bbs = SOME x` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  simp[]
QED

Theorem bypass_source_data_insts:
  !xs. FILTER (\i. ~is_terminator i.inst_opcode)
    (MAP (\i. if ~is_terminator i.inst_opcode then i
              else canon_jnz_inst (subst_label_inst b c i)) xs) =
  FILTER (\i. ~is_terminator i.inst_opcode) xs
Proof
  Induct >> simp[] >> gen_tac >>
  Cases_on `is_terminator h.inst_opcode` >>
  simp[canon_jnz_inst_shape, subst_label_inst_shape]
QED

Theorem update_phi_bypass_no_phi_list:
  EVERY (\i. i.inst_opcode <> PHI) xs ==>
  MAP (update_phi_bypass a b) xs = xs
Proof
  strip_tac >> irule LIST_EQ >> simp[EL_MAP] >>
  fs[EVERY_EL, update_phi_bypass_def]
QED

Theorem do_merge_jump_data_projection:
  ALL_DISTINCT (fn_labels f) /\ EVERY no_phis f.fn_blocks /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  do_merge_jump f a b lm = SOME (f',lm') ==>
  MAP (\bb. FILTER (\i. ~is_terminator i.inst_opcode) bb.bb_instructions)
    f'.fn_blocks =
  MAP (\bb. FILTER (\i. ~is_terminator i.inst_opcode) bb.bb_instructions)
    (remove_block b.bb_label f.fn_blocks)
Proof
  strip_tac >>
  `no_phis a` by
    (drule lookup_block_member_label >> fs[EVERY_MEM]) >>
  fs[do_merge_jump_def, AllCaseEqs()] >>
  drule lookup_block_member_label >> strip_tac >> gvs[] >>
  `no_phis target` by metis_tac[EVERY_MEM] >>
  `MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions =
   target.bb_instructions` by
    (irule update_phi_bypass_no_phi_list >> fs[no_phis_def]) >>
  simp[replace_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[remove_block_def, MEM_FILTER] >>
  qx_gen_tac `bb` >> strip_tac >>
  `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  Cases_on `bb.bb_label = target.bb_label` >>
  Cases_on `bb.bb_label = a.bb_label` >> gvs[] >>
  simp[bypass_source_data_insts] >>
  `MAP (\inst. update_phi_bypass a.bb_label b.bb_label
     (if ~is_terminator inst.inst_opcode then inst
      else canon_jnz_inst (subst_label_inst b.bb_label a.bb_label inst)))
     a.bb_instructions =
   MAP (\inst. if ~is_terminator inst.inst_opcode then inst
      else canon_jnz_inst (subst_label_inst b.bb_label a.bb_label inst))
     a.bb_instructions` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     irule update_phi_bypass_no_phi_identity >>
     irule bypass_source_inst_no_phi >> fs[no_phis_def, EVERY_MEM]) >>
  simp[bypass_source_data_insts]
QED

Theorem remove_control_block_data_insts:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\ MEM b bbs /\
  FILTER (\i. ~is_terminator i.inst_opcode) b.bb_instructions = [] ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (FLAT (MAP (\bb. bb.bb_instructions) (remove_block b.bb_label bbs)))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (FLAT (MAP (\bb. bb.bb_instructions) bbs)))
Proof
  strip_tac >> drule_all blocks_extract_perm >>
  disch_then (mp_tac o MATCH_MP blocks_data_insts_perm) >>
  simp[FILTER_APPEND]
QED

Theorem do_merge_jump_data_insts:
  ALL_DISTINCT (fn_labels f) /\ EVERY no_phis f.fn_blocks /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\ MEM b f.fn_blocks /\
  FILTER (\i. ~is_terminator i.inst_opcode) b.bb_instructions = [] /\
  do_merge_jump f a b lm = SOME (f',lm') ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f')) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f))
Proof
  strip_tac >> drule_all do_merge_jump_data_projection >> strip_tac >>
  fs[fn_labels_def] >> drule_all remove_control_block_data_insts >>
  simp[fn_insts_def, fn_insts_blocks_flat, FILTER_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem bypass_terminator_ptr_use_ok:
  is_terminator inst.inst_opcode /\ inst_wf inst /\ label_positions_ok inst /\
  ptr_use_ok P pv inst ==>
  ptr_use_ok P pv (canon_jnz_inst (subst_label_inst a b inst))
Proof
  strip_tac >> Cases_on `inst.inst_opcode = JNZ`
  >- (gvs[inst_wf_def, label_positions_ok_def] >>
      simp[subst_label_inst_def, subst_label_op_def] >>
      Cases_on `c` >>
      gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def, is_label_operand_def,
          subst_label_op_def, canon_jnz_inst_def] >>
      rpt IF_CASES_TAC >>
      gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def]) >>
  Cases_on `inst.inst_opcode = JMP`
  >- (gvs[inst_wf_def] >>
      simp[subst_label_inst_def, subst_label_op_def, canon_jnz_inst_def,
           ptr_use_ok_def] >> IF_CASES_TAC >> simp[]) >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, label_positions_ok_def]) >>
  `subst_label_inst a b inst = inst` by
    (irule subst_label_inst_no_label_operands >> simp[]) >>
  `canon_jnz_inst inst = inst` by metis_tac[canon_jnz_inst_changed] >>
  simp[]
QED

Theorem singleton_block_data_insts:
  bb_well_formed bb /\ LENGTH bb.bb_instructions = 1 ==>
  FILTER (\i. ~is_terminator i.inst_opcode) bb.bb_instructions = []
Proof
  strip_tac >> simp[bb_data_insts_front] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem legal_bypass_data_insts:
  wf_function f /\ EVERY no_phis f.fn_blocks /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\ do_merge_jump f a b lm = SOME (f',lm') ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f')) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f))
Proof
  strip_tac >>
  `MEM b f.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `FILTER (\i. ~is_terminator i.inst_opcode) b.bb_instructions = []` by
    (irule singleton_block_data_insts >>
     fs[wf_function_def, EVERY_MEM, can_bypass_jump_def]) >>
  `ALL_DISTINCT (fn_labels f)` by fs[wf_function_def] >>
  drule_all do_merge_jump_data_insts >> simp[]
QED

Theorem do_merge_jump_signature:
  do_merge_jump f a b lm = SOME (g,lm') ==>
  g with fn_blocks := f.fn_blocks = f
Proof
  simp[do_merge_jump_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem legal_chain_merge_data_insts:
  wf_function f /\ EVERY no_phis f.fn_blocks /\
  MEM a f.fn_blocks /\ MEM b f.fn_blocks /\ can_merge_blocks f a b ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (f with fn_blocks :=
      update_succ_phi_labels b.bb_label a.bb_label
        (replace_block a.bb_label (merge_blocks a b)
          (remove_block b.bb_label f.fn_blocks)) succs))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f))
Proof
  strip_tac >>
  `no_phis a /\ no_phis b /\ bb_well_formed a /\
   ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks) /\
   a.bb_label <> b.bb_label` by
    fs[wf_function_def, fn_labels_def, EVERY_MEM, can_merge_blocks_def] >>
  `EVERY no_phis (replace_block a.bb_label (merge_blocks a b)
     (remove_block b.bb_label f.fn_blocks))` by
    (irule replace_block_no_phi >>
     simp[remove_block_no_phi, merge_blocks_no_phi]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
     (replace_block a.bb_label (merge_blocks a b)
       (remove_block b.bb_label f.fn_blocks)))` by
    simp[fn_labels_replace_block, ALL_DISTINCT_remove_block, merge_blocks_def] >>
  simp[update_succ_phi_labels_no_phi_identity, fn_insts_def, fn_insts_blocks_flat] >>
  irule chain_merge_data_insts >> simp[]
QED

Theorem collapse_dfs_data_insts:
  wf_function f /\ EVERY no_phis f.fn_blocks ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (FST (collapse_dfs f lm vis lbl)))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `set _ = data` >>
  `!g lm vis lbl. wf_function g /\ EVERY no_phis g.fn_blocks /\
    set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) = data ==>
    wf_function (FST (collapse_dfs g lm vis lbl)) /\
    EVERY no_phis (FST (collapse_dfs g lm vis lbl)).fn_blocks /\
    set (FILTER (\i. ~is_terminator i.inst_opcode)
      (fn_insts (FST (collapse_dfs g lm vis lbl)))) = data` by
    (ho_match_mp_tac collapse_dfs_preserves_predicate >> conj_tac
     >- (rpt strip_tac
         >- metis_tac[do_merge_jump_wf]
         >- (irule do_merge_jump_no_phi >>
             metis_tac[lookup_block_member_label, EVERY_MEM]) >>
         metis_tac[legal_bypass_data_insts]) >>
     rpt gen_tac >> strip_tac >>
     `a.bb_label = lbl /\ b.bb_label = next` by
       metis_tac[lookup_block_member_label] >> gvs[] >>
     conj_tac >- metis_tac[chain_merge_wf] >>
     conj_tac >- metis_tac[chain_merge_no_phi] >>
     metis_tac[legal_chain_merge_data_insts, lookup_block_member_label]) >>
  first_x_assum (qspecl_then [`f`, `lm`, `vis`, `lbl`] mp_tac) >>
  simp[Abbr `data`]
QED

Theorem remove_unreachable_blocks_normalized_identity:
  scfg_normalized f ==> remove_unreachable_blocks f = f
Proof
  strip_tac >>
  `FILTER (\bb. reachable f bb.bb_label) f.fn_blocks = f.fn_blocks` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >>
     fs[scfg_normalized_def, scfg_static_def, wf_function_def] >>
     metis_tac[fn_reachable_iff_reachable]) >>
  simp[remove_unreachable_blocks_def] >> Cases_on `fn_entry_label f` >> simp[]
QED

Theorem simplify_cfg_round_data_insts:
  scfg_static f /\ EVERY no_phis f.fn_blocks ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (FST (simplify_cfg_round_with_labels f)))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (remove_unreachable_blocks f)))
Proof
  strip_tac >> Cases_on `fn_entry_label f`
  >- simp[simplify_cfg_round_with_labels_def, remove_unreachable_blocks_def] >>
  qabbrev_tac `clean = remove_unreachable_blocks f` >>
  `EVERY no_phis clean.fn_blocks` by
    (simp[Abbr `clean`, remove_unreachable_blocks_def] >>
     fs[EVERY_MEM, MEM_FILTER]) >>
  `fix_all_phis clean = clean` by simp[fix_all_phis_no_phi_identity] >>
  `scfg_normalized clean` by
    metis_tac[scfg_normalized_cleanup] >>
  `wf_function clean` by
    metis_tac[scfg_normalized_static, scfg_static_wf] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts q)) =
   set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts clean))` by
    (drule_all collapse_dfs_data_insts >>
     disch_then (qspecl_then [`[]`, `[]`, `x`] mp_tac) >> simp[]) >>
  `scfg_normalized q` by metis_tac[scfg_collapse_normalized] >>
  `EVERY no_phis q.fn_blocks` by
    metis_tac[collapse_dfs_no_phi, pairTheory.FST] >>
  `subst_block_labels_fn r0 q = q` by
    (irule scfg_collapse_subst_identity >> simp[] >>
     qexistsl_tac [`clean`, `x`, `[]`, `r1`] >> simp[] >>
     fs[wf_function_def]) >>
  `remove_unreachable_blocks q = q` by
    simp[remove_unreachable_blocks_normalized_identity] >>
  Cases_on `r0 = []` >>
  simp[simplify_cfg_round_with_labels_def, GSYM (Abbr `clean`),
       fix_all_phis_no_phi_identity]
QED

Theorem simplify_cfg_iter_normalized_data_insts:
  !n f. scfg_normalized f /\ EVERY no_phis f.fn_blocks ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (FST (simplify_cfg_iter_with_labels n f)))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f))
Proof
  Induct >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >> Cases_on `simplify_cfg_round_with_labels f` >>
  `scfg_static f` by metis_tac[scfg_normalized_static] >>
  `scfg_normalized q` by
    metis_tac[scfg_round_contract, scfg_collapse_contract_def, pairTheory.FST] >>
  `EVERY no_phis q.fn_blocks` by
    metis_tac[simplify_cfg_round_no_phi, pairTheory.FST] >>
  `set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts q)) =
   set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f))` by
    (drule_all simplify_cfg_round_data_insts >>
     simp[remove_unreachable_blocks_normalized_identity]) >>
  Cases_on `q.fn_blocks = f.fn_blocks`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  simp[simplify_cfg_iter_with_labels_def] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED

Theorem simplify_cfg_iter_positive_data_insts:
  scfg_static f /\ EVERY no_phis f.fn_blocks ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (FST (simplify_cfg_iter_with_labels (SUC n) f)))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (remove_unreachable_blocks f)))
Proof
  strip_tac >> Cases_on `simplify_cfg_round_with_labels f` >>
  `scfg_normalized q` by
    metis_tac[scfg_round_contract, scfg_collapse_contract_def, pairTheory.FST] >>
  `EVERY no_phis q.fn_blocks` by
    metis_tac[simplify_cfg_round_no_phi, pairTheory.FST] >>
  `set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts q)) =
   set (FILTER (\i. ~is_terminator i.inst_opcode)
     (fn_insts (remove_unreachable_blocks f)))` by
    (drule_all simplify_cfg_round_data_insts >> simp[]) >>
  Cases_on `q.fn_blocks = f.fn_blocks`
  >- (gvs[simplify_cfg_iter_with_labels_def, fn_insts_def]) >>
  drule_all simplify_cfg_iter_normalized_data_insts >>
  disch_then (qspec_then `n` mp_tac) >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  simp[simplify_cfg_iter_with_labels_def]
QED

Theorem reachable_fn_no_phi_cleanup:
  wf_function f /\ EVERY no_phis f.fn_blocks ==>
  reachable_fn f = remove_unreachable_blocks f
Proof
  strip_tac >>
  `MAP (\bb. bb with bb_instructions :=
      MAP (reachable_inst f bb.bb_label) bb.bb_instructions)
    (FILTER (\bb. fn_reachable f bb.bb_label) f.fn_blocks) =
    FILTER (\bb. fn_reachable f bb.bb_label) f.fn_blocks` by
    (qmatch_goalsub_abbrev_tac `MAP _ blocks` >>
     irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     rename1 `n < LENGTH blocks` >>
     `MEM (EL n blocks) f.fn_blocks` by
       (gvs[Abbr `blocks`, MEM_FILTER] >> metis_tac[MEM_EL, MEM_FILTER]) >>
     `MAP (reachable_inst f (EL n blocks).bb_label) (EL n blocks).bb_instructions =
        (EL n blocks).bb_instructions` by
       (irule LIST_EQ >> simp[EL_MAP] >>
        fs[EVERY_MEM, no_phis_def, reachable_inst_def] >>
        metis_tac[MEM_EL]) >> simp[]) >>
  `ALL_DISTINCT (fn_labels f)` by fs[wf_function_def] >>
  `fn_entry_label f <> NONE` by
    (fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
     Cases_on `f.fn_blocks` >> gvs[]) >>
  simp[reachable_fn_def, remove_unreachable_blocks_def] >>
  Cases_on `fn_entry_label f` >> gvs[] >>
  ` (\bb. fn_reachable f bb.bb_label) = (\bb. reachable f bb.bb_label)` by
    simp[FUN_EQ_THM, fn_reachable_iff_reachable] >> simp[]
QED

Theorem simplify_cfg_fn_data_insts:
  scfg_static f /\ EVERY no_phis f.fn_blocks ==>
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (simplify_cfg_fn f))) =
  set (FILTER (\i. ~is_terminator i.inst_opcode)
    (fn_insts (reachable_fn f)))
Proof
  strip_tac >> `wf_function f` by metis_tac[scfg_static_wf] >>
  `LENGTH f.fn_blocks <> 0` by
    (fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
     Cases_on `f.fn_blocks` >> gvs[]) >>
  Cases_on `LENGTH f.fn_blocks` >> gvs[] >>
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def,
       reachable_fn_no_phi_cleanup] >>
  irule simplify_cfg_iter_positive_data_insts >> simp[]
QED

Theorem collapse_dfs_control_ptr_use_ok:
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i)) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i))
    (fn_insts (FST (collapse_dfs f lm vis lbl)))
Proof
  map_every qid_spec_tac [`lbl`, `vis`, `lm`, `f`] >>
  ho_match_mp_tac collapse_dfs_preserves_predicate >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule do_merge_jump_every >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> simp[update_phi_bypass_no_phi_identity]) >>
      rpt strip_tac
      >- metis_tac[subst_label_inst_no_phi, canon_jnz_inst_no_phi]
      >- metis_tac[bypass_terminator_wf]
      >- metis_tac[bypass_terminator_label_positions] >>
      metis_tac[bypass_terminator_ptr_use_ok]) >>
  rpt gen_tac >> strip_tac >> irule chain_merge_every >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem simplify_cfg_round_every_from_collapse:
  (!g lm vis lbl. EVERY Q (fn_insts g) ==>
    EVERY Q (fn_insts (FST (collapse_dfs g lm vis lbl)))) /\
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  EVERY Q (fn_insts (remove_unreachable_blocks f)) ==>
  EVERY Q (fn_insts (FST (simplify_cfg_round_with_labels f)))
Proof
  strip_tac >> Cases_on `fn_entry_label f`
  >- gvs[simplify_cfg_round_with_labels_def, remove_unreachable_blocks_def] >>
  qabbrev_tac `clean = remove_unreachable_blocks f` >>
  `EVERY no_phis clean.fn_blocks` by
    (simp[Abbr `clean`, remove_unreachable_blocks_def] >>
     fs[EVERY_MEM, MEM_FILTER]) >>
  `fix_all_phis clean = clean` by simp[fix_all_phis_no_phi_identity] >>
  `scfg_normalized clean` by metis_tac[scfg_normalized_cleanup] >>
  Cases_on `collapse_dfs clean [] [] x` >> PairCases_on `r` >>
  `EVERY Q (fn_insts q)` by metis_tac[pairTheory.FST] >>
  `scfg_normalized q` by metis_tac[scfg_collapse_normalized] >>
  `EVERY no_phis q.fn_blocks` by
    metis_tac[collapse_dfs_no_phi, pairTheory.FST] >>
  `subst_block_labels_fn r0 q = q` by
    (irule scfg_collapse_subst_identity >> simp[] >>
     qexistsl_tac [`clean`, `x`, `[]`, `r1`] >> simp[] >>
     fs[scfg_normalized_def, scfg_static_def, wf_function_def]) >>
  `remove_unreachable_blocks q = q` by
    simp[remove_unreachable_blocks_normalized_identity] >>
  Cases_on `r0 = []` >>
  simp[simplify_cfg_round_with_labels_def, GSYM (Abbr `clean`),
       fix_all_phis_no_phi_identity]
QED

Theorem simplify_cfg_round_control_ptr_use_ok:
  scfg_static f /\
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i)) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i))
    (fn_insts (FST (simplify_cfg_round_with_labels f)))
Proof
  strip_tac >> irule simplify_cfg_round_every_from_collapse >>
  simp[collapse_dfs_control_ptr_use_ok] >> conj_tac
  >- (fs[fn_insts_def, fn_insts_blocks_flat, EVERY_FLAT, EVERY_MAP,
          EVERY_MEM, no_phis_def, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  irule remove_unreachable_blocks_every >> simp[]
QED

Theorem simplify_cfg_iter_control_ptr_use_ok:
  !n f. scfg_static f /\
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i)) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i))
    (fn_insts (FST (simplify_cfg_iter_with_labels n f)))
Proof
  Induct >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `simplify_cfg_round_with_labels f` >>
  `scfg_static q` by
    metis_tac[scfg_round_contract, scfg_collapse_contract_def,
              scfg_normalized_static, pairTheory.FST] >>
  drule_all simplify_cfg_round_control_ptr_use_ok >> simp[] >> strip_tac >>
  Cases_on `q.fn_blocks = f.fn_blocks`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  first_x_assum drule_all >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  simp[simplify_cfg_iter_with_labels_def]
QED

Theorem simplify_cfg_fn_control_ptr_use_ok:
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
    (is_terminator i.inst_opcode ==> ptr_use_ok P pv i))
    (fn_insts (reachable_fn f)) ==>
  EVERY (\i. is_terminator i.inst_opcode ==> ptr_use_ok P pv i)
    (fn_insts (simplify_cfg_fn f))
Proof
  strip_tac >> `wf_function f` by metis_tac[scfg_static_wf] >>
  `LENGTH f.fn_blocks <> 0` by
    (fs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `f.fn_blocks` >> gvs[]) >>
  Cases_on `LENGTH f.fn_blocks` >> gvs[] >>
  Cases_on `simplify_cfg_round_with_labels f` >>
  `scfg_static q` by
    metis_tac[scfg_round_contract, scfg_collapse_contract_def,
              scfg_normalized_static, pairTheory.FST] >>
  `EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
     (is_terminator i.inst_opcode ==> ptr_use_ok P pv i)) (fn_insts q)` by
    (`EVERY (\i. i.inst_opcode <> PHI /\ inst_wf i /\ label_positions_ok i /\
        (is_terminator i.inst_opcode ==> ptr_use_ok P pv i))
        (fn_insts (FST (simplify_cfg_round_with_labels f)))` suffices_by simp[] >>
     irule simplify_cfg_round_every_from_collapse >>
     simp[collapse_dfs_control_ptr_use_ok, GSYM reachable_fn_no_phi_cleanup]) >>
  Cases_on `q.fn_blocks = f.fn_blocks`
  >- (gvs[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def,
          simplify_cfg_iter_with_labels_def, fn_insts_def, EVERY_MEM]) >>
  drule_all simplify_cfg_iter_control_ptr_use_ok >>
  disch_then (qspec_then `n` mp_tac) >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def,
       simplify_cfg_iter_with_labels_def, EVERY_MEM]
QED

Theorem pointer_preserving_nonterminator:
  is_pointer_preserving_op op ==> ~is_terminator op
Proof
  Cases_on `op` >> simp[is_pointer_preserving_op_def, is_terminator_def]
QED

Theorem pointer_use_vars_data_subset:
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) SUBSET
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) ==>
  set (pointer_use_vars f vars) SUBSET set (pointer_use_vars g vars)
Proof
  strip_tac >> simp[SUBSET_DEF] >>
  qspecl_then [`f`, `vars`, `set (pointer_use_vars g vars)`]
    mp_tac pointer_use_vars_least >> simp[] >> impl_tac
  >- (conj_tac >- simp[pointer_use_vars_initial] >>
      rpt strip_tac >>
      `MEM inst (fn_insts g)` by
        (fs[SUBSET_DEF, MEM_FILTER] >>
         metis_tac[MEM_fn_insts_blocks_iff, fn_insts_def,
                   pointer_preserving_nonterminator]) >>
      fs[fn_insts_def, MEM_fn_insts_blocks_iff] >>
      metis_tac[pointer_use_vars_closed]) >> simp[]
QED

Theorem pointer_derived_vars_data_eq:
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) ==>
  pointer_derived_vars f roots = pointer_derived_vars g roots
Proof
  strip_tac >> simp[pointer_derived_vars_def] >>
  irule SUBSET_ANTISYM >> conj_tac >>
  irule pointer_use_vars_data_subset >> simp[]
QED

Theorem data_insts_opcode_membership:
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) /\
  ~is_terminator op ==>
  !i. i.inst_opcode = op ==> (MEM i (fn_insts f) <=> MEM i (fn_insts g))
Proof
  simp[EXTENSION, MEM_FILTER] >> metis_tac[]
QED

Theorem alloca_roots_data_eq:
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) ==>
  alloca_roots f = alloca_roots g
Proof
  strip_tac >>
  `!i. i.inst_opcode = ALLOCA ==> (MEM i (fn_insts f) <=> MEM i (fn_insts g))` by
    (rpt strip_tac >> irule data_insts_opcode_membership >>
     simp[is_terminator_def] >> metis_tac[]) >>
  simp[alloca_roots_def, EXTENSION] >> metis_tac[]
QED

Theorem ptr_roots_data_eq:
  f.fn_name = g.fn_name /\
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) ==>
  ptr_roots P f = ptr_roots P g
Proof
  strip_tac >> `alloca_roots f = alloca_roots g` by
    (irule alloca_roots_data_eq >> simp[]) >>
  `!i. i.inst_opcode = DALLOCA ==> (MEM i (fn_insts f) <=> MEM i (fn_insts g))` by
    (rpt strip_tac >> irule data_insts_opcode_membership >>
     simp[is_terminator_def] >> metis_tac[]) >>
  `!i. i.inst_opcode = PARAM ==> (MEM i (fn_insts f) <=> MEM i (fn_insts g))` by
    (rpt strip_tac >> irule data_insts_opcode_membership >>
     simp[is_terminator_def] >> metis_tac[]) >>
  simp[ptr_roots_def, EXTENSION] >> metis_tac[]
QED

Theorem fn_pv_data_eq:
  f.fn_name = g.fn_name /\
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) ==>
  fn_pv P f = fn_pv P g
Proof
  strip_tac >> simp[fn_pv_def] >>
  `ptr_roots P f = ptr_roots P g` by metis_tac[ptr_roots_data_eq] >>
  simp[] >> irule pointer_derived_vars_data_eq >> simp[]
QED

Theorem terminator_ptr_static_rows:
  is_terminator i.inst_opcode /\ i.inst_opcode <> DRET /\
  i.inst_opcode <> RETFMP ==>
  i.inst_opcode <> MEMTOP /\ i.inst_opcode <> GETFMP /\
  i.inst_opcode <> SETFMP /\ i.inst_opcode <> RETFMP /\
  i.inst_opcode <> FMP_PARAM /\ i.inst_opcode <> ISTORE /\
  i.inst_opcode <> ILOAD /\ i.inst_opcode <> ADD /\
  i.inst_opcode <> SUB /\ mem_write_ops i = NONE
Proof
  Cases_on `i.inst_opcode` >> simp[is_terminator_def, mem_write_ops_def]
QED

Theorem fn_ptr_ok_data_transfer:
  f.fn_name = g.fn_name /\
  g.fn_forced_alloc_positions = f.fn_forced_alloc_positions /\
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts f)) =
  set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts g)) /\
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts g) /\
  EVERY (\i. is_terminator i.inst_opcode ==>
       i.inst_opcode <> DRET /\ i.inst_opcode <> RETFMP /\
       i.inst_outputs = [] /\ ptr_use_ok P (fn_pv P g) i) (fn_insts g) /\
  fn_ptr_ok P f ==> fn_ptr_ok P g
Proof
  strip_tac >>
  `ptr_roots P f = ptr_roots P g` by metis_tac[ptr_roots_data_eq] >>
  `alloca_roots f = alloca_roots g` by metis_tac[alloca_roots_data_eq] >>
  `!r. pointer_derived_vars f r = pointer_derived_vars g r` by
    metis_tac[pointer_derived_vars_data_eq] >>
  `fn_pv P f = fn_pv P g` by metis_tac[fn_pv_data_eq] >>
  fs[fn_ptr_ok_def] >> conj_tac
  >- (gen_tac >> disch_tac >> Cases_on `is_terminator inst.inst_opcode`
      >- (fs[EVERY_MEM] >>
          qpat_x_assum `!i. MEM i (fn_insts g) ==> is_terminator _ ==> _`
            (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
          drule_all terminator_ptr_static_rows >> simp[]) >>
      `MEM inst (fn_insts f)` by (fs[EXTENSION, MEM_FILTER] >> metis_tac[]) >>
      metis_tac[]) >>
  conj_tac
  >- (fs[affine_pointer_ops_def, fn_insts_blocks_flat,
          MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
      `~is_terminator inst.inst_opcode` by
        (fs[is_terminator_def] >> metis_tac[]) >>
      `MEM inst (fn_insts g)` by
        (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
      `MEM inst (fn_insts f)` by
        (fs[EXTENSION, MEM_FILTER] >> metis_tac[]) >>
      fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `EVERY (\i. i.inst_opcode <> PHI) _` mp_tac >>
      simp[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff,
           phi_pv_all_var_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~is_terminator inst.inst_opcode` by
        (Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
         `inst.inst_opcode <> DRET /\ inst.inst_opcode <> RETFMP` by
           (fs[EVERY_MEM] >> metis_tac[]) >>
         drule_all terminator_ptr_static_rows >> simp[]) >>
      `MEM inst (fn_insts f)` by
        (fs[EXTENSION, MEM_FILTER] >> metis_tac[]) >> metis_tac[]) >>
  rpt strip_tac >>
  `~is_terminator inst.inst_opcode` by
    (strip_tac >> `inst.inst_outputs = []` by (fs[EVERY_MEM] >> metis_tac[]) >>
     fs[]) >>
  `MEM inst (fn_insts f)` by
    (fs[EXTENSION, MEM_FILTER] >> metis_tac[]) >> metis_tac[]
QED

Theorem simplify_cfg_fn_ptr_ok:
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  EVERY label_positions_ok (fn_insts f) /\
  fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f) ==>
  fn_ptr_ok P (simplify_cfg_fn f)
Proof
  strip_tac >>
  `set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts (reachable_fn f))) =
   set (FILTER (\i. ~is_terminator i.inst_opcode) (fn_insts (simplify_cfg_fn f)))`
    by metis_tac[simplify_cfg_fn_data_insts] >>
  `f.fn_name = (simplify_cfg_fn f).fn_name /\
   (simplify_cfg_fn f).fn_forced_alloc_positions = f.fn_forced_alloc_positions` by
    metis_tac[simplify_cfg_fn_metadata, fn_identity_metadata_eq_def,
              fn_static_input_eq_def] >>
  `fn_pv P (reachable_fn f) = fn_pv P (simplify_cfg_fn f)` by
    (irule fn_pv_data_eq >> simp[reachable_fn_def]) >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts (simplify_cfg_fn f))` by
    (irule simplify_cfg_fn_no_phi >>
     fs[EVERY_MEM, no_phis_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> DRET /\ i.inst_opcode <> RETFMP)
       (fn_insts (simplify_cfg_fn f))` by
    (simp[simplify_cfg_fn_def] >> ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >>
     fs[fn_ptr_ok_def, EVERY_MEM]) >>
  `EVERY (\i. is_terminator i.inst_opcode ==>
       ptr_use_ok P (fn_pv P (reachable_fn f)) i)
       (fn_insts (simplify_cfg_fn f))` by
    (irule simplify_cfg_fn_control_ptr_use_ok >> simp[] >>
     simp[EVERY_MEM] >> gen_tac >> strip_tac >>
     `MEM i (fn_insts f) /\ i.inst_opcode <> PHI` by
       (fs[MEM_reachable_fn_insts, EVERY_MEM, no_phis_def] >>
        metis_tac[reachable_inst_fields, fn_insts_def, MEM_fn_insts_blocks_iff]) >>
     fs[scfg_static_def, fn_inst_wf_def, fn_ptr_ok_def, EVERY_MEM] >>
     metis_tac[fn_insts_def, MEM_fn_insts_blocks_iff]) >>
  `scfg_static (simplify_cfg_fn f)` by
    (qspecl_then [`LENGTH f.fn_blocks`, `f`] mp_tac scfg_iter_contract >>
     simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def]) >>
  `EVERY (\i. is_terminator i.inst_opcode ==> i.inst_outputs = [])
       (fn_insts (simplify_cfg_fn f))` by
    (drule scfg_static_inst_wf >>
     simp[fn_inst_wf_def, EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[venomExecProofsTheory.terminator_no_outputs]) >>
  irule fn_ptr_ok_data_transfer >> simp[EVERY_MEM] >> conj_tac
  >- (fs[EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `reachable_fn f` >> simp[reachable_fn_def]
QED

Theorem reachable_fn_no_phi_all_reachable:
  all_reachable f /\ EVERY no_phis f.fn_blocks ==> reachable_fn f = f
Proof
  strip_tac >>
  `FILTER (\bb. fn_reachable f bb.bb_label) f.fn_blocks = f.fn_blocks` by
    fs[FILTER_EQ_ID, EVERY_MEM, all_reachable_def] >>
  simp[reachable_fn_def] >>
  `MAP (\bb. bb with bb_instructions :=
     MAP (reachable_inst f bb.bb_label) bb.bb_instructions) f.fn_blocks =
     MAP I f.fn_blocks` suffices_by simp[] >>
  irule MAP_CONG >> simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM bb f.fn_blocks` >>
  `MAP (reachable_inst f bb.bb_label) bb.bb_instructions = bb.bb_instructions` by
    (irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
     fs[EVERY_MEM, no_phis_def] >>
     metis_tac[reachable_inst_fields, MEM_EL]) >> simp[]
QED

Theorem simplify_cfg_fn_ptr_ok_reachable:
  scfg_static f /\ EVERY no_phis f.fn_blocks /\
  EVERY label_positions_ok (fn_insts f) /\
  fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f) ==>
  fn_ptr_ok P (simplify_cfg_fn f) /\
  fn_ptr_ok P (reachable_fn (simplify_cfg_fn f))
Proof
  strip_tac >> `fn_ptr_ok P (simplify_cfg_fn f)` by
    (irule simplify_cfg_fn_ptr_ok >> simp[]) >> simp[] >>
  `reachable_fn (simplify_cfg_fn f) = simplify_cfg_fn f` suffices_by simp[] >>
  irule reachable_fn_no_phi_all_reachable >> conj_tac
  >- metis_tac[simplify_cfg_establishes_all_reachable, scfg_static_wf] >>
  `EVERY (\i. i.inst_opcode <> PHI) (fn_insts (simplify_cfg_fn f))` by
    (irule simplify_cfg_fn_no_phi >>
     fs[EVERY_MEM, no_phis_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[]) >>
  fs[EVERY_MEM, no_phis_def, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem simplify_cfg_ctx_static_rows:
  C'.ctx_functions = MAP simplify_cfg_fn C.ctx_functions /\
  C'.ctx_global_reserved = C.ctx_global_reserved /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ~ctx_has_dalloca C /\ fmp_free_ctx C ==>
  EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions /\
  ~ctx_has_dalloca C' /\ fmp_free_ctx C' /\
  (!lo. fixed_region_reserved lo C ==> fixed_region_reserved lo C')
Proof
  strip_tac >>
  `!f. (simplify_cfg_fn f).fn_eom = f.fn_eom /\
       (simplify_cfg_fn f).fn_fmp_signature = f.fn_fmp_signature` by
    metis_tac[simplify_cfg_fn_metadata, fn_static_layout_eq_def,
              fn_fmp_convention_eq_def] >>
  `!f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f) ==>
       EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts (simplify_cfg_fn f))` by
    (gen_tac >> strip_tac >> simp[simplify_cfg_fn_def] >>
     ho_match_mp_tac simplify_cfg_fn_with_labels_opcodes >> simp[]) >>
  `!f. no_raw_fmp_ops f ==> no_raw_fmp_ops (simplify_cfg_fn f)` by
    simp[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_no_raw_fmp_ops] >>
  fs[EVERY_MAP, EVERY_MEM, ctx_has_dalloca_def, EXISTS_MEM,
     fmp_free_ctx_def, fixed_region_reserved_def, MEM_MAP] >> metis_tac[]
QED

Theorem simplify_cfg_fn_shape_ptr_ok:
  o1_fn_shape C f /\ simplify_cfg_fn_ok f /\
  EVERY (\i. i.inst_opcode <> PHI) (fn_insts f) /\
  fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f) ==>
  fn_ptr_ok P (simplify_cfg_fn f) /\
  fn_ptr_ok P (reachable_fn (simplify_cfg_fn f))
Proof
  strip_tac >> irule simplify_cfg_fn_ptr_ok_reachable >>
  fs[o1_fn_shape_def, scfg_static_def, simplifyCfgShapeCoreTheory.fn_shape_ok_scfg_shape] >>
  conj_tac
  >- (fs[EVERY_MEM, no_phis_def, fn_insts_def, MEM_fn_insts_blocks_iff] >>
      metis_tac[]) >>
  fs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]
QED
