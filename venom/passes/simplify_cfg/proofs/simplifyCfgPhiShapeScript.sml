(* PHI predecessor and local-reference interfaces for SimplifyCFG. *)
Theory simplifyCfgPhiShape
Ancestors
  simplifyCfgShape simplifyCfgGraphShape simplifyCfgDefs cfgTransform
  venomWf venomInst cfgTransformProps unitShapeDefs list rich_list

Theorem filter_phi_ops_label:
  !ops ps l. phi_well_formed ops ==>
  (MEM (Label l) (filter_phi_ops ps ops) <=>
   MEM (Label l) ops /\ MEM l ps)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[filter_phi_ops_def, phi_well_formed_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem remove_phi_label_label:
  !ops b l. phi_well_formed ops ==>
  (MEM (Label l) (remove_phi_label b ops) <=>
   MEM (Label l) ops /\ l <> b)
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[remove_phi_label_def, phi_well_formed_def] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem update_phi_bypass_label:
  i.inst_opcode = PHI /\ phi_well_formed i.inst_operands /\ a <> b ==>
  (MEM (Label l) (update_phi_bypass a b i).inst_operands <=>
   if MEM (Label a) i.inst_operands then
     MEM (Label l) i.inst_operands /\ l <> b
   else ?k. MEM (Label k) i.inst_operands /\
             l = (if k = b then a else k))
Proof
  strip_tac >> simp[update_phi_bypass_def] >> IF_CASES_TAC >>
  simp[remove_phi_label_label, MEM_MAP] >>
  eq_tac >> rpt strip_tac
  >- (Cases_on `op` >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  qexists_tac `Label k` >> Cases_on `k = b` >> simp[]
QED

Theorem fix_all_phis_graph:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks ==>
  MAP (\bb. (bb.bb_label, bb_succs bb)) (fix_all_phis f).fn_blocks =
  MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks
Proof
  strip_tac >> simp[fix_all_phis_def, MAP_MAP_o, combinTheory.o_DEF] >>
  irule MAP_CONG >> simp[] >> rpt strip_tac >>
  rename1 `MEM bb f.fn_blocks` >>
  `bb_well_formed bb` by gvs[EVERY_MEM] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++
    [LAST bb.bb_instructions]` by
    metis_tac[bb_well_formed_def, APPEND_FRONT_LAST] >>
  metis_tac[fix_phis_in_block_cfg, bb_well_formed_def]
QED

Theorem block_graph_pred_labels:
  MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks =
    MAP (\bb. (bb.bb_label, bb_succs bb)) g.fn_blocks ==>
  pred_labels f lbl = pred_labels g lbl
Proof
  strip_tac >>
  `MAP FST (FILTER (\p. MEM lbl (SND p))
      (MAP (\bb. (bb.bb_label, bb_succs bb)) f.fn_blocks)) =
   MAP FST (FILTER (\p. MEM lbl (SND p))
      (MAP (\bb. (bb.bb_label, bb_succs bb)) g.fn_blocks))` by
    asm_rewrite_tac[] >>
  gvs[pred_labels_def, block_preds_def, FILTER_MAP, MAP_MAP_o,
      combinTheory.o_DEF]
QED

Theorem fix_phi_inst_phi_label:
  inst_wf i /\ (fix_phi_inst ps i).inst_opcode = PHI /\
  MEM (Label l) (fix_phi_inst ps i).inst_operands ==>
  i.inst_opcode = PHI /\ MEM l ps
Proof
  Cases_on `i.inst_opcode = PHI`
  >- (strip_tac >> `phi_well_formed i.inst_operands` by gvs[inst_wf_def] >>
      qpat_x_assum `MEM (Label l) _` mp_tac >>
      qpat_x_assum `(fix_phi_inst ps i).inst_opcode = PHI` mp_tac >>
      simp[fix_phi_inst_def] >>
      Cases_on `filter_phi_ops ps i.inst_operands` >> simp[] >>
      rename1 `h::rest` >> Cases_on `rest` >> simp[]
      >- metis_tac[filter_phi_ops_label, MEM] >>
      rename1 `h::h'::rest` >> Cases_on `rest` >> simp[] >>
      metis_tac[filter_phi_ops_label, MEM]) >>
  simp[fix_phi_inst_def]
QED

Theorem fix_all_phis_phi_preds:
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  EVERY inst_wf (fn_insts f) ==>
  !bb i l. MEM bb (fix_all_phis f).fn_blocks /\
    MEM i bb.bb_instructions /\ i.inst_opcode = PHI /\
    MEM (Label l) i.inst_operands ==>
    MEM l (pred_labels (fix_all_phis f) bb.bb_label)
Proof
  strip_tac >>
  `!lbl. pred_labels (fix_all_phis f) lbl = pred_labels f lbl` by
    (gen_tac >> irule block_graph_pred_labels >> simp[fix_all_phis_graph]) >>
  simp[fix_all_phis_def, MEM_MAP] >> rpt strip_tac >> gvs[] >>
  rename1 `MEM old f.fn_blocks` >>
  qpat_x_assum `MEM i _` mp_tac >>
  simp[fix_phis_in_block_def, MEM_FILTER, MEM_MAP] >> strip_tac >> gvs[] >>
  rename1 `MEM orig old.bb_instructions` >>
  `inst_wf orig` by
    (drule_all ctxLookupAgreeHelpersTheory.EVERY_fn_block >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  drule_all fix_phi_inst_phi_label >> simp[fix_phis_in_block_def]
QED

Theorem pred_labels_mem:
  MEM l (pred_labels f x) <=>
  ?bb. MEM bb f.fn_blocks /\ bb.bb_label = l /\ MEM x (bb_succs bb)
Proof
  simp[pred_labels_def, block_preds_def, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem chain_merge_pred_labels:
  ALL_DISTINCT (fn_labels f) /\
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_merge_blocks f a b /\
  g = f with fn_blocks :=
    update_succ_phi_labels b.bb_label a.bb_label
      (replace_block a.bb_label (merge_blocks a b)
        (remove_block b.bb_label f.fn_blocks))
      (bb_succs (merge_blocks a b)) /\
  MEM x (fn_labels g) /\ MEM l (pred_labels f x) ==>
  MEM (if l = b.bb_label then a.bb_label else l) (pred_labels g x)
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `b.bb_instructions <> []` by
    gvs[EVERY_MEM, bb_well_formed_def] >>
  `a.bb_label <> b.bb_label` by gvs[can_merge_blocks_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label)
    (replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)))` by
    (simp[fn_labels_replace_block, merge_blocks_def] >>
     irule ALL_DISTINCT_remove_block >> gvs[fn_labels_def]) >>
  `!lbl. pred_labels g lbl = pred_labels
    (f with fn_blocks := replace_block a.bb_label (merge_blocks a b)
      (remove_block b.bb_label f.fn_blocks)) lbl` by
    (gen_tac >> irule block_graph_pred_labels >>
     simp[update_succ_phi_labels_graph]) >>
  `x <> b.bb_label` by
    (gvs[fn_labels_def, update_succ_phi_labels_labels,
         fn_labels_replace_block, merge_blocks_def,
         fn_labels_remove_block, MEM_FILTER]) >>
  qpat_x_assum `MEM l (pred_labels f x)`
    (strip_assume_tac o REWRITE_RULE [pred_labels_mem]) >>
  rename1 `MEM src f.fn_blocks` >>
  `src.bb_label = a.bb_label ==> src = a` by
    (strip_tac >> `lookup_block src.bb_label f.fn_blocks = SOME src` by
      (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
     gvs[]) >>
  `src.bb_label = b.bb_label ==> src = b` by
    (strip_tac >> `lookup_block src.bb_label f.fn_blocks = SOME src` by
      (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
     gvs[]) >>
  qpat_x_assum `!lbl. pred_labels g lbl = _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `g = _` kall_tac >>
  simp[pred_labels_mem, replace_block_def, remove_block_def,
       MEM_MAP, MEM_FILTER] >>
  Cases_on `src.bb_label = b.bb_label`
  >- (gvs[] >> qexists_tac `merge_blocks a b` >>
      simp[merge_blocks_succs, merge_blocks_def, MEM_MAP, MEM_FILTER] >>
      metis_tac[]) >>
  Cases_on `src.bb_label = a.bb_label`
  >- gvs[can_merge_blocks_def] >>
  qexists_tac `src` >> simp[] >> conj_tac
  >- (qexists_tac `src` >> simp[]) >> metis_tac[]
QED

Theorem bypass_inst_successors:
  inst_wf i /\ label_positions_ok i ==>
  (MEM lbl (get_successors
    (if ~is_terminator i.inst_opcode then i
     else canon_jnz_inst (subst_label_inst old new i))) <=>
   ?l. MEM l (get_successors i) /\ lbl = (if l = old then new else l))
Proof
  strip_tac >> Cases_on `is_terminator i.inst_opcode` >> simp[]
  >- (Cases_on `i.inst_opcode = JNZ`
      >- (gvs[inst_wf_def] >> gvs[label_positions_ok_def] >>
          rename1 `i.inst_operands = [c; Label t; Label f]` >>
          Cases_on `c` >>
          gvs[stackPlanTypesTheory.is_label_operand_def] >>
          Cases_on `t = old` >> Cases_on `f = old` >>
          simp[subst_label_inst_def, subst_label_op_def, canon_jnz_inst_def] >>
          rpt IF_CASES_TAC >>
          gvs[get_successors_def, is_terminator_def,
              venomStateTheory.get_label_def] >> metis_tac[]) >>
      `canon_jnz_inst (subst_label_inst old new i) = subst_label_inst old new i` by
        (simp[canon_jnz_inst_def, subst_label_inst_def] >>
         Cases_on `MAP (subst_label_op old new) i.inst_operands` >> simp[] >>
         Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
         Cases_on `t` >> simp[]) >>
      simp[subst_label_inst_successors_mem]) >>
  simp[get_successors_def]
QED

Theorem bypass_block_successors:
  EVERY inst_wf bb.bb_instructions /\
  EVERY label_positions_ok bb.bb_instructions ==>
  (MEM lbl (bb_succs
    (bb with bb_instructions := MAP (\i.
      if ~is_terminator i.inst_opcode then i
      else canon_jnz_inst (subst_label_inst old new i)) bb.bb_instructions)) <=>
   ?l. MEM l (bb_succs bb) /\ lbl = (if l = old then new else l))
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `MAP tr bb.bb_instructions` >>
  Cases_on `bb.bb_instructions` >> simp[bb_succs_def] >>
  qspecl_then [`h::t`, `tr`] mp_tac LAST_MAP >>
  (impl_tac >- simp[]) >> pure_rewrite_tac[MAP] >>
  disch_then SUBST1_TAC >> simp[MEM_nub, Abbr `tr`] >>
  irule bypass_inst_successors >>
  metis_tac[EVERY_MEM, LAST_MEM, NOT_CONS_NIL]
QED

Theorem member_lookup_block_eq:
  ALL_DISTINCT (fn_labels f) /\ MEM src f.fn_blocks /\
  lookup_block lbl f.fn_blocks = SOME bb /\ src.bb_label = lbl ==>
  src = bb
Proof
  strip_tac >>
  `lookup_block src.bb_label f.fn_blocks = SOME src` by
    (irule venomExecPropsTheory.MEM_lookup_block >> gvs[fn_labels_def]) >>
  gvs[]
QED

Theorem do_merge_jump_pred_labels:
  ALL_DISTINCT (fn_labels f) /\
  EVERY (\bb. bb_well_formed bb) f.fn_blocks /\
  EVERY inst_wf (fn_insts f) /\
  EVERY label_positions_ok (fn_insts f) /\
  lookup_block a.bb_label f.fn_blocks = SOME a /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\
  do_merge_jump f a b lm = SOME (g,lm') /\
  MEM x (fn_labels g) /\ MEM l (pred_labels f x) ==>
  MEM (if l = b.bb_label then a.bb_label else l) (pred_labels g x)
Proof
  strip_tac >>
  `MEM a f.fn_blocks /\ MEM b f.fn_blocks` by
    metis_tac[lookup_block_member_label] >>
  `EVERY inst_wf a.bb_instructions /\
   EVERY label_positions_ok a.bb_instructions` by
    metis_tac[ctxLookupAgreeHelpersTheory.EVERY_fn_block] >>
  `a.bb_label <> b.bb_label` by
    (strip_tac >> `a = b` by gvs[] >>
     gvs[can_bypass_jump_def, num_succs_def]) >>
  `x <> b.bb_label` by
    (drule do_merge_jump_labels >> strip_tac >> gvs[MEM_FILTER]) >>
  qpat_x_assum `MEM l (pred_labels f x)`
    (strip_assume_tac o REWRITE_RULE [pred_labels_mem]) >>
  rename1 `MEM src f.fn_blocks` >>
  `src.bb_label = a.bb_label ==> src = a` by
    metis_tac[member_lookup_block_eq] >>
  `src.bb_label = b.bb_label ==> src = b` by
    metis_tac[member_lookup_block_eq] >>
  qpat_x_assum `do_merge_jump f a b lm = _` mp_tac >>
  simp[do_merge_jump_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `lookup_block target_lbl f.fn_blocks = SOME target` >>
  `target.bb_label = target_lbl` by metis_tac[lookup_block_member_label] >>
  qmatch_goalsub_abbrev_tac `replace_block a.bb_label source
    (replace_block target_lbl dest rest)` >>
  `source.bb_label = a.bb_label /\ dest.bb_label = target_lbl` by
    simp[Abbr `source`, Abbr `dest`] >>
  `bb_succs dest = bb_succs target` by
    simp[Abbr `dest`, bb_succs_update_phi_bypass_map] >>
  `!lbl. MEM lbl (bb_succs source) <=>
    ?k. MEM k (bb_succs a) /\ lbl = (if k = b.bb_label then target_lbl else k)` by
    (simp[Abbr `source`] >> Cases_on `target_lbl = a.bb_label` >>
     simp[bb_succs_update_phi_bypass_map, bypass_block_successors]) >>
  `MEM source (replace_block a.bb_label source
    (replace_block target_lbl dest rest))` by
    (simp[replace_block_def, Abbr `rest`, remove_block_def, MEM_MAP, MEM_FILTER] >>
     qexists_tac `if a.bb_label = target_lbl then dest else a` >>
     Cases_on `a.bb_label = target_lbl` >> simp[] >>
     qexists_tac `a` >> simp[]) >>
  simp[pred_labels_mem] >>
  Cases_on `src.bb_label = b.bb_label`
  >- (gvs[] >> qexists_tac `source` >> simp[] >>
      metis_tac[can_bypass_jump_def, MEM]) >>
  Cases_on `src.bb_label = a.bb_label`
  >- (gvs[] >> qexists_tac `source` >> simp[] >> metis_tac[]) >>
  Cases_on `src.bb_label = target_lbl`
  >- (`src = target` by (irule member_lookup_block_eq >> metis_tac[]) >>
      qexists_tac `dest` >>
      simp[replace_block_def, Abbr `rest`, remove_block_def, MEM_MAP, MEM_FILTER] >>
      conj_tac >- (qexists_tac `dest` >> simp[] >>
        conj_tac >- metis_tac[] >> qexists_tac `src` >> simp[]) >> metis_tac[]) >>
  qexists_tac `src` >>
  simp[replace_block_def, Abbr `rest`, remove_block_def, MEM_MAP, MEM_FILTER] >>
  qexists_tac `src` >> simp[] >> qexists_tac `src` >> simp[]
QED

Theorem bypass_removed_pred_target:
  ALL_DISTINCT (fn_labels f) /\
  lookup_block b.bb_label f.fn_blocks = SOME b /\
  can_bypass_jump f a b /\ MEM b.bb_label (pred_labels f x) ==>
  bb_succs b = [x]
Proof
  simp[pred_labels_mem] >> strip_tac >>
  rename1 `MEM src f.fn_blocks` >>
  `src = b` by (irule member_lookup_block_eq >> metis_tac[]) >>
  gvs[can_bypass_jump_def, num_succs_def] >>
  Cases_on `bb_succs b` >> gvs[] >> Cases_on `t` >> gvs[]
QED
