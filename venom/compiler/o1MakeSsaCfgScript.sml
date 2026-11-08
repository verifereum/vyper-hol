Theory o1MakeSsaCfg
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps makeSsaHelper makeSsaCurrentInduct venomInst venomState venomWf unitShapeDefs list makeSsaCurrentCfg

Theorem rename_current_block_insts_length:
  !insts s rs rs' s' insts'.
  rename_current_block_insts s rs insts = (rs',s',insts') ==>
  LENGTH insts' = LENGTH insts
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem rename_current_block_insts_last_successors:
  !insts s rs rs' s' insts'.
  insts <> [] /\
  rename_current_block_insts s rs insts = (rs',s',insts') ==>
  get_successors (LAST insts') = get_successors (LAST insts)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `insts = []`
  >- (gvs[rename_current_block_insts_def] >>
      drule rename_current_inst_successors >> simp[]) >>
  `rest' <> []` by
    (drule rename_current_block_insts_length >> Cases_on `rest'` >> gvs[]) >>
  simp[LAST_DEF] >> first_x_assum irule >> metis_tac[]
QED

Theorem rename_current_block_insts_succs:
  rename_current_block_insts s rs bb.bb_instructions = (rs',s',insts') ==>
  bb_succs (bb with bb_instructions := insts') = bb_succs bb
Proof
  strip_tac >>
  drule rename_current_block_insts_length >> strip_tac >>
  Cases_on `bb.bb_instructions = []`
  >- gvs[bb_succs_def] >>
  `insts' <> []` by (Cases_on `insts'` >> gvs[]) >>
  drule_all rename_current_block_insts_last_successors >>
  simp[bb_succs_def] >> Cases_on `bb.bb_instructions` >>
  Cases_on `insts'` >> gvs[]
QED

Theorem update_current_phi_insts_succs:
  bb_succs (bb with bb_instructions :=
    MAP (\inst. if inst.inst_opcode <> PHI then inst
                else inst with inst_operands := update_current_phi_for_pred rs lbl inst.inst_operands)
        bb.bb_instructions) = bb_succs bb
Proof
  qmatch_goalsub_abbrev_tac `MAP f bb.bb_instructions` >>
  Cases_on `bb.bb_instructions` >- simp[bb_succs_def] >>
  simp[bb_succs_def] >>
  pure_once_rewrite_tac[GSYM (CONJUNCT2 MAP)] >>
  simp[LAST_MAP] >>
  Cases_on `(LAST (h::t)).inst_opcode = PHI` >>
  simp[Abbr `f`, get_successors_def, is_terminator_def]
QED

Theorem replace_block_cfg_distinct:
  ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
  lookup_block lbl bbs = SOME bb /\
  bb'.bb_label = bb.bb_label /\ bb_succs bb' = bb_succs bb ==>
  MAP (\b. (b.bb_label, bb_succs b)) (replace_block lbl bb' bbs) =
  MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  rpt strip_tac >> simp[cfgTransformTheory.replace_block_def] >>
  ho_match_mp_tac MAP_replace_at_FIND_distinct >>
  qexists `bb` >> conj_tac
  >- (qpat_assum `ALL_DISTINCT _` mp_tac >> simp[GSYM bb_label_eta]) >>
  gvs[lookup_block_def]
QED

Theorem update_current_succ_phis_cfg:
  ALL_DISTINCT (MAP basic_block_bb_label bbs) ==>
  MAP (\b. (b.bb_label, bb_succs b))
    (update_current_succ_phis rs cur bbs succs) =
  MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  strip_tac >> simp[update_current_succ_phis_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL cfgstep bbs succs` >>
  qsuff_tac `MAP (\b. (b.bb_label, bb_succs b)) (FOLDL cfgstep bbs succs) =
      MAP (\b. (b.bb_label, bb_succs b)) bbs /\
    MAP basic_block_bb_label (FOLDL cfgstep bbs succs) =
      MAP basic_block_bb_label bbs`
  >- simp[] >>
  irule FOLDL_two_maps_invariant_distinct >> rpt strip_tac >>
  simp[Abbr `cfgstep`] >> Cases_on `lookup_block x a` >> gvs[]
  >- (irule replace_block_cfg_distinct >>
      simp[update_current_phi_insts_succs] >> metis_tac[]) >>
  drule lookup_block_label >> strip_tac >>
  irule replace_block_labels_selector >> simp[]
QED

Theorem rename_current_blocks_cfg:
  (!t s rs bbs sm ctrs s' bbs'.
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
    MAP (\b. (b.bb_label, bb_succs b)) bbs' =
    MAP (\b. (b.bb_label, bb_succs b)) bbs) /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
    MAP (\b. (b.bb_label, bb_succs b)) bbs' =
    MAP (\b. (b.bb_label, bb_succs b)) bbs)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >>
      drule lookup_block_label >> strip_tac >>
      drule rename_current_block_insts_succs >> strip_tac >>
      `MAP (\b. (b.bb_label, bb_succs b))
        (replace_block lbl (bb with bb_instructions := insts') bbs) =
       MAP (\b. (b.bb_label, bb_succs b)) bbs` by
        (irule replace_block_cfg_distinct >> simp[] >> metis_tac[]) >>
      `MAP basic_block_bb_label
        (replace_block lbl (bb with bb_instructions := insts') bbs) =
       MAP basic_block_bb_label bbs` by
        (irule replace_block_labels_selector >> simp[]) >>
      `ALL_DISTINCT (MAP basic_block_bb_label
        (update_current_succ_phis rs1 lbl
          (replace_block lbl (bb with bb_instructions := insts') bbs)
          (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss)))` by
        simp[update_current_succ_phis_labels_selector] >>
      first_x_assum drule >> strip_tac >>
      qpat_assum `!s0 c0 st0 sm0 c1 s2 out. _ ==> _` drule >> strip_tac >>
      simp[update_current_succ_phis_cfg])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >>
  qpat_assum `!s0 rs0 b0 sm0 c0 s1 b1. _` (drule_all_then assume_tac) >>
  `ALL_DISTINCT (MAP basic_block_bb_label bbs'')` by
    (drule (CONJUNCT1 rename_current_blocks_labels) >> simp[bb_label_eta]) >>
  qpat_assum `!s0 c0 st0 b0 sm0 c1 s1 b1. _` (drule_all_then assume_tac) >>
  metis_tac[]
QED

Theorem process_frontiers_supply_cfg:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    MAP (\b. (b.bb_label, bb_succs b)) bbs' =
    MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >> rw[MAP_MAP_o] >>
  irule MAP_CONG >> rw[] >> Cases_on `e.bb_label = h` >>
  simp[insert_phi_at_block_succs, build_phi_inst_supply_def,
       makeSsaDefsTheory.insert_phi_at_block_def]
QED

Theorem insert_phis_for_var_supply_cfg:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    MAP (\b. (b.bb_label, bb_succs b)) bbs' =
    MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  drule process_frontiers_supply_cfg >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem add_phi_nodes_supply_cfg:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    MAP (\b. (b.bb_label, bb_succs b)) bbs' =
    MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_cfg >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem simplify_current_phi_successors:
  get_successors (simplify_current_phi inst) = get_successors inst
Proof
  simp[simplify_current_phi_def, keep_current_phi_vars_def] >>
  IF_CASES_TAC >> simp[] >>
  simp[simplify_current_phi_raw_def] >> rpt CASE_TAC >>
  gvs[get_successors_def, is_terminator_def]
QED

Theorem empty_successors_prefix_last:
  !xs ys. EVERY (\i. get_successors i = []) xs ==>
  (if xs ++ ys = [] then [] else get_successors (LAST (xs ++ ys))) =
  (if ys = [] then [] else get_successors (LAST ys))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `xs ++ ys = []` >> gvs[LAST_DEF] >>
  first_x_assum (qspec_then `ys` mp_tac) >>
  Cases_on `xs = []` >> Cases_on `ys = []` >> gvs[]
QED

Theorem simplify_current_phi_prefix_parts_successors:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) ==>
    EVERY (\i. get_successors i = []) phis /\
    (if ordinary = [] then [] else get_successors (LAST ordinary)) =
    (if insts = [] then [] else get_successors (LAST insts))
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >> pairarg_tac >> gvs[] >>
  `get_successors h = []` by gvs[get_successors_def, is_terminator_def] >>
  `get_successors (simplify_current_phi h) = []` by
    simp[simplify_current_phi_successors] >>
  CASE_TAC >> strip_tac >> gvs[] >>
  Cases_on `insts = []` >> Cases_on `ordinary = []` >>
  gvs[LAST_DEF, simplify_current_phi_prefix_parts_def] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem reassign_current_inst_ids_last_successors:
  (if reassign_current_inst_ids ids insts = [] then []
   else get_successors (LAST (reassign_current_inst_ids ids insts))) =
  (if insts = [] then [] else get_successors (LAST insts))
Proof
  mp_tac reassign_current_inst_ids_successors >>
  disch_then (qspecl_then [`ids`,`insts`] mp_tac) >>
  Cases_on `insts` >- simp[reassign_current_inst_ids_def] >>
  Cases_on `reassign_current_inst_ids ids (h::t)` >> simp[] >>
  strip_tac >>
  `LAST (MAP get_successors (h'::t')) = LAST (MAP get_successors (h::t))`
    by (pure_rewrite_tac[MAP] >> asm_rewrite_tac[]) >>
  qpat_x_assum `LAST (MAP _ _) = _` mp_tac >>
  pure_rewrite_tac[LAST_MAP] >> simp[]
QED

Theorem simplify_current_phi_prefix_last_successors:
  (if simplify_current_phi_prefix insts = [] then []
   else get_successors (LAST (simplify_current_phi_prefix insts))) =
  (if insts = [] then [] else get_successors (LAST insts))
Proof
  simp[simplify_current_phi_prefix_def] >> pairarg_tac >> gvs[] >>
  rewrite_tac[reassign_current_inst_ids_last_successors] >>
  drule simplify_current_phi_prefix_parts_successors >> strip_tac >>
  drule empty_successors_prefix_last >>
  disch_then (qspec_then `ordinary` mp_tac) >> simp[]
QED

Theorem simplify_current_phi_block_cfg:
  (simplify_current_phi_block bb).bb_label = bb.bb_label /\
  bb_succs (simplify_current_phi_block bb) = bb_succs bb
Proof
  simp[simplify_current_phi_block_def] >> rpt CASE_TAC >> gvs[] >>
  mp_tac (Q.SPEC `h::t` (GEN_ALL simplify_current_phi_prefix_last_successors)) >>
  Cases_on `simplify_current_phi_prefix (h::t)` >>
  gvs[bb_succs_def]
QED

Theorem simplify_current_phis_if_cfg:
  MAP (\b. (b.bb_label, bb_succs b)) (simplify_current_phis_if enabled bbs) =
  MAP (\b. (b.bb_label, bb_succs b)) bbs
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >>
  simp[simplify_current_phis_def, MAP_MAP_o] >>
  irule MAP_CONG >> simp[simplify_current_phi_block_cfg]
QED

Theorem make_ssa_current_fn_cfg_blocks:
  ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks) /\
  make_ssa_current_fn s fn = (fn',s') ==>
  MAP (\b. (b.bb_label, bb_succs b)) fn'.fn_blocks =
  MAP (\b. (b.bb_label, bb_succs b)) fn.fn_blocks
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule add_phi_nodes_supply_cfg >> strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label bbs1)` by
    (drule add_phi_nodes_supply_labels >> strip_tac >> gvs[bb_label_eta]) >>
  drule_all_then assume_tac (CONJUNCT1 rename_current_blocks_cfg) >>
  gvs[simplify_current_phis_if_cfg]
QED

Theorem cfg_blocks_edges:
  MAP (\b. (b.bb_label, bb_succs b)) fn'.fn_blocks =
  MAP (\b. (b.bb_label, bb_succs b)) fn.fn_blocks ==>
  fn_cfg_edge fn' = fn_cfg_edge fn
Proof
  strip_tac >> simp[FUN_EQ_THM, fn_cfg_edge_def] >> rpt gen_tac >>
  `!a ss. MEM (a,ss) (MAP (\b. (b.bb_label, bb_succs b)) fn'.fn_blocks) <=>
           MEM (a,ss) (MAP (\b. (b.bb_label, bb_succs b)) fn.fn_blocks)`
    by simp[] >>
  fs[MEM_MAP] >> metis_tac[]
QED

Theorem make_ssa_current_fn_cfg_edge:
  ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks) /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_cfg_edge fn' = fn_cfg_edge fn
Proof
  strip_tac >> irule cfg_blocks_edges >>
  drule_all make_ssa_current_fn_cfg_blocks >> simp[]
QED

Theorem make_ssa_current_fn_entry_label:
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >> drule make_ssa_current_fn_labels >>
  Cases_on `fn'.fn_blocks` >> Cases_on `fn.fn_blocks` >>
  simp[fn_entry_label_def, entry_block_def]
QED

Theorem make_ssa_current_fn_reachable:
  ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks) /\
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_reachable fn' = fn_reachable fn
Proof
  strip_tac >> drule_all make_ssa_current_fn_cfg_edge >> strip_tac >>
  drule make_ssa_current_fn_entry_label >>
  simp[FUN_EQ_THM, fn_reachable_def]
QED

Theorem make_ssa_current_fn_first_block_no_preds:
  ALL_DISTINCT (MAP basic_block_bb_label fn.fn_blocks) /\
  make_ssa_current_fn s fn = (fn',s') ==>
  (first_block_no_preds fn' <=> first_block_no_preds fn)
Proof
  strip_tac >> drule_all make_ssa_current_fn_cfg_edge >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  gvs[first_block_no_preds_def] >>
  `h'.bb_label = h.bb_label` by gvs[] >>
  `!l. (?bb. MEM bb fn'.fn_blocks /\ MEM l (bb_succs bb)) <=>
       (?bb. MEM bb fn.fn_blocks /\ MEM l (bb_succs bb))` by
    (qpat_x_assum `fn_cfg_edge _ = _` mp_tac >>
     simp[FUN_EQ_THM, fn_cfg_edge_def] >> metis_tac[]) >>
  qpat_x_assum `!l. _ <=> _` (qspec_then `h.bb_label` mp_tac) >>
  simp[EVERY_MEM] >> metis_tac[]
QED
