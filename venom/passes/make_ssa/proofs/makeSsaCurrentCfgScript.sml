(*
 * MakeSSA (make_ssa_current_fn) keeps every block's label and successors,
 * so its output has the input's CFG, entry and reachable blocks.  PHI
 * insertion only prepends PHIs, renaming rewrites variables and never
 * labels, and the PHI cleanup only turns leading PHIs into other
 * non-terminators; none of them changes what a block's last instruction
 * branches to.
 *
 * Also: SSA code with distinct block labels has definite assignment
 * (wf_ssa_defs_reach_uses needs only the distinct labels of wf_function).
 *)
Theory makeSsaCurrentCfg
Ancestors
  makeSsaCurrentDefs makeSsaCurrentProps makeSsaCurrentInduct makeSsaDefs
  venomExecProofs venomWf cfgWf venomInst venomState cfgTransform list rich_list

Overload block_succs_map = ``MAP (\bb. (bb.bb_label, bb_succs bb))``

Theorem block_succs_map_labels[simp]:
  MAP FST (block_succs_map bbs) = MAP (\bb. bb.bb_label) bbs
Proof
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

(* ===== A block's successors ===== *)

Theorem bb_succs_same_successors:
  MAP get_successors new.bb_instructions =
  MAP get_successors old.bb_instructions ==>
  bb_succs new = bb_succs old
Proof
  strip_tac >>
  `LENGTH new.bb_instructions = LENGTH old.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LAST`) >>
  Cases_on `new.bb_instructions` >> Cases_on `old.bb_instructions` >>
  gvs[bb_succs_def, LAST_MAP]
QED

Theorem non_terminators_last_successors:
  EVERY (\i. ~is_terminator i.inst_opcode) l /\ l <> [] ==>
  get_successors (LAST l) = []
Proof
  rw[EVERY_MEM, get_successors_def] >>
  `MEM (LAST l) l` by simp[LAST_MEM] >> metis_tac[]
QED

Theorem bb_succs_non_terminator_prefix:
  !bb pre rest.
  bb.bb_instructions = pre ++ rest /\
  EVERY (\i. ~is_terminator i.inst_opcode) pre ==>
  bb_succs bb = bb_succs (bb with bb_instructions := rest)
Proof
  rpt strip_tac >> Cases_on `rest`
  >- (Cases_on `pre` >> gvs[bb_succs_def] >>
      `get_successors (LAST (h::t)) = []` suffices_by simp[] >>
      irule non_terminators_last_successors >> simp[]) >>
  Cases_on `pre` >- (simp[bb_succs_def] >> fs[]) >>
  `LAST (h'::(t' ++ h::t)) = LAST (h::t)` by
    (`h'::(t' ++ h::t) = (h'::t') ++ h::t` by simp[] >>
     pop_assum SUBST1_TAC >> REWRITE_TAC[LAST_APPEND_CONS]) >>
  simp[bb_succs_def] >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
  simp[] >> ASM_REWRITE_TAC[]
QED

Theorem insert_phi_at_block_succs:
  inst.inst_opcode = PHI ==>
  bb_succs (insert_phi_at_block inst bb) = bb_succs bb /\
  (insert_phi_at_block inst bb).bb_label = bb.bb_label
Proof
  strip_tac >> simp[insert_phi_at_block_def] >>
  qmatch_goalsub_abbrev_tac `bb_succs b'` >>
  `bb_succs b' = bb_succs (b' with bb_instructions := bb.bb_instructions)` by
    (irule bb_succs_non_terminator_prefix >> qexists_tac `[inst]` >>
     simp[Abbr `b'`, is_terminator_def]) >>
  simp[Abbr `b'`] >> AP_TERM_TAC >>
  simp[venomInstTheory.basic_block_component_equality]
QED

(* Replacing the block at a label by one with the same label and
   successors keeps the map, given distinct labels. *)
Theorem replace_block_succs_map:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  lookup_block lbl bbs = SOME bb /\
  bb'.bb_label = bb.bb_label /\ bb_succs bb' = bb_succs bb ==>
  block_succs_map (replace_block lbl bb' bbs) = block_succs_map bbs
Proof
  rw[replace_block_def, MAP_MAP_o] >> irule MAP_CONG >> rw[] >>
  `lookup_block x.bb_label bbs = SOME x` by (irule MEM_lookup_block >> simp[]) >>
  gvs[]
QED

(* ===== PHI insertion ===== *)

Theorem process_frontiers_supply_succs_map:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    block_succs_map bbs' = block_succs_map bbs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >>
  rw[MAP_MAP_o] >> irule MAP_CONG >> rw[] >>
  simp[insert_phi_at_block_succs, build_phi_inst_supply_def]
QED

Theorem insert_phis_for_var_supply_succs_map:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    block_succs_map bbs' = block_succs_map bbs
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[]
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
     drule process_frontiers_supply_succs_map >> strip_tac >>
     first_x_assum drule >> simp[]
QED

Theorem add_phi_nodes_supply_succs_map:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    block_succs_map bbs' = block_succs_map bbs
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_succs_map >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* ===== Renaming ===== *)

Theorem rename_current_operands_labels:
  !ops. MAP get_label (rename_current_operands rs ops) = MAP get_label ops
Proof
  Induct >> simp[rename_current_operands_def] >>
  Cases_on `h` >> simp[rename_current_operands_def, get_label_def]
QED

Theorem rename_current_inst_successors:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  get_successors inst' = get_successors inst
Proof
  rw[rename_current_inst_def] >> pairarg_tac >> gvs[] >>
  simp[get_successors_def, rename_current_operands_labels]
QED

Theorem rename_current_block_insts_successors:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    MAP get_successors insts' = MAP get_successors insts
Proof
  Induct >> simp[rename_current_block_insts_def] >> rpt gen_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[rename_current_inst_successors]
QED

Theorem FOLDL_distinct_invariant:
  !xs step acc (g : 'a -> ('b # 'c) list).
    (!a x. ALL_DISTINCT (MAP FST (g a)) ==> g (step a x) = g a) /\
    ALL_DISTINCT (MAP FST (g acc)) ==>
    g (FOLDL step acc xs) = g acc
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `g (FOLDL step (step acc h) xs) = g (step acc h)` by
    (first_x_assum irule >> metis_tac[]) >>
  metis_tac[]
QED

Theorem update_current_succ_phis_succs_map:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  block_succs_map (update_current_succ_phis rs current_label bbs succs) =
  block_succs_map bbs
Proof
  strip_tac >> simp[update_current_succ_phis_def] >>
  ho_match_mp_tac FOLDL_distinct_invariant >> simp[] >>
  rpt strip_tac >> CASE_TAC >> simp[] >>
  irule replace_block_succs_map >> simp[] >>
  irule bb_succs_same_successors >> simp[MAP_MAP_o] >>
  irule MAP_CONG >> rw[] >> simp[get_successors_def, is_terminator_def]
QED

Theorem rename_current_blocks_succs_map:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     block_succs_map bbs' = block_succs_map bbs) /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     block_succs_map bbs' = block_succs_map bbs)
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
        block_succs_map bbs' = block_succs_map bbs) /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
        block_succs_map bbs' = block_succs_map bbs)`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `replace_block lbl bb' bbs` >>
      `block_succs_map (replace_block lbl bb' bbs) = block_succs_map bbs` by
        (irule replace_block_succs_map >> simp[Abbr `bb'`] >>
         irule bb_succs_same_successors >> simp[] >>
         metis_tac[rename_current_block_insts_successors]) >>
      qmatch_asmsub_abbrev_tac `update_current_succ_phis rs1 lbl bbs1 succs` >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
        metis_tac[block_succs_map_labels] >>
      `block_succs_map (update_current_succ_phis rs1 lbl bbs1 succs) =
       block_succs_map bbs` by simp[update_current_succ_phis_succs_map] >>
      first_x_assum drule >> impl_tac >- metis_tac[block_succs_map_labels] >>
      simp[])
  >- simp[rename_current_blocks_def]
  >> rpt strip_tac >> gvs[rename_current_blocks_def] >>
     pairarg_tac >> gvs[] >>
     first_x_assum drule_all >> strip_tac >>
     first_x_assum drule >> impl_tac >- metis_tac[block_succs_map_labels] >>
     simp[]
QED

(* ===== PHI cleanup ===== *)

Theorem simplify_current_phi_non_terminator:
  inst.inst_opcode = PHI ==>
  ~is_terminator (simplify_current_phi inst).inst_opcode
Proof
  rw[simplify_current_phi_def, keep_current_phi_vars_def,
     simplify_current_phi_raw_def] >>
  rpt CASE_TAC >> gvs[is_terminator_def]
QED

(* The cleanup turns a block's leading PHIs into PHIs and copies, which
   it reorders, and keeps the rest of the block. *)
Theorem simplify_current_phi_prefix_parts_shape:
  !insts phis ord.
    simplify_current_phi_prefix_parts insts = (phis,ord) ==>
    ?pre post rest.
      insts = pre ++ rest /\ ord = post ++ rest /\
      EVERY (\i. ~is_terminator i.inst_opcode) pre /\
      EVERY (\i. ~is_terminator i.inst_opcode) phis /\
      EVERY (\i. ~is_terminator i.inst_opcode) post
Proof
  Induct >> simp[simplify_current_phi_prefix_parts_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> qexistsl_tac [`[]`, `[]`, `h::insts`] >> gvs[]) >>
  pairarg_tac >> simp[] >> first_x_assum drule >> strip_tac >>
  `~is_terminator (simplify_current_phi h).inst_opcode` by
    gvs[simplify_current_phi_non_terminator] >>
  `~is_terminator h.inst_opcode` by gvs[is_terminator_def] >>
  rw[]
  >- (qexistsl_tac [`h::pre`, `post`, `rest`] >> gvs[])
  >> qexistsl_tac [`h::pre`, `simplify_current_phi h::post`, `rest`] >> gvs[]
QED

Theorem reassign_current_inst_ids_successors:
  !ids insts.
    MAP get_successors (reassign_current_inst_ids ids insts) =
    MAP get_successors insts
Proof
  recInduct reassign_current_inst_ids_ind >>
  simp[reassign_current_inst_ids_def, get_successors_def]
QED

Theorem simplify_current_phi_block_succs:
  bb_succs (simplify_current_phi_block bb) = bb_succs bb /\
  (simplify_current_phi_block bb).bb_label = bb.bb_label
Proof
  simp[simplify_current_phi_block_def] >> CASE_TAC >> simp[] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_def] >>
  pairarg_tac >> simp[] >>
  drule simplify_current_phi_prefix_parts_shape >> strip_tac >>
  qmatch_goalsub_abbrev_tac `bb_succs b'` >>
  `bb_succs b' = bb_succs (bb with bb_instructions := phis ++ post ++ rest)` by
    (irule bb_succs_same_successors >>
     simp[Abbr `b'`, reassign_current_inst_ids_successors]) >>
  `bb_succs (bb with bb_instructions := phis ++ post ++ rest) =
   bb_succs (bb with bb_instructions := rest)` by
    (qspecl_then [`bb with bb_instructions := phis ++ post ++ rest`,
                  `phis ++ post`, `rest`] mp_tac bb_succs_non_terminator_prefix >>
     simp[]) >>
  `bb_succs bb = bb_succs (bb with bb_instructions := rest)` by
    (irule bb_succs_non_terminator_prefix >> qexists_tac `pre` >> simp[]) >>
  simp[]
QED

Theorem simplify_current_phis_if_succs_map:
  block_succs_map (simplify_current_phis_if b bbs) = block_succs_map bbs
Proof
  rw[simplify_current_phis_if_def, simplify_current_phis_def, MAP_MAP_o,
     combinTheory.o_DEF, simplify_current_phi_block_succs]
QED

(* ===== The whole pass ===== *)

Theorem make_ssa_current_fn_succs_map:
  make_ssa_current_fn s fn = (fn',s') /\ ALL_DISTINCT (fn_labels fn) ==>
  block_succs_map fn'.fn_blocks = block_succs_map fn.fn_blocks
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[]
  >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  simp[simplify_current_phis_if_succs_map] >>
  drule add_phi_nodes_supply_succs_map >> strip_tac >>
  drule (CONJUNCT1 rename_current_blocks_succs_map) >>
  impl_tac >- metis_tac[block_succs_map_labels, fn_labels_def] >>
  simp[]
QED

Theorem succs_map_cfg_edge:
  block_succs_map f'.fn_blocks = block_succs_map f.fn_blocks ==>
  fn_cfg_edge f' = fn_cfg_edge f /\ fn_entry_label f' = fn_entry_label f
Proof
  strip_tac >>
  `!g a b. fn_cfg_edge g a b <=>
     ?ss. MEM (a,ss) (block_succs_map g.fn_blocks) /\ MEM b ss` by
    (simp[fn_cfg_edge_def, MEM_MAP] >> metis_tac[]) >>
  simp[FUN_EQ_THM] >>
  `MAP (\bb. bb.bb_label) f'.fn_blocks = MAP (\bb. bb.bb_label) f.fn_blocks` by
    metis_tac[block_succs_map_labels] >>
  Cases_on `f'.fn_blocks` >> Cases_on `f.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def]
QED

Theorem make_ssa_current_fn_cfg:
  make_ssa_current_fn s fn = (fn',s') /\ ALL_DISTINCT (fn_labels fn) ==>
  fn_cfg_edge fn' = fn_cfg_edge fn /\ fn_entry_label fn' = fn_entry_label fn
Proof
  metis_tac[make_ssa_current_fn_succs_map, succs_map_cfg_edge]
QED

Theorem make_ssa_current_fn_all_reachable:
  make_ssa_current_fn s fn = (fn',s') /\ ALL_DISTINCT (fn_labels fn) /\
  all_reachable fn ==>
  all_reachable fn'
Proof
  strip_tac >> drule_all make_ssa_current_fn_cfg >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  gvs[all_reachable_def, fn_reachable_def] >> rpt strip_tac >>
  `MEM bb.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED

(* ===== Definite assignment from SSA ===== *)

Theorem distinct_labels_same_block:
  ALL_DISTINCT (fn_labels f) /\ MEM bb1 f.fn_blocks /\ MEM bb2 f.fn_blocks /\
  bb1.bb_label = bb2.bb_label ==>
  bb1 = bb2
Proof
  rw[fn_labels_def] >>
  `lookup_block bb1.bb_label f.fn_blocks = SOME bb1` by
    (irule MEM_lookup_block >> simp[]) >>
  `lookup_block bb1.bb_label f.fn_blocks = SOME bb2` by
    (irule MEM_lookup_block >> gvs[]) >>
  gvs[]
QED

Theorem def_available_on_all_paths_distinct:
  ALL_DISTINCT (fn_labels fn) /\ MEM bb fn.fn_blocks /\
  def_available_at fn bb point v ==>
  def_on_all_paths fn bb point v
Proof
  simp[def_available_at_def] >> rpt strip_tac >>
  simp[def_on_all_paths_def] >> rpt strip_tac >>
  Cases_on `def_bb = bb`
  >- (gvs[] >> disj2_tac >> Cases_on `point` >> gvs[]
      >- metis_tac[MEM_EL] >>
      qexists_tac `i` >> simp[] >> metis_tac[arithmeticTheory.LESS_TRANS]) >>
  disj1_tac >>
  `MEM def_bb.bb_label path` by metis_tac[fn_dominates_def] >>
  `def_bb.bb_label <> bb.bb_label` by metis_tac[distinct_labels_same_block] >>
  qpat_x_assum `MEM def_bb.bb_label path` mp_tac >>
  disch_then (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `k < LENGTH path` >>
  qexistsl_tac [`k`, `def_bb`, `def_inst`] >> simp[] >>
  `LAST path = EL (LENGTH path - 1) path` by
    (qspec_then `path` mp_tac LAST_EL >> simp[arithmeticTheory.PRE_SUB1]) >>
  Cases_on `k = LENGTH path - 1` >> gvs[] >> decide_tac
QED

Theorem wf_ssa_defs_reach_uses_distinct:
  wf_ssa fn /\ ALL_DISTINCT (fn_labels fn) ==> fn_defs_reach_uses fn
Proof
  simp[wf_ssa_def, fn_defs_reach_uses_def, def_dominates_uses_def] >>
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (rpt strip_tac >>
      `phi_edge_uses_wf fn bb inst` by metis_tac[] >>
      qpat_x_assum `phi_edge_uses_wf _ _ _` mp_tac >>
      pure_rewrite_tac[phi_edge_uses_wf_def] >> strip_tac >>
      qpat_x_assum `!pred v. MEM (pred,v) _ ==> _` drule >>
      strip_tac >> rename1 `def_available_at fn source NONE v` >>
      `source = pred_bb` by metis_tac[distinct_labels_same_block] >>
      gvs[] >> irule def_available_on_all_paths_distinct >> metis_tac[]) >>
  rpt strip_tac >> irule def_available_on_all_paths_distinct >> metis_tac[]
QED

(* In SSA form every variable has at most one writer. *)
Theorem ssa_outputs_single_def:
  !l. ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) l)) ==>
      LENGTH (FILTER (\i. MEM v i.inst_outputs) l) <= 1
Proof
  Induct >> rw[ALL_DISTINCT_APPEND] >>
  `FILTER (\i. MEM v i.inst_outputs) l = []` suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  gvs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED
