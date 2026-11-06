(*
 * MakeSSA keeps each block's terminator last and only lengthens blocks,
 * so a REVERT at instruction k of an input block is a REVERT at
 * make_ssa_pos in the output block of the same label.  The pointer
 * discipline's taint row exempts a RETURNDATACOPY right before a REVERT
 * (about_to_revert); this carries the exemption to the output.
 *)
Theory o1ContractMakeSsaPtrPos
Ancestors
  makeSsaCurrentLockstep makeSsaCurrentDefs makeSsaCurrentProps
  makeSsaCurrentCfg makeSsaCurrentRevertForward makeSsaDefs o1FrameLockstep
  ptrDiscipline contextCodegenRel o1PassContract venomWf venomInst
  o1ContractMakeSsaSrcOpcodes cfgTransform venomExecProofs makeSsaCurrentInduct

(* Structural interface for the insertion and renaming stages. *)
Definition ptr_block_last_rel_def:
  ptr_block_last_rel bb bb' <=>
    bb.bb_label = bb'.bb_label /\
    LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
    (bb.bb_instructions <> [] /\
     is_terminator (LAST bb.bb_instructions).inst_opcode ==>
     (LAST bb'.bb_instructions).inst_opcode =
     (LAST bb.bb_instructions).inst_opcode)
End

Theorem ptr_block_last_rel_refl[local]:
  ptr_block_last_rel bb bb
Proof
  simp[ptr_block_last_rel_def]
QED

Theorem ptr_block_last_rel_trans[local]:
  ptr_block_last_rel a b /\ ptr_block_last_rel b c ==>
  ptr_block_last_rel a c
Proof
  rw[ptr_block_last_rel_def] >>
  `b.bb_instructions <> []` by
    (Cases_on `b.bb_instructions` >> gvs[]) >>
  metis_tac[]
QED

Theorem ptr_block_last_list_refl[local]:
  LIST_REL ptr_block_last_rel bbs bbs
Proof
  Induct_on `bbs` >> simp[ptr_block_last_rel_refl]
QED

Theorem ptr_block_last_list_trans[local]:
  !xs ys zs. LIST_REL ptr_block_last_rel xs ys /\
    LIST_REL ptr_block_last_rel ys zs ==>
    LIST_REL ptr_block_last_rel xs zs
Proof
  Induct >> Cases_on `ys` >> Cases_on `zs` >>
  simp[] >> metis_tac[ptr_block_last_rel_trans]
QED

Theorem ptr_block_last_lookup[local]:
  !xs ys l bb bb'. LIST_REL ptr_block_last_rel xs ys /\
    lookup_block l xs = SOME bb /\ lookup_block l ys = SOME bb' ==>
    ptr_block_last_rel bb bb'
Proof
  Induct >> Cases_on `ys` >> simp[lookup_block_def, listTheory.FIND_thm] >>
  rpt strip_tac >>
  qpat_assum `ptr_block_last_rel _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_block_last_rel_def]) >>
  qpat_x_assum `_.bb_label = _.bb_label` assume_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `if guard then _ else _` >>
  Cases_on `guard` >> gvs[] >>
  first_x_assum irule >> simp[lookup_block_def] >> metis_tac[]
QED

Theorem ptr_block_last_insert_phi[local]:
  ptr_block_last_rel bb (insert_phi_at_block inst bb)
Proof
  simp[ptr_block_last_rel_def, insert_phi_at_block_def] >>
  Cases_on `bb.bb_instructions` >> simp[]
QED

Theorem ptr_block_last_map_insert[local]:
  LIST_REL ptr_block_last_rel bbs
    (MAP (\bb. if bb.bb_label = l then insert_phi_at_block inst bb else bb) bbs)
Proof
  Induct_on `bbs` >> simp[] >>
  gen_tac >> IF_CASES_TAC >>
  simp[ptr_block_last_insert_phi, ptr_block_last_rel_refl]
QED

Theorem process_frontiers_supply_block_last[local]:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    LIST_REL ptr_block_last_rel bbs bbs'
Proof
  Induct >- simp[process_frontiers_supply_def, ptr_block_last_list_refl] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >> strip_tac >>
  irule ptr_block_last_list_trans >>
  metis_tac[ptr_block_last_map_insert]
QED

Theorem insert_phis_for_var_supply_block_last[local]:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    LIST_REL ptr_block_last_rel bbs bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[ptr_block_last_list_refl] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  drule process_frontiers_supply_block_last >> strip_tac >>
  metis_tac[ptr_block_last_list_trans]
QED

Theorem add_phi_nodes_supply_block_last[local]:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    LIST_REL ptr_block_last_rel bbs bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def, ptr_block_last_list_refl] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_block_last >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ptr_block_last_list_trans]
QED

Theorem ptr_block_last_same_opcodes[local]:
  a.bb_label = b.bb_label /\
  MAP (\i. i.inst_opcode) a.bb_instructions =
  MAP (\i. i.inst_opcode) b.bb_instructions ==>
  ptr_block_last_rel a b
Proof
  strip_tac >>
  `LENGTH a.bb_instructions = LENGTH b.bb_instructions` by
    metis_tac[listTheory.LENGTH_MAP] >>
  simp[ptr_block_last_rel_def] >> strip_tac >>
  qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LAST`) >>
  Cases_on `a.bb_instructions` >> Cases_on `b.bb_instructions` >>
  gvs[listTheory.LAST_MAP]
QED

Theorem ptr_block_last_replace[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  lookup_block l bbs = SOME bb /\ ptr_block_last_rel bb bb' ==>
  LIST_REL ptr_block_last_rel bbs (replace_block l bb' bbs)
Proof
  rw[replace_block_def, listTheory.LIST_REL_EL_EQN] >>
  rename1 `n < LENGTH bbs` >>
  `MEM (EL n bbs) bbs` by simp[listTheory.EL_MEM] >>
  simp[listTheory.EL_MAP] >>
  qmatch_goalsub_abbrev_tac `if x.bb_label = l then _ else _` >>
  Cases_on `x.bb_label = l`
  >- (`lookup_block x.bb_label bbs = SOME x` by
        (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  simp[ptr_block_last_rel_refl]
QED

Theorem ptr_block_last_list_labels[local]:
  !xs ys. LIST_REL ptr_block_last_rel xs ys ==>
    MAP (\bb. bb.bb_label) xs = MAP (\bb. bb.bb_label) ys
Proof
  Induct >> Cases_on `ys` >> simp[] >>
  rpt strip_tac >> gvs[ptr_block_last_rel_def] >> metis_tac[]
QED

Theorem ptr_block_last_fold[local]:
  !xs upd bbs.
    (!a x. ALL_DISTINCT (MAP (\bb. bb.bb_label) a) ==>
      LIST_REL ptr_block_last_rel a (upd a x)) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    LIST_REL ptr_block_last_rel bbs (FOLDL upd bbs xs)
Proof
  Induct >> simp[ptr_block_last_list_refl] >> rpt strip_tac >>
  `LIST_REL ptr_block_last_rel bbs (upd bbs h)` by simp[] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (upd bbs h))` by
    metis_tac[ptr_block_last_list_labels] >>
  `LIST_REL ptr_block_last_rel (upd bbs h) (FOLDL upd (upd bbs h) xs)` by
    (first_x_assum irule >> simp[]) >>
  metis_tac[ptr_block_last_list_trans]
QED

Theorem update_current_succ_phis_block_last[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  LIST_REL ptr_block_last_rel bbs (update_current_succ_phis rs cur bbs succs)
Proof
  strip_tac >> simp[update_current_succ_phis_def] >>
  irule ptr_block_last_fold >> simp[] >> rpt strip_tac >>
  CASE_TAC >> simp[ptr_block_last_list_refl] >>
  irule ptr_block_last_replace >> simp[] >>
  irule ptr_block_last_same_opcodes >> simp[listTheory.MAP_MAP_o] >>
  irule listTheory.MAP_CONG >> rw[]
QED

Theorem rename_current_blocks_block_last[local]:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     LIST_REL ptr_block_last_rel bbs bbs') /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     LIST_REL ptr_block_last_rel bbs bbs')
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
        LIST_REL ptr_block_last_rel bbs bbs') /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
        LIST_REL ptr_block_last_rel bbs bbs')`
  >- metis_tac[] >>
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs(), ptr_block_last_list_refl] >>
      pairarg_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `replace_block lbl bb' bbs` >>
      `LIST_REL ptr_block_last_rel bbs (replace_block lbl bb' bbs)` by
        (irule ptr_block_last_replace >> simp[] >>
         irule ptr_block_last_same_opcodes >> simp[Abbr `bb'`] >>
         metis_tac[rename_current_block_insts_opcodes]) >>
      qmatch_asmsub_abbrev_tac `update_current_succ_phis rs1 lbl bbs1 succs` >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
        metis_tac[ptr_block_last_list_labels] >>
      `LIST_REL ptr_block_last_rel bbs1
         (update_current_succ_phis rs1 lbl bbs1 succs)` by
        simp[update_current_succ_phis_block_last] >>
      first_x_assum drule >>
      impl_tac >- metis_tac[ptr_block_last_list_labels] >>
      metis_tac[ptr_block_last_list_trans])
  >- simp[rename_current_blocks_def, ptr_block_last_list_refl] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >> first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >>
  impl_tac >- metis_tac[ptr_block_last_list_labels] >>
  metis_tac[ptr_block_last_list_trans]
QED

Theorem reassign_current_inst_ids_opcodes[local]:
  !ids insts. MAP (\i. i.inst_opcode) (reassign_current_inst_ids ids insts) =
    MAP (\i. i.inst_opcode) insts
Proof
  recInduct reassign_current_inst_ids_ind >> simp[reassign_current_inst_ids_def]
QED

Theorem ptr_last_nonterminator_prefix[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  pre ++ rest <> [] /\ is_terminator (LAST (pre ++ rest)).inst_opcode ==>
  rest <> []
Proof
  Cases_on `rest` >- (rpt strip_tac >> gvs[] >>
    gvs[listTheory.EVERY_MEM] >>
    metis_tac[rich_listTheory.LAST_MEM]) >> simp[]
QED

Theorem reassign_current_inst_ids_last[local]:
  insts <> [] ==>
  (LAST (reassign_current_inst_ids ids insts)).inst_opcode =
  (LAST insts).inst_opcode
Proof
  strip_tac >>
  qspecl_then [`ids`, `insts`] mp_tac reassign_current_inst_ids_opcodes >>
  disch_then (mp_tac o Q.AP_TERM `LAST`) >>
  Cases_on `insts` >> Cases_on `ids` >>
  simp[reassign_current_inst_ids_def, listTheory.LAST_MAP]
QED

Theorem simplify_current_phi_prefix_last[local]:
  insts <> [] /\ is_terminator (LAST insts).inst_opcode ==>
  (LAST (simplify_current_phi_prefix insts)).inst_opcode =
    (LAST insts).inst_opcode
Proof
  strip_tac >> simp[simplify_current_phi_prefix_def] >>
  pairarg_tac >> gvs[] >>
  drule simplify_current_phi_prefix_parts_shape >> strip_tac >>
  `rest <> []` by metis_tac[ptr_last_nonterminator_prefix] >>
  simp[reassign_current_inst_ids_last] >>
  Cases_on `rest` >> gvs[listTheory.LAST_APPEND_CONS]
QED

Theorem simplify_current_phi_block_last[local]:
  ptr_block_last_rel bb (simplify_current_phi_block bb)
Proof
  simp[ptr_block_last_rel_def] >>
  `LENGTH (simplify_current_phi_block bb).bb_instructions =
   LENGTH bb.bb_instructions` by
    (mp_tac (Q.AP_TERM `LENGTH` simplify_current_phi_block_ids) >>
     pure_rewrite_tac[irSupplyTheory.block_ir_inst_ids_def,
                      listTheory.LENGTH_MAP] >> simp[]) >>
  simp[] >> strip_tac >>
  simp[simplify_current_phi_block_def] >> CASE_TAC >> gvs[] >>
  IF_CASES_TAC >> simp[simplify_current_phi_prefix_last]
QED

Theorem simplify_current_phis_if_block_last[local]:
  LIST_REL ptr_block_last_rel bbs (simplify_current_phis_if enabled bbs)
Proof
  `LIST_REL ptr_block_last_rel bbs (MAP simplify_current_phi_block bbs)` by
    (Induct_on `bbs` >> simp[simplify_current_phi_block_last]) >>
  rw[simplify_current_phis_if_def, simplify_current_phis_def,
     ptr_block_last_list_refl]
QED

Theorem make_ssa_current_fn_block_last_rel[local]:
  make_ssa_current_fn s fn = (fn',s') /\ ALL_DISTINCT (fn_labels fn) ==>
  LIST_REL ptr_block_last_rel fn.fn_blocks fn'.fn_blocks
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[ptr_block_last_list_refl] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  drule add_phi_nodes_supply_block_last >> strip_tac >>
  drule (CONJUNCT1 rename_current_blocks_block_last) >>
  impl_tac >- metis_tac[ptr_block_last_list_labels, fn_labels_def] >>
  strip_tac >>
  metis_tac[ptr_block_last_list_trans, simplify_current_phis_if_block_last]
QED

(* PHI insertion only lengthens blocks at their heads;
   rename_current_blocks keeps each instruction's opcode and the block
   lengths, and simplify_current_phis_if only rewrites the leading PHIs
   (to PHI, ASSIGN or NOP, keeping the count).  A well-formed block ends
   in a terminator, which is no PHI, so it stays last. *)
Theorem make_ssa_current_fn_block_last:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' ==>
  LENGTH bb.bb_instructions <= LENGTH bb'.bb_instructions /\
  (LAST bb'.bb_instructions).inst_opcode =
  (LAST bb.bb_instructions).inst_opcode
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all make_ssa_current_fn_block_last_rel >> strip_tac >>
  drule_all ptr_block_last_lookup >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  gvs[ptr_block_last_rel_def, bb_well_formed_def]
QED

Theorem make_ssa_pos_revert:
  wf_function fn /\ make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = REVERT ==>
  make_ssa_pos fn fn' l k < LENGTH bb'.bb_instructions /\
  (EL (make_ssa_pos fn fn' l k) bb'.bb_instructions).inst_opcode = REVERT
Proof
  strip_tac >> drule_all make_ssa_current_fn_block_last >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `k = PRE (LENGTH bb.bb_instructions)` by
    (gvs[bb_well_formed_def] >>
     first_x_assum irule >> simp[is_terminator_def]) >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `make_ssa_pos fn fn' l k = PRE (LENGTH bb'.bb_instructions)` by
    (simp[make_ssa_pos_def] >> decide_tac) >>
  `0 < LENGTH bb'.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  gvs[] >>
  `LAST bb.bb_instructions =
     EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions` by
    metis_tac[listTheory.LAST_EL] >>
  `LAST bb'.bb_instructions =
     EL (PRE (LENGTH bb'.bb_instructions)) bb'.bb_instructions` by
    (irule listTheory.LAST_EL >> Cases_on `bb'.bb_instructions` >> gvs[]) >>
  metis_tac[]
QED

Theorem make_ssa_pos_suc[local]:
  make_ssa_pos fn fn' l (SUC k) = SUC (make_ssa_pos fn fn' l k)
Proof
  simp[make_ssa_pos_def]
QED

(* A paired state of a MakeSSA lockstep sits at make_ssa_pos in the block
   of the same label (lockstep_rel, state_rel); the revert forwarding
   (make_ssa_current_fn_revert_forward_at) and a REVERT right after
   (make_ssa_pos_revert, with make_ssa_pos l (SUC k) = SUC (make_ssa_pos
   l k)) sit at the matching positions of the output block. *)
Theorem make_ssa_lockstep_revert:
  lockstep_sim L C C' fn fn' (make_ssa_pos fn fn') R /\
  R T (inst,s) sg (inst',s') /\
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
  make_ssa_current_fn t fn = (fn',t') ==>
  (in_revert_forward fn s ==> in_revert_forward fn' s') /\
  (about_to_revert fn inst s ==> about_to_revert fn' inst' s')
Proof
  strip_tac >> drule_all lockstep_rel >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn'.fn_blocks)` by
    metis_tac[make_ssa_current_fn_labels] >>
  `?bb'. lookup_block s.vs_current_bb fn'.fn_blocks = SOME bb'` by
    (gvs[active_inst_def, state_rel_def] >>
     metis_tac[MEM_lookup_block]) >>
  conj_tac
  >- (rw[in_revert_forward_def] >>
      drule_all make_ssa_current_fn_revert_forward_at >> strip_tac >>
      gvs[state_rel_def, make_ssa_pos_def] >> metis_tac[]) >>
  rw[about_to_revert_def]
  >- gvs[inst_pair_def] >>
  disj2_tac >> conj_tac >- gvs[inst_pair_def] >>
  `s'.vs_current_bb = s.vs_current_bb` by metis_tac[state_rel_def] >>
  qpat_x_assum `state_rel _ _ _` kall_tac >>
  gvs[active_inst_def] >>
  rename1 `(EL (SUC s.vs_inst_idx) next.bb_instructions).inst_opcode = REVERT` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME next` by
    (drule_all MEM_lookup_block >> simp[]) >>
  drule_all make_ssa_pos_revert >> strip_tac >>
  qexists_tac `EL (make_ssa_pos fn fn' s.vs_current_bb (SUC s.vs_inst_idx))
                  bb'.bb_instructions` >>
  simp[] >> qexists_tac `bb'` >>
  metis_tac[lookup_block_MEM, lookup_block_label, make_ssa_pos_suc]
QED
