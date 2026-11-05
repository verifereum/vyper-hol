(*
 * MakeSSA keeps every instruction's opcode but PHIs and the ASSIGNs and
 * NOPs its cleanup makes of them: each block keeps its label and its
 * other opcodes in order.  So a function's opcodes other than PHI, ASSIGN
 * and NOP are the same list before and after, which keeps the DLOAD count
 * and the absence of DALLOCA.
 *
 * TOP-LEVEL:
 *   make_ssa_current_fn_kept_opcodes - the opcode list besides PHI/ASSIGN/NOP
 *   make_ssa_current_fn_dload_count  - the number of DLOADs
 *   make_ssa_current_fn_no_dalloca   - no DALLOCA added
 *)
Theory o1ContractMakeSsaSrcOpcodes
Ancestors
  makeSsaCurrentProps makeSsaCurrentInduct makeSsaHelper makeSsaCurrentDefs
  makeSsaDefs cfgTransform venomInst list

(* The opcodes MakeSSA neither adds nor removes. *)
Definition kept_opcode_def:
  kept_opcode op <=> op <> PHI /\ op <> ASSIGN /\ op <> NOP
End

(* What MakeSSA keeps of a block: its label and its kept opcodes. *)
Definition block_key_def:
  block_key bb =
    (bb.bb_label,
     FILTER kept_opcode (MAP (\i. i.inst_opcode) bb.bb_instructions))
End

Theorem block_key_labels:
  MAP block_key bbs = MAP block_key bbs' ==>
  MAP (\bb. bb.bb_label) bbs = MAP (\bb. bb.bb_label) bbs'
Proof
  strip_tac >>
  `MAP FST (MAP block_key bbs) = MAP FST (MAP block_key bbs')` by simp[] >>
  fs[MAP_MAP_o, combinTheory.o_DEF, block_key_def]
QED

(* ===== PHI placement ===== *)

Theorem insert_phi_blocks_key:
  phi.inst_opcode = PHI ==>
  MAP block_key
    (MAP (\bb. if bb.bb_label = lbl then insert_phi_at_block phi bb else bb)
         bbs) = MAP block_key bbs
Proof
  rw[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >>
  rw[block_key_def, insert_phi_at_block_def, kept_opcode_def]
QED

Theorem process_frontiers_supply_key:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    MAP block_key bbs' = MAP block_key bbs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> first_x_assum drule >> simp[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  irule insert_phi_blocks_key >> simp[build_phi_inst_supply_def]
QED

Theorem insert_phis_for_var_supply_key:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    MAP block_key bbs' = MAP block_key bbs
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  drule process_frontiers_supply_key >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem add_phi_nodes_supply_key:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    MAP block_key bbs' = MAP block_key bbs
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule insert_phis_for_var_supply_key >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* ===== Renaming ===== *)

(* Replacing the one block of a label by one with its key. *)
Theorem replace_block_key:
  !bbs. ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    lookup_block lbl bbs = SOME bb /\ block_key new = block_key bb ==>
    MAP block_key (replace_block lbl new bbs) = MAP block_key bbs
Proof
  Induct >> simp[replace_block_def, lookup_block_def, FIND_thm] >>
  rpt gen_tac >> Cases_on `h.bb_label = lbl` >> simp[] >> strip_tac >> gvs[]
  >- (simp[MAP_MAP_o, combinTheory.o_DEF] >> irule MAP_CONG >>
      rw[] >> fs[MEM_MAP] >> metis_tac[]) >>
  fs[replace_block_def, lookup_block_def]
QED

Theorem rename_current_inst_opcode:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  inst'.inst_opcode = inst.inst_opcode
Proof
  simp[rename_current_inst_def] >> rpt CASE_TAC >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Theorem rename_current_block_insts_opcodes:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    MAP (\i. i.inst_opcode) insts' = MAP (\i. i.inst_opcode) insts
Proof
  Induct >- simp[rename_current_block_insts_def] >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule rename_current_inst_opcode >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem FOLDL_block_key:
  !xs upd acc.
    (!a x. ALL_DISTINCT (MAP (\bb. bb.bb_label) a) ==>
           MAP block_key (upd a x) = MAP block_key a) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) acc) ==>
    MAP block_key (FOLDL upd acc xs) = MAP block_key acc
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `MAP block_key (upd acc h) = MAP block_key acc` by simp[] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (upd acc h))` by
    metis_tac[block_key_labels] >>
  `MAP block_key (FOLDL upd (upd acc h) xs) =
   MAP block_key (upd acc h)` by (first_x_assum irule >> simp[]) >>
  simp[]
QED

Theorem update_current_succ_phis_key:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
  MAP block_key (update_current_succ_phis rs cur bbs succs) =
  MAP block_key bbs
Proof
  strip_tac >> simp[update_current_succ_phis_def] >>
  irule FOLDL_block_key >> simp[] >> rpt strip_tac >>
  Cases_on `lookup_block x a` >> simp[] >>
  irule replace_block_key >> simp[] >>
  simp[block_key_def, MAP_MAP_o, combinTheory.o_DEF] >>
  AP_TERM_TAC >> irule MAP_CONG >> rw[]
QED

Theorem rename_current_blocks_key:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     MAP block_key bbs' = MAP block_key bbs) /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
     MAP block_key bbs' = MAP block_key bbs)
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
        MAP block_key bbs' = MAP block_key bbs) /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
        ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
        MAP block_key bbs' = MAP block_key bbs)`
  >- metis_tac[] >>
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >>
      rename1 `lookup_block lbl bbs = SOME bb` >>
      rename1 `rename_current_block_insts s rs bb.bb_instructions =
                 (rs1,s1,insts')` >>
      qmatch_asmsub_abbrev_tac `update_current_succ_phis rs1 lbl bbs1 succs` >>
      `MAP block_key bbs1 = MAP block_key bbs` by
        (unabbrev_all_tac >> irule replace_block_key >> simp[] >>
         drule rename_current_block_insts_opcodes >>
         simp[block_key_def]) >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
        metis_tac[block_key_labels] >>
      `MAP block_key (update_current_succ_phis rs1 lbl bbs1 succs) =
       MAP block_key bbs` by simp[update_current_succ_phis_key] >>
      `ALL_DISTINCT (MAP (\bb. bb.bb_label)
         (update_current_succ_phis rs1 lbl bbs1 succs))` by
        metis_tac[block_key_labels] >>
      first_x_assum drule_all >> simp[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs'')` by
    metis_tac[block_key_labels] >>
  first_x_assum drule_all >> simp[]
QED

(* ===== PHI cleanup ===== *)

Theorem simplify_current_phi_not_kept:
  inst.inst_opcode = PHI ==>
  ~kept_opcode (simplify_current_phi inst).inst_opcode
Proof
  rw[simplify_current_phi_def, keep_current_phi_vars_def,
     simplify_current_phi_raw_def] >>
  rpt (CASE_TAC >> gvs[kept_opcode_def]) >> rw[] >> gvs[kept_opcode_def]
QED

Theorem simplify_current_phi_prefix_parts_kept:
  !insts phis ordinary.
    simplify_current_phi_prefix_parts insts = (phis,ordinary) ==>
    FILTER kept_opcode (MAP (\i. i.inst_opcode) (phis ++ ordinary)) =
    FILTER kept_opcode (MAP (\i. i.inst_opcode) insts)
Proof
  Induct >- simp[simplify_current_phi_prefix_parts_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode <> PHI`
  >- (simp[simplify_current_phi_prefix_parts_def] >> strip_tac >> gvs[]) >>
  simp[simplify_current_phi_prefix_parts_def] >> pairarg_tac >> gvs[] >>
  `~kept_opcode (simplify_current_phi h).inst_opcode /\
   ~kept_opcode h.inst_opcode` by
    simp[simplify_current_phi_not_kept, kept_opcode_def] >>
  rw[] >> gvs[FILTER_APPEND_DISTRIB, kept_opcode_def]
QED

Theorem reassign_current_inst_ids_opcodes:
  !ids insts.
    MAP (\i. i.inst_opcode) (reassign_current_inst_ids ids insts) =
    MAP (\i. i.inst_opcode) insts
Proof
  Induct >> Cases_on `insts` >> simp[reassign_current_inst_ids_def]
QED

Theorem simplify_current_phi_block_key:
  block_key (simplify_current_phi_block bb) = block_key bb
Proof
  simp[simplify_current_phi_block_def] >> rpt CASE_TAC >> gvs[] >>
  simp[block_key_def, simplify_current_phi_prefix_def] >>
  pairarg_tac >> gvs[] >>
  rewrite_tac[reassign_current_inst_ids_opcodes] >>
  drule simplify_current_phi_prefix_parts_kept >> simp[]
QED

Theorem simplify_current_phis_if_key:
  MAP block_key (simplify_current_phis_if enabled bbs) = MAP block_key bbs
Proof
  rw[simplify_current_phis_if_def, simplify_current_phis_def, MAP_MAP_o] >>
  irule MAP_CONG >> simp[simplify_current_phi_block_key]
QED

(* ===== The function ===== *)

Theorem make_ssa_current_fn_key:
  ALL_DISTINCT (fn_labels fn) /\ make_ssa_current_fn s fn = (fn',s') ==>
  MAP block_key fn'.fn_blocks = MAP block_key fn.fn_blocks
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  gvs[simplify_current_phis_if_key] >>
  drule add_phi_nodes_supply_key >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    metis_tac[block_key_labels, fn_labels_def] >>
  drule_all (CONJUNCT1 rename_current_blocks_key) >> simp[]
QED

Theorem fn_insts_blocks_kept:
  !bbs. FILTER kept_opcode (MAP (\i. i.inst_opcode) (fn_insts_blocks bbs)) =
        FLAT (MAP (SND o block_key) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, FILTER_APPEND_DISTRIB, block_key_def]
QED

Theorem make_ssa_current_fn_kept_opcodes:
  ALL_DISTINCT (fn_labels fn) /\ make_ssa_current_fn s fn = (fn',s') ==>
  FILTER kept_opcode (MAP (\i. i.inst_opcode) (fn_insts fn')) =
  FILTER kept_opcode (MAP (\i. i.inst_opcode) (fn_insts fn))
Proof
  strip_tac >> drule_all make_ssa_current_fn_key >> strip_tac >>
  simp[fn_insts_def, fn_insts_blocks_kept] >>
  metis_tac[MAP_MAP_o]
QED

Theorem kept_opcode_count:
  kept_opcode op ==>
  LENGTH (FILTER (\i. i.inst_opcode = op) insts) =
  LENGTH (FILTER ($= op) (FILTER kept_opcode (MAP (\i. i.inst_opcode) insts)))
Proof
  strip_tac >> Induct_on `insts` >> rw[] >> gvs[]
QED

Theorem make_ssa_current_fn_dload_count:
  ALL_DISTINCT (fn_labels fn) /\ make_ssa_current_fn s fn = (fn',s') ==>
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn')) =
  LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn))
Proof
  strip_tac >> drule_all make_ssa_current_fn_kept_opcodes >>
  `kept_opcode DLOAD` by simp[kept_opcode_def] >>
  simp[kept_opcode_count]
QED

Theorem make_ssa_current_fn_no_dalloca:
  ALL_DISTINCT (fn_labels fn) /\ make_ssa_current_fn s fn = (fn',s') /\
  MEM inst (fn_insts fn') /\ inst.inst_opcode = DALLOCA ==>
  ?i. MEM i (fn_insts fn) /\ i.inst_opcode = DALLOCA
Proof
  strip_tac >> drule_all make_ssa_current_fn_kept_opcodes >> strip_tac >>
  `MEM DALLOCA (FILTER kept_opcode (MAP (\i. i.inst_opcode) (fn_insts fn')))`
    by (simp[MEM_FILTER, MEM_MAP, kept_opcode_def] >> metis_tac[]) >>
  pop_assum mp_tac >> asm_rewrite_tac[] >> simp[MEM_FILTER, MEM_MAP] >>
  metis_tac[]
QED
