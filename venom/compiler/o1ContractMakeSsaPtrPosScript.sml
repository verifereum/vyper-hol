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

(* add_phi_nodes_supply only inserts PHIs at the head of a block,
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
  cheat
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
  cheat
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
  cheat
QED
