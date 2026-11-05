Theory makeSsaRfEdgeShape
Ancestors makeSsaCurrentDefs makeSsaCurrentProps makeSsaHelper cfgTransform cfgTransformProps
          makeSsaRfWitness makeSsaRfRenameTrace venomInst list rich_list pair

Definition current_edge_inst_def:
  current_edge_inst rs p inst = if inst.inst_opcode <> PHI then inst
    else inst with inst_operands := update_current_phi_for_pred rs p inst.inst_operands
End

Definition current_edge_block_def:
  current_edge_block rs p bb =
    bb with bb_instructions := MAP (current_edge_inst rs p) bb.bb_instructions
End

Definition current_edge_step_def:
  current_edge_step rs p bbs l = case lookup_block l bbs of
    NONE => bbs
  | SOME bb => replace_block l (current_edge_block rs p bb) bbs
End

Theorem current_edge_block_label[simp]:
  (current_edge_block rs p bb).bb_label = bb.bb_label
Proof
  simp[current_edge_block_def]
QED

Theorem current_edge_step_lookup:
  lookup_block l (current_edge_step rs p bbs h) =
  OPTION_MAP (\bb. if l = h then current_edge_block rs p bb else bb)
    (lookup_block l bbs)
Proof
  simp[current_edge_step_def] >> Cases_on `lookup_block h bbs` >> simp[]
  >- (Cases_on `l = h` >> gvs[]) >>
  drule lookup_block_label >> strip_tac >> Cases_on `l = h` >> gvs[]
  >- (irule lookup_block_replace_eq >> simp[] >> metis_tac[]) >>
  irule lookup_block_replace_neq >> simp[]
QED

Theorem current_succ_phis_nil[simp]:
  update_current_succ_phis rs p bbs [] = bbs
Proof
  simp[update_current_succ_phis_def]
QED

Theorem current_succ_phis_cons:
  update_current_succ_phis rs p bbs (h::t) =
  update_current_succ_phis rs p (current_edge_step rs p bbs h) t
Proof
  simp[update_current_succ_phis_def, current_edge_step_def,
       current_edge_block_def, GSYM current_edge_inst_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Theorem current_succ_phis_lookup:
  !succs bbs l rs p.
  ALL_DISTINCT succs ==>
  lookup_block l (update_current_succ_phis rs p bbs succs) =
  OPTION_MAP (\bb. if MEM l succs then current_edge_block rs p bb else bb)
    (lookup_block l bbs)
Proof
  Induct >> simp[current_succ_phis_cons] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[current_edge_step_lookup] >>
  Cases_on `lookup_block l bbs` >> simp[] >>
  Cases_on `l = h` >> Cases_on `MEM l succs` >> gvs[]
QED

Theorem current_edge_inst_outputs[simp]:
  (current_edge_inst rs p inst).inst_outputs = inst.inst_outputs
Proof
  simp[current_edge_inst_def] >> Cases_on `inst.inst_opcode = PHI` >> simp[]
QED

Theorem current_edge_block_outputs[simp]:
  MAP instruction_inst_outputs (current_edge_block rs p bb).bb_instructions =
    MAP instruction_inst_outputs bb.bb_instructions
Proof
  simp[current_edge_block_def, MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED

Definition current_block_edge_fold_def:
  current_block_edge_fold rs p succs bb =
    FOLDL (\b q. if q = b.bb_label then current_edge_block rs p b else b) bb succs
End

Definition current_event_edge_def:
  current_event_edge sm
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) =
    current_block_edge_fold rs1 l
      (case ALOOKUP sm l of NONE => [] | SOME ss => ss)
End

Definition current_replay_edges_def:
  current_replay_edges sm events blk =
    FOLDL (\b ev. current_event_edge sm ev b) blk events
End

Theorem current_block_edge_fold_label[simp]:
  !succs bb. (current_block_edge_fold rs p succs bb).bb_label = bb.bb_label
Proof
  Induct >> simp[current_block_edge_fold_def] >>
  rpt gen_tac >> Cases_on `h = bb.bb_label` >>
  simp[GSYM current_block_edge_fold_def]
QED

Theorem current_succ_phis_fold_lookup_option:
  !succs bbs.
    lookup_block q (update_current_succ_phis rs p bbs succs) =
      OPTION_MAP (current_block_edge_fold rs p succs) (lookup_block q bbs)
Proof
  Induct
  >- (gen_tac >> Cases_on `lookup_block q bbs` >>
      simp[current_succ_phis_nil, current_block_edge_fold_def]) >>
  rpt gen_tac >> rewrite_tac[current_succ_phis_cons] >>
  first_x_assum (qspec_then `current_edge_step rs p bbs h` mp_tac) >>
  simp[current_edge_step_lookup] >>
  Cases_on `lookup_block q bbs` >> simp[] >>
  `x.bb_label = q` by metis_tac[lookup_block_label] >>
  Cases_on `q = h` >> gvs[current_block_edge_fold_def]
QED

Theorem current_succ_phis_fold_lookup:
  lookup_block q bbs = SOME bb ==>
  lookup_block q (update_current_succ_phis rs p bbs succs) =
    SOME (current_block_edge_fold rs p succs bb)
Proof
  simp[current_succ_phis_fold_lookup_option]
QED

Theorem current_event_edge_label[simp]:
  (current_event_edge sm ev bb).bb_label = bb.bb_label
Proof
  PairCases_on `ev` >> simp[current_event_edge_def]
QED

Theorem current_replay_edges_label[simp]:
  !events bb. (current_replay_edges sm events bb).bb_label = bb.bb_label
Proof
  Induct >- simp[current_replay_edges_def] >>
  simp[Once current_replay_edges_def] >> simp[GSYM current_replay_edges_def]
QED

Theorem current_replay_edges_append:
  current_replay_edges sm (xs ++ ys) bb =
    current_replay_edges sm ys (current_replay_edges sm xs bb)
Proof
  simp[current_replay_edges_def, FOLDL_APPEND]
QED

Definition current_edge_shape_def:
  current_edge_shape old new <=>
    old.bb_label = new.bb_label /\
    LIST_REL (\i j. i.inst_outputs = j.inst_outputs /\
      i.inst_opcode = j.inst_opcode /\ (i.inst_opcode <> PHI ==> i = j))
      old.bb_instructions new.bb_instructions
End

Theorem current_edge_shape_refl:
  current_edge_shape bb bb
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN]
QED

Theorem current_edge_shape_trans:
  current_edge_shape a b /\ current_edge_shape b c ==> current_edge_shape a c
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem current_edge_block_shape:
  current_edge_shape bb (current_edge_block rs p bb)
Proof
  simp[current_edge_shape_def, current_edge_block_def, LIST_REL_EL_EQN, EL_MAP] >>
  rpt strip_tac >> simp[current_edge_inst_def] >>
  Cases_on `(EL n bb.bb_instructions).inst_opcode = PHI` >> simp[]
QED

Theorem current_block_edge_fold_shape:
  !succs bb. current_edge_shape bb (current_block_edge_fold rs p succs bb)
Proof
  Induct >- simp[current_block_edge_fold_def, current_edge_shape_refl] >>
  rpt gen_tac >> simp[Once current_block_edge_fold_def] >>
  simp[GSYM current_block_edge_fold_def] >>
  Cases_on `h = bb.bb_label` >> simp[] >>
  metis_tac[current_edge_shape_trans, current_edge_block_shape]
QED

Theorem current_event_edge_shape:
  current_edge_shape bb (current_event_edge sm ev bb)
Proof
  PairCases_on `ev` >> simp[current_event_edge_def, current_block_edge_fold_shape]
QED

Theorem current_replay_edges_shape:
  !events bb. current_edge_shape bb (current_replay_edges sm events bb)
Proof
  Induct >- simp[current_replay_edges_def, current_edge_shape_refl] >>
  rpt gen_tac >> simp[Once current_replay_edges_def] >>
  simp[GSYM current_replay_edges_def] >>
  metis_tac[current_edge_shape_trans, current_event_edge_shape]
QED

Theorem current_edge_shape_copy_shape:
  current_edge_shape old new ==>
  LIST_REL rf_copy_shape old.bb_instructions new.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN, rf_copy_shape_def] >> metis_tac[]
QED

Theorem current_replay_edges_length:
  LENGTH (current_replay_edges sm events bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  mp_tac current_replay_edges_shape >> simp[current_edge_shape_def, LIST_REL_EL_EQN]
QED

Theorem current_edge_shape_outputs:
  current_edge_shape old new ==>
  MAP instruction_inst_outputs new.bb_instructions =
    MAP instruction_inst_outputs old.bb_instructions
Proof
  simp[current_edge_shape_def, LIST_REL_EL_EQN] >> strip_tac >>
  irule LIST_EQ >> simp[EL_MAP]
QED

Theorem current_succ_phis_outputs:
  OPTION_MAP (\bb. MAP instruction_inst_outputs bb.bb_instructions)
    (lookup_block l (update_current_succ_phis rs p bbs succs)) =
  OPTION_MAP (\bb. MAP instruction_inst_outputs bb.bb_instructions) (lookup_block l bbs)
Proof
  simp[current_succ_phis_fold_lookup_option] >> Cases_on `lookup_block l bbs` >> simp[] >>
  irule current_edge_shape_outputs >> simp[current_block_edge_fold_shape]
QED

Theorem current_replay_edges_non_phi:
  i < LENGTH bb.bb_instructions /\ (EL i bb.bb_instructions).inst_opcode <> PHI ==>
  EL i (current_replay_edges sm events bb).bb_instructions = EL i bb.bb_instructions
Proof
  mp_tac current_replay_edges_shape >> simp[current_edge_shape_def, LIST_REL_EL_EQN] >>
  metis_tac[]
QED

Theorem current_replay_edges_outputs:
  MAP instruction_inst_outputs (current_replay_edges sm events bb).bb_instructions =
    MAP instruction_inst_outputs bb.bb_instructions
Proof
  irule current_edge_shape_outputs >> simp[current_replay_edges_shape]
QED

Theorem current_annotations_edge_insts:
  !anns insts.
  LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns
    (MAP (current_edge_inst rs p) insts) <=>
  LIST_REL (\a inst. MAP SND a = inst.inst_outputs) anns insts
Proof
  Induct >> Cases_on `insts` >> simp[]
QED

Theorem current_inst_trace_edge:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  current_inst_trace anns (current_edge_inst rt p inst) s rs H E
    (current_edge_inst rt p inst') s' rs' H' E'
Proof
  simp[current_inst_trace_def, current_edge_inst_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[] >>
  qexists_tac `names` >> simp[]
QED

Theorem current_local_trace_edge:
  !annss insts s rs H E insts' s' rs' H' E'.
  current_local_trace annss insts s rs H E insts' s' rs' H' E' ==>
  current_local_trace annss (MAP (current_edge_inst rt p) insts) s rs H E
    (MAP (current_edge_inst rt p) insts') s' rs' H' E'
Proof
  Induct >> simp[current_local_trace_def] >> rpt strip_tac >> gvs[] >>
  drule current_inst_trace_edge >> strip_tac >>
  first_x_assum drule >> strip_tac >> metis_tac[]
QED
