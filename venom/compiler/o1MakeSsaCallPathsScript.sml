Theory o1MakeSsaCallPaths
Ancestors
  unitShapeDefs makeSsaCurrentDefs list

(* The structural observations made by a bounded revert witness. *)
Definition mssa_revert_block_def:
  mssa_revert_block bb bb' <=>
    bb'.bb_label = bb.bb_label /\
    (bb.bb_instructions <> [] /\
     EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions ==>
     bb'.bb_instructions <> [] /\
     EVERY (\i. i.inst_opcode <> INVOKE) bb'.bb_instructions /\
     ((LAST bb.bb_instructions).inst_opcode = REVERT ==>
      (LAST bb'.bb_instructions).inst_opcode = REVERT) /\
     (!l. (LAST bb.bb_instructions).inst_opcode = JMP /\
           (LAST bb.bb_instructions).inst_operands = [Label l] ==>
           (LAST bb'.bb_instructions).inst_opcode = JMP /\
           (LAST bb'.bb_instructions).inst_operands = [Label l]))
End

Theorem mssa_revert_block_refl[simp]:
  mssa_revert_block bb bb
Proof simp[mssa_revert_block_def]
QED

Theorem mssa_revert_block_trans:
  mssa_revert_block a b /\ mssa_revert_block b c ==>
  mssa_revert_block a c
Proof simp[mssa_revert_block_def] >> metis_tac[]
QED

Theorem mssa_revert_path_transport:
  !n l bbs bbs'.
  (!bb. MEM bb bbs ==> ?bb'. MEM bb' bbs' /\ mssa_revert_block bb bb') /\
  revert_path bbs n l ==> revert_path bbs' n l
Proof
  Induct >- simp[revert_path_def] >>
  rpt gen_tac >> simp[revert_path_def, EXISTS_MEM] >> strip_tac >>
  first_assum (drule_then strip_assume_tac) >>
  qpat_x_assum `mssa_revert_block _ _` mp_tac >>
  simp[mssa_revert_block_def] >> strip_tac >>
  qexists_tac `bb'` >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_opcode = REVERT` >> simp[] >>
  Cases_on `(LAST bb.bb_instructions).inst_operands` >> gvs[] >>
  Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
  first_x_assum irule >> qexists_tac `bbs` >> simp[]
QED

Theorem mssa_revert_path_ids:
  !n l bbs.
  revert_path (MAP (\bb. bb with bb_instructions :=
    MAP (\i. i with inst_id := f i) bb.bb_instructions) bbs) n l <=>
  revert_path bbs n l
Proof
  Induct >- simp[revert_path_def] >>
  rpt gen_tac >> simp[revert_path_def, EXISTS_MAP, EVERY_MAP, combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bb.bb_instructions` >> simp[LAST_MAP]
QED

Theorem mssa_flag_fails_ids[simp]:
  flag_fails bbs vs (inst with inst_id := id) <=> flag_fails bbs vs inst
Proof
  simp[flag_fails_def]
QED

Theorem mssa_flag_fails_environment:
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l = revert_path bbs' n l) ==>
  flag_fails bbs vs inst = flag_fails bbs' vs inst
Proof
  strip_tac >> simp[flag_fails_def]
QED

Theorem mssa_flag_path_environment:
  !insts vs.
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l = revert_path bbs' n l) ==>
  flag_path bbs vs insts = flag_path bbs' vs insts
Proof
  Induct >- simp[flag_path_def] >>
  rpt strip_tac >> simp[flag_path_def] >>
  drule_all mssa_flag_fails_environment >> simp[]
QED

Theorem mssa_flag_path_ids:
  !insts vs.
  flag_path bbs vs (MAP (\i. i with inst_id := f i) insts) =
  flag_path bbs vs insts
Proof
  Induct >> simp[flag_path_def]
QED

Theorem mssa_calls_flagged_ids:
  !insts.
  calls_flagged bbs (MAP (\i. i with inst_id := f i) insts) =
  calls_flagged bbs insts
Proof
  Induct >> simp[calls_flagged_def, mssa_flag_path_ids]
QED

Theorem mssa_calls_flagged_environment:
  !insts.
  LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l = revert_path bbs' n l) ==>
  calls_flagged bbs insts = calls_flagged bbs' insts
Proof
  Induct >- simp[calls_flagged_def] >>
  rpt strip_tac >> simp[calls_flagged_def] >>
  Cases_on `h.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  `flag_path bbs [h'] insts = flag_path bbs' [h'] insts` by
    (irule mssa_flag_path_environment >> simp[]) >> simp[]
QED

Theorem mssa_flag_path_reassign_ids:
  !insts ids vs. LENGTH insts <= LENGTH ids ==>
  flag_path bbs vs (reassign_current_inst_ids ids insts) = flag_path bbs vs insts
Proof
  Induct >- (Cases_on `ids` >> simp[reassign_current_inst_ids_def, flag_path_def]) >>
  Cases_on `ids` >> simp[reassign_current_inst_ids_def, flag_path_def]
QED

Theorem mssa_calls_flagged_reassign_ids:
  !insts ids. LENGTH insts <= LENGTH ids ==>
  calls_flagged bbs (reassign_current_inst_ids ids insts) = calls_flagged bbs insts
Proof
  Induct >- (Cases_on `ids` >> simp[reassign_current_inst_ids_def, calls_flagged_def]) >>
  Cases_on `ids` >> simp[reassign_current_inst_ids_def, calls_flagged_def,
                        mssa_flag_path_reassign_ids]
QED

Theorem mssa_flag_path_ids_environment:
  flag_path (MAP (\bb. bb with bb_instructions :=
    MAP (\i. i with inst_id := f i) bb.bb_instructions) bbs) vs insts =
  flag_path bbs vs insts
Proof
  irule mssa_flag_path_environment >> simp[mssa_revert_path_ids]
QED

Theorem mssa_calls_flagged_ids_environment:
  calls_flagged (MAP (\bb. bb with bb_instructions :=
    MAP (\i. i with inst_id := f i) bb.bb_instructions) bbs) insts =
  calls_flagged bbs insts
Proof
  irule mssa_calls_flagged_environment >> simp[mssa_revert_path_ids]
QED
