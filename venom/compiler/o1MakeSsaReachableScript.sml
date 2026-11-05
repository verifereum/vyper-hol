Theory o1MakeSsaReachable
Ancestors
  unitShapeDefs venomInst list rich_list

Theorem reachable_fn_fixed:
  (!bb. MEM bb fn.fn_blocks ==> fn_reachable fn bb.bb_label) /\
  (!bb i. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions ==>
          reachable_inst fn bb.bb_label i = i) ==>
  reachable_fn fn = fn
Proof
  rpt strip_tac >>
  `FILTER (\bb. fn_reachable fn bb.bb_label) fn.fn_blocks = fn.fn_blocks` by
    (simp[FILTER_EQ_ID, EVERY_MEM]) >>
  simp[reachable_fn_def] >>
  `MAP (\bb. bb with bb_instructions :=
          MAP (reachable_inst fn bb.bb_label) bb.bb_instructions)
       fn.fn_blocks = fn.fn_blocks` suffices_by simp[] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  `MEM (EL x fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `MAP (reachable_inst fn (EL x fn.fn_blocks).bb_label)
       (EL x fn.fn_blocks).bb_instructions =
       (EL x fn.fn_blocks).bb_instructions` suffices_by simp[] >>
  irule LIST_EQ >> simp[EL_MAP] >> rpt strip_tac >>
  first_x_assum irule >> simp[EL_MEM]
QED

Theorem reachable_preds_all_reachable:
  (!bb. MEM bb fn.fn_blocks ==> fn_reachable fn bb.bb_label) ==>
  reachable_preds fn lbl =
    FILTER (\l. fn_cfg_edge fn l lbl) (MAP (\bb. bb.bb_label) fn.fn_blocks)
Proof
  strip_tac >> simp[reachable_preds_def] >>
  simp[FILTER_EQ, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED
