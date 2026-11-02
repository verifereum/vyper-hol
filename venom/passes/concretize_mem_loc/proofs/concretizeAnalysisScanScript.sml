Theory concretizeAnalysisScan
Ancestors concretizeAnalysisBoundary basePtrDefs execEquivParamBase allocaRemapSSA
  list pred_set venomInst pair

Definition bp_scan_insts_def:
  bp_scan_insts fn [] = [] /\
  bp_scan_insts fn (lbl::ls) =
    (case FIND (\bb. bb.bb_label = lbl) fn.fn_blocks of
       NONE => [] | SOME bb => bb.bb_instructions) ++ bp_scan_insts fn ls
End

Theorem bp_process_block_append:
  !xs r ys. bp_process_block r (xs ++ ys) =
    (FST (bp_process_block r xs) \/
       FST (bp_process_block (SND (bp_process_block r xs)) ys),
     SND (bp_process_block (SND (bp_process_block r xs)) ys))
Proof
  Induct >> simp[bp_process_block_def] >> rpt gen_tac >>
  Cases_on `bp_handle_inst r h` >> simp[] >>
  rename1 `bp_handle_inst r h = (c,r1)` >>
  Cases_on `bp_process_block r1 xs` >> simp[DISJ_ASSOC]
QED

Theorem bp_one_pass_scan:
  !order r. bp_one_pass fn order r =
    bp_process_block r (bp_scan_insts fn order)
Proof
  Induct >> simp[bp_one_pass_def, bp_one_pass_aux_def, bp_scan_insts_def,
                 bp_process_block_def] >>
  rpt gen_tac >> Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >>
  gvs[bp_one_pass_def, bp_process_block_append, bp_process_block_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem bp_scan_insts_member:
  !order i. MEM i (bp_scan_insts fn order) ==> MEM i (fn_insts fn)
Proof
  Induct >> simp[bp_scan_insts_def] >> rpt gen_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> simp[] >>
  metis_tac[FIND_MEM, mem_fn_insts_intro]
QED
