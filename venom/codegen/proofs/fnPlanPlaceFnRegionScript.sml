Theory fnPlanPlaceFnRegion
Ancestors
  stackPlanGen callLayoutDefs venomInst stackPlanTypes list

Theorem generate_block_plan_leading_label:
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops, ps') ==>
  ?tail. ops = SOLabel bb.bb_label :: tail
Proof
  simp[generate_block_plan_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem generate_fn_plan_with_cleanup_analyzed_leading_label:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn spill_base ctr =
    SOME (ops, ps') ==>
  ?tail. ops = SOLabel (HD fn.fn_blocks).bb_label :: tail
Proof
  Cases_on `fn.fn_blocks` >-
    simp[generate_fn_plan_with_cleanup_analyzed_def, canonical_param_prefix_def] >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, fn_entry_label_def,
       entry_block_def] >>
  simp[Once generate_fn_plan_aux_def, lookup_block_def, FIND_thm] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule generate_block_plan_leading_label >> strip_tac >> gvs[]
QED
