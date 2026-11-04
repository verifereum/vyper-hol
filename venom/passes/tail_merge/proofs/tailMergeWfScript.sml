(*
 * Tail Merge Pass — ssa_form and wf_function preservation
 *
 * The pass rewrites label operands of terminators and PHIs, then drops the
 * merged blocks; instruction outputs and ids are unchanged, so the
 * transformed function's instructions are a sublist of the original's.
 *)

Theory tailMergeWf
Ancestors
  tailMergeMap tailMergeHelpers tailMergeDefs cfgTransform venomInst venomWf

(* Outputs of the kept, substituted blocks: distinct, and among the
   original outputs *)
Theorem outputs_filter_subst[local]:
  !P m bbs.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (FILTER P (MAP (subst_block_labels_block m) bbs))))) /\
    !x. MEM x (FLAT (MAP (\i. i.inst_outputs)
          (fn_insts_blocks (FILTER P (MAP (subst_block_labels_block m) bbs))))) ==>
        MEM x (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  gen_tac >> gen_tac >> Induct >>
  simp[fn_insts_blocks_def] >> rpt gen_tac >> strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND] >>
  IF_CASES_TAC >>
  gvs[fn_insts_blocks_def, listTheory.ALL_DISTINCT_APPEND, subst_block_labels_block_def,
      listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  metis_tac[]
QED

Theorem tail_merge_fn_ssa_form:
  !func. ssa_form func ==> ssa_form (tail_merge_fn func)
Proof
  rw[tail_merge_fn_def] >> Cases_on `fn_entry_label func` >> simp[] >>
  rw[] >> gvs[ssa_form_def, fn_insts_def, subst_block_labels_fn_def] >>
  metis_tac[outputs_filter_subst]
QED

Theorem tail_merge_fn_wf_function:
  !func. wf_function func ==> wf_function (tail_merge_fn func)
Proof
  cheat
QED
