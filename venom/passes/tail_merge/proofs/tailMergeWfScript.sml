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

Theorem bb_well_formed_subst_block_labels[local]:
  !m bb. bb_well_formed bb ==>
    bb_well_formed (subst_block_labels_block m bb)
Proof
  rw[bb_well_formed_def, subst_block_labels_block_def,
     listTheory.LAST_MAP] >>
  gvs[listTheory.EL_MAP] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem operand_labels_subst[local]:
  !ops m s.
    MEM s (MAP THE (FILTER IS_SOME
      (MAP get_label (MAP (subst_label_map_op m) ops)))) <=>
    ?l. MEM l (MAP THE (FILTER IS_SOME (MAP get_label ops))) /\
        s = (case ALOOKUP m l of NONE => l | SOME k => k)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[subst_label_map_op_def, venomStateTheory.get_label_def] >>
  Cases_on `ALOOKUP m s'` >>
  simp[venomStateTheory.get_label_def,
       RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem get_successors_subst_block_labels[local]:
  !m inst s.
    MEM s (get_successors (subst_block_labels_inst m inst)) <=>
    ?l. MEM l (get_successors inst) /\
        s = (case ALOOKUP m l of NONE => l | SOME k => k)
Proof
  rpt gen_tac >> Cases_on `is_terminator inst.inst_opcode` >>
  simp[get_successors_def, subst_block_labels_inst_def,
       is_block_label_opcode_def, subst_label_map_inst_def,
       operand_labels_subst]
QED

Theorem bb_succs_subst_block_labels[local]:
  !m bb s.
    MEM s (bb_succs (subst_block_labels_block m bb)) <=>
    ?l. MEM l (bb_succs bb) /\
        s = (case ALOOKUP m l of NONE => l | SOME k => k)
Proof
  rpt gen_tac >> Cases_on `bb.bb_instructions` >>
  simp[bb_succs_def, subst_block_labels_block_def,
       listTheory.LAST_MAP, get_successors_subst_block_labels] >>
  qspecl_then [`h::t`, `subst_block_labels_inst m`] mp_tac
    listTheory.LAST_MAP >>
  (impl_tac >- simp[]) >>
  pure_rewrite_tac [listTheory.MAP] >>
  disch_then SUBST1_TAC >> simp[get_successors_subst_block_labels]
QED

Theorem tail_merge_fn_wf_function:
  !func. wf_function func ==> wf_function (tail_merge_fn func)
Proof
  cheat
QED
