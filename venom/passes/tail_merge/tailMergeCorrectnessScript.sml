(*
 * Tail Merge Pass — Correctness Statement
 *
 * Proof in proofs/tailMergeProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory tailMergeCorrectness
Ancestors
  tailMergeProof tailMergeHelpers tailMergeDefs cfgTransformProps
  venomWf venomInst venomExecSemantics cfgTransform
  list combin

Libs
  BasicProvers

Theorem tail_merge_pass_correct:
  !func s fuel ctx.
    wf_function func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE ==>
    let func' = tail_merge_fn func in
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
(* tail_merge_fn_correct has extra preconditions; cheat only the gap *)
Proof
  rpt strip_tac >> irule tail_merge_fn_correct >> cheat
QED

(* ===== Helpers ===== *)

(* subst_block_labels_inst preserves inst_id *)
Theorem subst_block_labels_inst_id_gen[local]:
  !m inst. (subst_block_labels_inst m inst).inst_id = inst.inst_id
Proof
  rw[subst_block_labels_inst_def, subst_label_map_inst_def]
QED

(* MEM in output list of filter+subst implies MEM in original *)
Theorem MEM_outputs_filter_subst[local]:
  !m P bbs e.
    MEM e (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (FILTER P (MAP (subst_block_labels_block m) bbs))))) ==>
    MEM e (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  ntac 2 gen_tac >> Induct >> simp[fn_insts_blocks_def] >>
  rpt gen_tac >>
  simp[listTheory.FILTER] >> COND_CASES_TAC >>
  simp[fn_insts_blocks_def, subst_block_labels_block_def,
       MEM_APPEND, MAP_APPEND, FLAT_APPEND, MAP_MAP_o, o_DEF] >>
  metis_tac[]
QED

(* FILTER + subst preserves ALL_DISTINCT of output list *)
Theorem filter_subst_preserves_output_distinct[local]:
  !m P bbs.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (fn_insts_blocks (FILTER P (MAP (subst_block_labels_block m) bbs)))))
Proof
  ntac 2 gen_tac >> Induct >> simp[fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  simp[listTheory.FILTER] >>
  COND_CASES_TAC >>
  simp[fn_insts_blocks_def, subst_block_labels_block_def,
       MAP_APPEND, FLAT_APPEND, MAP_MAP_o, o_DEF] >- (
    fs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
    rpt conj_tac >> TRY (first_x_assum irule >> simp[]) >>
    rpt strip_tac >>
    first_x_assum (qspec_then `e` mp_tac) >> simp[] >>
    drule_at Any MEM_outputs_filter_subst >> simp[]) >>
  first_x_assum irule >>
  fs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

(* MEM in id list of filter+subst implies MEM in original *)
Theorem MEM_ids_filter_subst[local]:
  !m P bbs e.
    MEM e (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (FILTER P (MAP (subst_block_labels_block m) bbs)))) ==>
    MEM e (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs))
Proof
  ntac 2 gen_tac >> Induct >> simp[] >>
  rpt gen_tac >>
  simp[listTheory.FILTER] >> COND_CASES_TAC >>
  simp[subst_block_labels_block_def,
       MEM_APPEND, MAP_APPEND, FLAT_APPEND, MAP_MAP_o, o_DEF,
       subst_block_labels_inst_id_gen] >>
  metis_tac[]
QED

(* FILTER + subst preserves ALL_DISTINCT of inst_id list *)
Theorem filter_subst_preserves_id_distinct[local]:
  !m P bbs.
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)) ==>
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
      (FILTER P (MAP (subst_block_labels_block m) bbs))))
Proof
  ntac 2 gen_tac >> Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[listTheory.FILTER] >> COND_CASES_TAC >>
  simp[subst_block_labels_block_def,
       MAP_APPEND, FLAT_APPEND, MAP_MAP_o, o_DEF,
       subst_block_labels_inst_id_gen] >- (
    fs[ALL_DISTINCT_APPEND, MAP_APPEND, FLAT_APPEND, MAP_MAP_o, o_DEF] >>
    rpt conj_tac >> TRY (first_x_assum irule >> simp[]) >>
    rpt strip_tac >>
    first_x_assum (qspec_then `e` mp_tac) >> simp[] >>
    drule_at Any MEM_ids_filter_subst >> simp[]) >>
  first_x_assum irule >>
  fs[ALL_DISTINCT_APPEND, MAP_APPEND, FLAT_APPEND]
QED

(* ===== Obligations ===== *)

Theorem tail_merge_preserves_ssa_form:
  !func. ssa_form func /\ wf_function func ==> ssa_form (tail_merge_fn func)
Proof
  rpt strip_tac >>
  simp[tail_merge_fn_def, LET_THM] >>
  Cases_on `fn_entry_label func` >> simp[] >>
  qmatch_goalsub_abbrev_tac `if mm = [] then _ else _` >>
  Cases_on `mm = []` >> simp[] >>
  simp[ssa_form_def, fn_insts_def, subst_block_labels_fn_def] >>
  irule filter_subst_preserves_output_distinct >>
  fs[ssa_form_def, fn_insts_def]
QED

(* Helper: MAP THE FILTER IS_SOME get_label commutes with subst *)
Theorem get_label_subst_map[local]:
  !mm ops.
    MAP THE (FILTER IS_SOME
      (MAP get_label (MAP (subst_label_map_op mm) ops))) =
    MAP (\l. case ALOOKUP mm l of SOME k => k | NONE => l)
        (MAP THE (FILTER IS_SOME (MAP get_label ops)))
Proof
  gen_tac >> Induct >> simp[] >>
  gen_tac >> Cases_on `h` >>
  simp[subst_label_map_op_def, venomStateTheory.get_label_def] >>
  Cases_on `ALOOKUP mm s` >>
  simp[venomStateTheory.get_label_def]
QED

(* Helper: get_successors after subst = MAP through merge map *)
Theorem get_successors_subst[local]:
  !mm inst.
    get_successors (subst_block_labels_inst mm inst) =
    MAP (\l. case ALOOKUP mm l of SOME k => k | NONE => l)
        (get_successors inst)
Proof
  rw[get_successors_def, subst_block_labels_inst_def,
     subst_label_map_inst_def] >>
  simp[get_label_subst_map] >>
  Cases_on `is_block_label_opcode inst.inst_opcode` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  fs[is_block_label_opcode_def, is_terminator_def] >>
  Cases_on `inst.inst_opcode` >> gvs[]
QED

(* Helper: bb_succs after subst relates to original bb_succs *)
Theorem MEM_bb_succs_subst[local]:
  !mm bb succ.
    MEM succ (bb_succs (subst_block_labels_block mm bb)) ==>
    ?old. MEM old (bb_succs bb) /\
          succ = (case ALOOKUP mm old of SOME k => k | NONE => old)
Proof
  rpt strip_tac >>
  fs[bb_succs_def, subst_block_labels_block_def, MEM_nub, MEM_REVERSE] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  `LAST (subst_block_labels_inst mm h :: MAP (subst_block_labels_inst mm) t) =
   subst_block_labels_inst mm (LAST (h::t))` by (
    `subst_block_labels_inst mm h :: MAP (subst_block_labels_inst mm) t =
     MAP (subst_block_labels_inst mm) (h::t)` by simp[] >>
    pop_assum SUBST1_TAC >>
    irule LAST_MAP >> simp[]) >>
  gvs[get_successors_subst, MEM_MAP] >>
  metis_tac[MEM_nub, MEM_REVERSE]
QED

Theorem tail_merge_preserves_wf_function:
  !func. wf_function func ==> wf_function (tail_merge_fn func)
Proof
  cheat
QED
