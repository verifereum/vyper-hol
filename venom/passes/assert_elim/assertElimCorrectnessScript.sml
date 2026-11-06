(*
 * Assert Elimination — Correctness Statement
 *
 * TOP-LEVEL:
 *   assert_elim_function_correct  — main correctness: assert elimination preserves
 *                                   function semantics (error or equivalent results)
 *   assert_elim_preserves_ssa_form — assert elimination preserves SSA form
 *   assert_elim_preserves_wf_function — assert elimination preserves well-formedness
 *
 * The proofs are in assertElimProofs.
 *)

Theory assertElimCorrectness
Ancestors
  assertElimProofs
  assertElimDefs
  analysisSimDefs
  indexedLists
  passSharedDefs
  passSharedProps
  passSimulationDefs
  passSimulationProps
  rangeAnalysisProofs
  venomExecSemantics
  venomInst
  venomWf
Libs
  BasicProvers

(* Running assert elimination on a well-formed, SSA, DFG-sound function either
   causes both original and transformed executions to error, or produces
   equivalent results (states and execution traces match). *)
Theorem assert_elim_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\ dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb cond true_lbl false_lbl.
      MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u.
      dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
      vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
      MEM (Var u) dinst.inst_operands ==>
      u IN FDOM s.vs_vars) /\
    range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assert_elim_function fn) s)
Proof
  rpt strip_tac >>
  `fn.fn_blocks <> []` by fs[wf_function_def, fn_has_entry_def] >>
  `fn_entry_label (assert_elim_function fn) = fn_entry_label fn` by
    (pop_assum mp_tac >> ntac 12 (pop_assum kall_tac) >>
     simp[fn_entry_label_def, entry_block_def, assert_elim_function_def,
          clear_nops_function_def, analysis_function_transform_widen_def,
          function_map_transform_def, clear_nops_block_def,
          analysis_block_transform_widen_def, LET_THM,
          listTheory.NULL_EQ, rich_listTheory.MAP_HD, listTheory.MAP_EQ_NIL]) >>
  once_rewrite_tac[run_function_def] >> simp[] >>
  `s with vs_current_bb := s.vs_current_bb = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule assert_elim_function_correct_proof >>
  metis_tac[]
QED

(* ===== Obligations ===== *)

(* A well-formed function in SSA form remains in SSA form after assert elimination. *)
Theorem assert_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (assert_elim_function fn)
Proof
  rpt strip_tac >> simp[assert_elim_function_def] >>
  irule clear_nops_function_preserves_ssa >>
  irule assert_elim_analysis_transform_ssa >> fs[]
QED

(* A well-formed function remains well-formed after assert elimination. *)
Theorem assert_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (assert_elim_function fn)
Proof
  rpt strip_tac >> simp[assert_elim_function_def] >>
  irule clear_nops_function_preserves_wf >>
  irule assert_elim_analysis_transform_wf >> fs[]
QED
