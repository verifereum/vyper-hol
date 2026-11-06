(*
 * Overflow Check Elimination — Correctness Statement
 *)

Theory overflowElimCorrectness
Ancestors
  overflowElimProofs venomWf
  overflowElimDefs overflowElimHelpers overflowElimHelpers2
  passSharedDefs passSimulationProps passSharedProps
  passSimulationDefs venomInst dfgDefs
  rangeAnalysisDefs dfAnalyzeWidenDefs stateEquiv
  rangePassProofs analysisSimDefs analysisSimProps stateEquivProps venomExecSemantics venomState venomInstProps venomExecProps execEquivParamProps rangeEvalDefs valueRangeDefs rangeAnalysisProofs dfgAnalysisProps dfgSoundDefs dfgSoundProofs worklistDefs list finite_map indexedLists

Libs
  BasicProvers

(* Lift clear_nops_function_correct from run_blocks to run_function *)
Triviality fn_entry_label_clear_nops[local]:
  !fn. fn_entry_label (clear_nops_function fn) = fn_entry_label fn
Proof
  gen_tac >> simp[fn_entry_label_def, entry_block_def,
    clear_nops_function_def, listTheory.NULL_EQ, listTheory.MAP_EQ_NIL] >>
  Cases_on `fn.fn_blocks` >> simp[clear_nops_block_def]
QED

Triviality clear_nops_function_correct_run_function[local]:
  !fuel ctx fn s.
    wf_function fn /\ s.vs_inst_idx = 0 ==>
    result_equiv {} (run_function fuel ctx fn s)
      (run_function fuel ctx (clear_nops_function fn) s)
Proof
  rpt strip_tac >>
  simp[run_function_def, fn_entry_label_clear_nops] >>
  Cases_on `fn_entry_label fn`
  >- simp[result_equiv_def]
  >> simp_tac std_ss [GSYM result_equiv_is_lift_result] >>
  irule passSharedPropsTheory.clear_nops_function_correct >>
  simp[]
QED

(* Helper: run_function = run_blocks when fn_entry_label known *)
Triviality run_function_is_run_blocks[local]:
  fn_entry_label fn = SOME s.vs_current_bb /\ s.vs_inst_idx = 0 ==>
  run_function fuel ctx fn s = run_blocks fuel ctx fn s
Proof
  strip_tac >> simp[run_function_def] >>
  Cases_on `s` >> gvs[venom_state_fn_updates]
QED

(* Helper: fn_entry_label preserved by function_map_transform when bt preserves label *)
Triviality fn_entry_label_function_map_transform[local]:
  (!bb. (bt bb).bb_label = bb.bb_label) ==>
  fn_entry_label (function_map_transform bt fn) = fn_entry_label fn
Proof
  strip_tac >>
  simp[fn_entry_label_def, entry_block_def, function_map_transform_def,
       listTheory.NULL_EQ, listTheory.MAP_EQ_NIL] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Theorem overflow_elim_function_correct:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    assert_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
    range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (overflow_elim_function fn) s)
Proof
  rpt strip_tac
  \\ REWRITE_TAC[BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_function_eq)]
  \\ mp_tac (Q.SPECL [`fn`, `fuel`, `ctx`, `s`] overflow_elim_function_sim)
  \\ impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  \\ qmatch_goalsub_abbrev_tac `clear_nops_function aft`
  \\ `fn_entry_label aft = fn_entry_label fn` by
       simp[Abbr `aft`, fn_entry_label_function_map_transform,
            analysis_function_transform_widen_def,
            analysis_block_transform_widen_def]
  \\ `run_function fuel ctx fn s = run_blocks fuel ctx fn s` by
       (irule run_function_is_run_blocks >> conj_tac >> first_assum ACCEPT_TAC)
  \\ `run_function fuel ctx aft s = run_blocks fuel ctx aft s` by
       (irule run_function_is_run_blocks >> metis_tac[])
  \\ strip_tac
  >- (DISJ1_TAC >> metis_tac[])
  \\ DISJ2_TAC
  \\ irule lift_result_trans
  \\ conj_tac >- metis_tac[state_equiv_trans]
  \\ conj_tac >- metis_tac[execution_equiv_trans]
  \\ qexists_tac `run_function fuel ctx aft s`
  \\ conj_tac
  >- (qpat_x_assum `run_function _ _ fn _ = _` SUBST1_TAC >>
      qpat_x_assum `run_function _ _ aft _ = _` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  \\ simp_tac std_ss [GSYM result_equiv_is_lift_result]
  \\ irule clear_nops_function_correct_run_function
  \\ conj_tac >- simp[Abbr `aft`, overflow_elim_analysis_transform_wf]
  \\ first_assum ACCEPT_TAC
QED

(* ===== Obligations ===== *)

Theorem overflow_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  REWRITE_TAC[BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_function_eq)] >>
  irule clear_nops_function_preserves_ssa >>
  irule overflow_elim_analysis_transform_ssa >> fs[]
QED

Theorem overflow_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  REWRITE_TAC[BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_function_eq)] >>
  irule clear_nops_function_preserves_wf >>
  irule overflow_elim_analysis_transform_wf >> fs[]
QED
