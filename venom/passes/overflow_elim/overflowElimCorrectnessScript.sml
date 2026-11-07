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
  rpt strip_tac >>
  REWRITE_TAC[BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_function_eq)] >>
  irule clear_nops_run_function_sim >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
  >~ [`wf_function _`] >- metis_tac[overflow_elim_analysis_transform_wf_ssa]
  >~ [`fn_entry_label _ = fn_entry_label _`]
  >- simp[fmt_preserves_entry_label, analysis_function_transform_widen_def,
          analysis_block_transform_widen_def] >>
  irule overflow_elim_function_sim >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ===== Obligations ===== *)

Theorem overflow_elim_preserves_ssa_form:
  ∀fn. wf_function fn ∧ ssa_form fn ⇒ ssa_form (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  REWRITE_TAC[BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_function_eq)] >>
  irule clear_nops_function_preserves_ssa >>
  metis_tac[overflow_elim_analysis_transform_wf_ssa]
QED

Theorem overflow_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (overflow_elim_function fn)
Proof
  rpt strip_tac >>
  REWRITE_TAC[BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_function_eq)] >>
  irule clear_nops_function_preserves_wf >>
  metis_tac[overflow_elim_analysis_transform_wf_ssa]
QED
