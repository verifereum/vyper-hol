(*
 * Overflow Check Elimination — Main Proofs
 *
 * overflow_elim_function_sim lifts the per-instruction simulation
 * overflow_elim_sim_pw through range_pass_correct, with the within-block
 * invariant dfg_prefix_sound.  Used by
 * overflowElimCorrectness.overflow_elim_function_correct.
 *)

Theory overflowElimProofs
Ancestors
  overflowElimHelpers2
  overflowElimHelpers
  overflowElimDefs
  rangePassProofs
  analysisSimDefs
  analysisSimProps
  passSimulationDefs
  passSimulationProps
  passSharedDefs
  passSharedProps
  stateEquiv
  stateEquivProps
  venomExecSemantics
  venomState
  venomInst
  venomWf
  venomInstProps
  venomExecProofs
  venomExecProps
  execEquivParamProps
  rangeAnalysisDefs
  rangeEvalDefs
  valueRangeDefs
  rangeAnalysisProofs
  dfAnalyzeWidenDefs
  dfgDefs
  dfgAnalysisProps
  dfgSoundDefs
  dfgSoundProofs
  worklistDefs
  list
  finite_map
  indexedLists

val _ = temp_delsimps ["dfg_block_local_def", "dfg_tracked_opcode_def"];

(* ================================================================
   Function-level correctness
   ================================================================ *)

Theorem overflow_elim_inst_structural[local]:
  !dfg. inst_transform_structural_1
          (\v inst. overflow_elim_inst_v dfg (range_unwrap v) inst)
Proof
  rw[inst_transform_structural_1_def, overflow_elim_inst_v_def] >>
  BasicProvers.every_case_tac >> gvs[mk_nop_inst_def, is_terminator_def]
QED

Theorem overflow_elim_function_sim:
  !fn fuel ctx s.
    wf_function fn /\ fn_inst_wf fn /\
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
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx
        (analysis_function_transform_widen NONE (range_analyze fn)
          (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                       (range_unwrap v) inst]) fn) s)
Proof
  rpt strip_tac >>
  mp_tac (BETA_RULE (ISPECL [``fn : ir_function``,
    ``\bb idx (t:venom_state).
        dfg_prefix_sound (dfg_build_function fn) bb t.vs_vars idx``,
    ``\v inst. overflow_elim_inst_v (dfg_build_function fn)
                 (range_unwrap v) inst``] range_pass_correct)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- ACCEPT_TAC (ISPEC ``dfg_build_function fn`` overflow_elim_inst_structural)
      (* entry: nothing tracked lies in the PHI prefix *)
      >- simp[dfg_prefix_sound_phi_prefix]
      (* step *)
      >- (rpt gen_tac >> strip_tac >>
          mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`, `t`, `t'`]
            dfg_prefix_sound_step) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          simp[])
      (* per-instruction simulation *)
      >> rpt gen_tac >> strip_tac >>
      mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_sim_pw)) >>
      disch_then (qspecl_then [`fn`, `bb`, `idx`,
        `df_widen_at NONE (range_analyze fn) bb.bb_label idx`, `fuel`, `ctx`,
        `EL idx bb.bb_instructions`, `t`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          fs[fn_inst_wf_def] >> first_x_assum irule >> metis_tac[MEM_EL]) >>
      disch_then ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      fs[dfg_ext_sound_def, dfg_sound_def] >> rpt strip_tac >> res_tac >>
      fs[dfg_entry_sound_def]) >>
  disch_then ACCEPT_TAC
QED

Theorem overflow_elim_analysis_transform_wf_ssa:
  !fn.
    (wf_function fn ==>
     wf_function
       (analysis_function_transform_widen NONE (range_analyze fn)
         (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                      (range_unwrap v) inst]) fn)) /\
    (wf_function fn /\ ssa_form fn ==>
     ssa_form
       (analysis_function_transform_widen NONE (range_analyze fn)
         (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                      (range_unwrap v) inst]) fn))
Proof
  gen_tac >> irule (BETA_RULE (Q.ISPEC
    `\v inst. overflow_elim_inst_v (dfg_build_function fn) (range_unwrap v) inst`
    nop_transform_preserves_wf_ssa)) >>
  simp[overflow_elim_inst_structural] >>
  rw[overflow_elim_inst_v_def]
QED

