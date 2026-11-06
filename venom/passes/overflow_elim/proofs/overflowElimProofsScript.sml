(*
 * Overflow Check Elimination — Main Proofs
 *
 * overflow_elim_function_sim lifts the per-instruction simulation
 * overflow_elim_sim_pw through range_pass_correct, with the within-block
 * invariant dfg_prefix_sound plus the chain closure.  Used by
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
   Within-block invariant
   ================================================================ *)

Triviality step_assign_output_in_fdom[local]:
  !inst s s' out.
    inst.inst_opcode = ASSIGN /\
    step_inst_base inst s = OK s' /\
    inst.inst_outputs = [out] ==>
    out IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `eval_operand h s` >>
  simp[update_var_def, FDOM_FUPDATE] >> strip_tac >>
  gvs[FDOM_FUPDATE]
QED

Triviality step_iszero_output_in_fdom[local]:
  !inst s s' out.
    inst.inst_opcode = ISZERO /\
    step_inst_base inst s = OK s' /\
    inst.inst_outputs = [out] ==>
    out IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[step_inst_base_def, exec_pure1_def] >>
  Cases_on `t` >> gvs[step_inst_base_def, exec_pure1_def] >>
  Cases_on `eval_operand h s` >> gvs[update_var_def, FDOM_FUPDATE]
QED

val tracked_pure2_output_finish_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[exec_pure2_def] >>
  Cases_on `t` >> simp[exec_pure2_def] >>
  Cases_on `t'` >> simp[exec_pure2_def] >>
  Cases_on `eval_operand h s` >> simp[exec_pure2_def] >>
  Cases_on `eval_operand h' s` >>
  simp[update_var_def, FDOM_FUPDATE] >> strip_tac >>
  gvs[FDOM_FUPDATE];

Triviality step_pure2_output_in_fdom[local]:
  !inst s s' out.
    (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/
     inst.inst_opcode = GT \/ inst.inst_opcode = SLT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = ADD \/
     inst.inst_opcode = SUB) /\
    step_inst_base inst s = OK s' /\
    inst.inst_outputs = [out] ==>
    out IN FDOM s'.vs_vars
Proof
  rpt strip_tac >> gvs[]
  >- tracked_pure2_output_finish_tac
  >- tracked_pure2_output_finish_tac
  >- tracked_pure2_output_finish_tac
  >- tracked_pure2_output_finish_tac
  >- tracked_pure2_output_finish_tac
  >- tracked_pure2_output_finish_tac
  >- tracked_pure2_output_finish_tac
QED

(* Helper: after executing a tracked opcode, the output variable is in FDOM *)
Triviality step_tracked_output_in_fdom[local]:
  !fuel ctx inst s s' out.
    step_inst fuel ctx inst s = OK s' /\
    dfg_tracked_opcode inst.inst_opcode /\
    inst.inst_outputs = [out] ==>
    out IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  imp_res_tac tracked_step_inst_base >>
  qpat_x_assum `dfg_tracked_opcode _`
    (strip_assume_tac o REWRITE_RULE[dfg_tracked_opcode_def]) >>
  gvs[]
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_assign_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_iszero_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
  >- (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
        step_pure2_output_in_fdom) >> simp[])
QED

Triviality oe_nonterm_pres[local]:
  !dfg v inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (overflow_elim_inst_v dfg v inst).inst_opcode
Proof
  rpt gen_tac >> disch_tac >>
  simp[overflow_elim_inst_v_def] >>
  rpt IF_CASES_TAC >> simp[mk_nop_inst_def, is_terminator_def]
QED

Triviality oe_not_phi_pres[local]:
  !dfg v inst. inst.inst_opcode <> PHI ==>
    (overflow_elim_inst_v dfg v inst).inst_opcode <> PHI
Proof
  rpt gen_tac >> strip_tac >>
  simp[overflow_elim_inst_v_def] >>
  rpt IF_CASES_TAC >> simp[mk_nop_inst_def]
QED

Triviality oe_inst_id[local]:
  !dfg v inst. (overflow_elim_inst_v dfg v inst).inst_id = inst.inst_id
Proof
  rpt gen_tac >> simp[overflow_elim_inst_v_def] >>
  rpt IF_CASES_TAC >> simp[mk_nop_inst_def]
QED

Triviality oe_terminator_identity[local]:
  !dfg v inst. is_terminator inst.inst_opcode ==>
    overflow_elim_inst_v dfg v inst = inst
Proof
  rpt strip_tac >> simp[overflow_elim_inst_v_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  gvs[is_terminator_def]
QED

Triviality oe_phi_pres[local]:
  !dfg v inst. inst.inst_opcode = PHI ==>
    (overflow_elim_inst_v dfg v inst).inst_opcode = PHI
Proof
  simp[overflow_elim_inst_v_def]
QED

Triviality oe_outputs[local]:
  !dfg v inst.
    (overflow_elim_inst_v dfg v inst).inst_outputs = inst.inst_outputs \/
    (overflow_elim_inst_v dfg v inst).inst_outputs = []
Proof
  rw[overflow_elim_inst_v_def, mk_nop_inst_def]
QED

(* chain closure extends by one step *)
Triviality nonterm_chain_closure[local]:
  !fn bb st s1 fuel ctx.
    (!chain_v chain_inst k.
       dfg_get_def (dfg_build_function fn) chain_v = SOME chain_inst /\
       dfg_tracked_opcode chain_inst.inst_opcode /\
       k < st.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
       EL k bb.bb_instructions = chain_inst ==>
       chain_v IN FDOM st.vs_vars) /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode /\
    MEM bb fn.fn_blocks /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) ==>
    (!chain_v chain_inst k.
       dfg_get_def (dfg_build_function fn) chain_v = SOME chain_inst /\
       dfg_tracked_opcode chain_inst.inst_opcode /\
       k < SUC st.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
       EL k bb.bb_instructions = chain_inst ==>
       chain_v IN FDOM s1.vs_vars)
Proof
  rpt strip_tac >> qpat_x_assum `EL _ _ = chain_inst` (SUBST_ALL_TAC o SYM) >>
  Cases_on `k < st.vs_inst_idx`
  >| [
    (* k < st.vs_inst_idx: variable preserved across step *)
    `chain_v IN FDOM st.vs_vars` by metis_tac[] >>
    `MEM chain_v (EL k bb.bb_instructions).inst_outputs` by
      (imp_res_tac dfg_build_function_correct >>
       metis_tac[dfg_tracked_inst_outputs]) >>
    `k <> st.vs_inst_idx` by DECIDE_TAC >>
    `~MEM chain_v (EL st.vs_inst_idx bb.bb_instructions).inst_outputs` by
      metis_tac[block_ssa_disjoint_outputs] >>
    `lookup_var chain_v s1 = lookup_var chain_v st` by
      metis_tac[step_preserves_non_output_vars] >>
    `?w. FLOOKUP st.vs_vars chain_v = SOME w` by
      metis_tac[FDOM_FLOOKUP] >>
    gvs[lookup_var_def] >>
    metis_tac[FDOM_FLOOKUP],
    (* k = st.vs_inst_idx: variable produced by this step *)
    `k = st.vs_inst_idx` by DECIDE_TAC >> rw[] >>
    `(EL st.vs_inst_idx bb.bb_instructions).inst_outputs = [chain_v]` by
      metis_tac[dfg_tracked_inst_outputs] >>
    metis_tac[step_tracked_output_in_fdom]
  ]
QED

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
        dfg_prefix_sound (dfg_build_function fn) bb t.vs_vars idx /\
        !chain_v chain_inst k.
          dfg_get_def (dfg_build_function fn) chain_v = SOME chain_inst /\
          dfg_tracked_opcode chain_inst.inst_opcode /\
          k < idx /\ k < LENGTH bb.bb_instructions /\
          EL k bb.bb_instructions = chain_inst ==>
          chain_v IN FDOM t.vs_vars``,
    ``\v inst. overflow_elim_inst_v (dfg_build_function fn)
                 (range_unwrap v) inst``] range_pass_correct)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- ACCEPT_TAC (ISPEC ``dfg_build_function fn`` overflow_elim_inst_structural)
      (* entry: nothing tracked lies in the PHI prefix *)
      >- (rpt gen_tac >> strip_tac >> conj_tac
          >- simp[dfg_prefix_sound_phi_prefix] >>
          rpt strip_tac >>
          `(EL k bb.bb_instructions).inst_opcode = PHI` by
            metis_tac[phi_prefix_length_el_phi] >>
          gvs[dfg_tracked_opcode_def])
      (* step *)
      >- (rpt gen_tac >> strip_tac >> conj_tac
          >- (mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`, `t`, `t'`]
                dfg_prefix_sound_step) >>
              impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
              simp[]) >>
          qpat_x_assum `t.vs_inst_idx = idx` (SUBST_ALL_TAC o SYM) >>
          mp_tac (Q.SPECL [`fn`, `bb`, `t`, `t'`, `fuel`, `ctx`]
            nonterm_chain_closure) >>
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
  impl_tac >- (fs[dfg_ext_sound_def] >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem overflow_elim_analysis_transform_wf:
  !fn. wf_function fn ==>
    wf_function
      (analysis_function_transform_widen NONE (range_analyze fn)
        (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                     (range_unwrap v) inst]) fn)
Proof
  rpt strip_tac >>
  qspecl_then
    [`NONE : range_state option`, `range_analyze fn`,
     `\v inst. overflow_elim_inst_v (dfg_build_function fn) (range_unwrap v) inst`,
     `fn`]
    (fn th => REWRITE_TAC[BETA_RULE th]) aftw_singleton_eq_fmt_mapi >>
  mp_tac (Q.SPECL
    [`\bb idx inst. overflow_elim_inst_v (dfg_build_function fn)
        (range_unwrap (df_widen_at NONE (range_analyze fn) bb.bb_label idx)) inst`,
     `fn`] passSimulationPropsTheory.mapi_transform_preserves_wf_bb) >>
  simp[oe_inst_id, oe_terminator_identity, oe_nonterm_pres,
       oe_phi_pres, oe_not_phi_pres]
QED

Theorem overflow_elim_analysis_transform_ssa:
  !fn. wf_function fn /\ ssa_form fn ==>
    ssa_form
      (analysis_function_transform_widen NONE (range_analyze fn)
        (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                     (range_unwrap v) inst]) fn)
Proof
  rpt strip_tac >>
  qspecl_then
    [`NONE : range_state option`, `range_analyze fn`,
     `\v inst. overflow_elim_inst_v (dfg_build_function fn) (range_unwrap v) inst`,
     `fn`]
    (fn th => REWRITE_TAC[BETA_RULE th]) aftw_singleton_eq_fmt_mapi >>
  mp_tac (Q.SPECL
    [`\bb idx inst. overflow_elim_inst_v (dfg_build_function fn)
        (range_unwrap (df_widen_at NONE (range_analyze fn) bb.bb_label idx)) inst`,
     `fn`] mapi_transform_preserves_ssa_bb) >>
  simp[oe_inst_id, oe_outputs]
QED
