(*
 * Overflow Check Elimination — Main Proofs
 *
 * Depends on overflowElimHelpers for all DFG soundness infrastructure.
 * This file contains: entry_transfer, operand_flookup, dfg_prefix_sound_step,
 * overflow_elim_block_sim, overflow_elim_function_sim, and the final theorem.
 *)

Theory overflowElimProofs
Ancestors
  overflowElimHelpers2
  overflowElimHelpers
  overflowElimDefs
  assertElimProofs
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
  venomExecProps
  execEquivParamProps
  rangeAnalysisDefs
  rangeEvalDefs
  valueRangeDefs
  variableRangeAnalysisProps
  rangeAnalysisProofs
  dfAnalyzeWidenDefs
  dfgDefs
  dfgAnalysisProps
  dfgSoundStep
  worklistDefs
  list
  finite_map
  indexedLists

val _ = temp_delsimps ["dfg_block_local_def", "dfg_tracked_opcode_def"];

(* ================================================================
   Per-block simulation
   ================================================================ *)

(* Helper: the transformed block has the same length as the original *)
Triviality bt_length[local]:
  !ra dfg bb.
    let bt = analysis_block_transform_widen NONE ra
               (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) in
    LENGTH (bt bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rpt gen_tac >> simp[analysis_block_transform_widen_def, FLAT_MAPi_SING] >>
  simp[LENGTH_MAPi]
QED

(* Helper: the transformed block instruction at index idx *)
Triviality bt_el[local]:
  !ra dfg bb idx.
    let bt = analysis_block_transform_widen NONE ra
               (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) in
    idx < LENGTH bb.bb_instructions ==>
    EL idx (bt bb).bb_instructions =
      overflow_elim_inst_v dfg
        (range_unwrap (df_widen_at NONE ra bb.bb_label idx))
        (EL idx bb.bb_instructions)
Proof
  rpt strip_tac >> simp[analysis_block_transform_widen_def, FLAT_MAPi_SING] >>
  simp[EL_MAPi]
QED

(* Helper: the transformed block preserves label *)
Triviality bt_label[local]:
  !ra dfg bb.
    let bt = analysis_block_transform_widen NONE ra
               (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) in
    (bt bb).bb_label = bb.bb_label
Proof
  simp[analysis_block_transform_widen_def]
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
  gvs[step_inst_base_def, exec_pure1_def, exec_pure2_def,
      AllCaseEqs(), update_var_def, FDOM_FUPDATE]
QED

Triviality state_equiv_empty_eq[local]:
  !s1 s2. state_equiv {} s1 s2 ==> (s1 = s2)
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  Cases_on `s1` >> Cases_on `s2` >> gvs[] >>
  fs[fmap_eq_flookup, lookup_var_def]
QED

Triviality lift_result_OK_left[local]:
  !R_ok R_term s1 r2.
    lift_result R_ok R_term R_term (OK s1) r2 ==> ?s2. r2 = OK s2 /\ R_ok s1 s2
Proof
  rpt gen_tac >> Cases_on `r2` >> simp[lift_result_def]
QED

Triviality lift_result_nonOK[local]:
  !R_ok R_term r1 r2.
    lift_result R_ok R_term R_term r1 r2 /\ (!s. r1 <> OK s) ==> (!s. r2 <> OK s)
Proof
  rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def]
QED

Triviality oe_is_terminator_pres:
  !dfg v inst. is_terminator inst.inst_opcode ==>
    is_terminator (overflow_elim_inst_v dfg v inst).inst_opcode
Proof
  rpt strip_tac >>
  simp[overflow_elim_inst_v_def] >>
  rpt IF_CASES_TAC >> simp[] >>
  gvs[is_terminator_def]
QED

Triviality oe_nonterm_pres:
  !dfg v inst. ~is_terminator inst.inst_opcode ==>
    ~is_terminator (overflow_elim_inst_v dfg v inst).inst_opcode
Proof
  rpt gen_tac >> disch_tac >>
  simp[overflow_elim_inst_v_def] >>
  rpt IF_CASES_TAC >> simp[mk_nop_inst_def, is_terminator_def]
QED

(* exec_block passes non-OK step results through directly *)
Triviality exec_block_nonOK_passthrough[local]:
  !fuel ctx bb st r.
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = r /\
    (!s. r <> OK s) ==>
    exec_block fuel ctx bb st = r
Proof
  rpt strip_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `r` >> gvs[]
QED

(* exec_block on terminator OK = halted/continue result *)
Triviality exec_block_terminator_OK:
  !fuel ctx bb st s1.
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    exec_block fuel ctx bb st =
      if s1.vs_halted then Halt s1 else OK s1
Proof
  rpt strip_tac >> simp[Once exec_block_def, get_instruction_def]
QED

(* exec_block on non-terminator OK = continuation *)
Triviality exec_block_nonterm_OK:
  !fuel ctx bb st s1.
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    ~is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    exec_block fuel ctx bb st =
      exec_block fuel ctx bb (s1 with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  rpt strip_tac >> simp[Once exec_block_def, get_instruction_def]
QED

(* Helper: after one non-terminator step, dfg_prefix_sound, range_sound, and
   chain closure all transfer from idx to SUC idx *)
(* range_sound ignores vs_inst_idx *)
Triviality range_sound_inst_idx:
  !X n s. range_sound X (s with vs_inst_idx := n) = range_sound X s
Proof
  rw[range_sound_def] >> Cases_on `X` >> simp[]
QED

(* range_sound transfers through one non-terminator step *)
Triviality nonterm_range_transfer[local]:
  !fn bb st s1 fuel ctx.
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label st.vs_inst_idx) st /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    ALL_DISTINCT (fn_labels fn) /\
    wf_function fn ==>
    range_sound
      (df_widen_at NONE (range_analyze fn) bb.bb_label (SUC st.vs_inst_idx))
      (s1 with vs_inst_idx := SUC st.vs_inst_idx)
Proof
  rpt strip_tac >>
  REWRITE_TAC [range_sound_inst_idx] >>
  mp_tac (Q.SPECL [`fn`, `bb.bb_label`, `bb`, `st.vs_inst_idx`]
            range_intra_transfer) >>
  (impl_tac >- (
    simp[] >> metis_tac[MEM_lookup_block, fn_labels_def])) >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  mp_tac (ISPECL [``range_sound``,
    ``range_transfer_opt``,
    ``(dfg_build_function fn, fn.fn_blocks)``]
    transfer_sound_step) >>
  disch_then (qspecl_then [`EL st.vs_inst_idx bb.bb_instructions`,
    `fuel`, `ctx`, `st`, `s1`,
    `df_widen_at NONE (range_analyze fn) bb.bb_label st.vs_inst_idx`] mp_tac) >>
  simp[range_transfer_sound]
QED

(* chain closure extends by one step *)
Triviality nonterm_chain_closure[local]:
  !fn bb st s1 fuel ctx.
    (!chain_v k.
       dfg_get_def (dfg_build_function fn) chain_v =
         SOME (EL k bb.bb_instructions) /\
       dfg_tracked_opcode (EL k bb.bb_instructions).inst_opcode /\
       k < st.vs_inst_idx /\ k < LENGTH bb.bb_instructions ==>
       chain_v IN FDOM st.vs_vars) /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode /\
    MEM bb fn.fn_blocks /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) ==>
    (!chain_v k.
       dfg_get_def (dfg_build_function fn) chain_v =
         SOME (EL k bb.bb_instructions) /\
       dfg_tracked_opcode (EL k bb.bb_instructions).inst_opcode /\
       k < SUC st.vs_inst_idx /\ k < LENGTH bb.bb_instructions ==>
       chain_v IN FDOM s1.vs_vars)
Proof
  rpt strip_tac >>
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

Triviality nonterm_ih_step:
  !fn bb st s1 fuel ctx.
    dfg_prefix_sound (dfg_build_function fn) bb st.vs_vars st.vs_inst_idx /\
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label st.vs_inst_idx) st /\
    (!chain_v k.
       dfg_get_def (dfg_build_function fn) chain_v =
         SOME (EL k bb.bb_instructions) /\
       dfg_tracked_opcode (EL k bb.bb_instructions).inst_opcode /\
       k < st.vs_inst_idx /\ k < LENGTH bb.bb_instructions ==>
       chain_v IN FDOM st.vs_vars) /\
    step_inst fuel ctx (EL st.vs_inst_idx bb.bb_instructions) st = OK s1 /\
    st.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    assert_local fn ==>
    dfg_prefix_sound (dfg_build_function fn) bb s1.vs_vars
      (SUC st.vs_inst_idx) /\
    range_sound
      (df_widen_at NONE (range_analyze fn) bb.bb_label (SUC st.vs_inst_idx))
      (s1 with vs_inst_idx := SUC st.vs_inst_idx) /\
    (!chain_v k.
       dfg_get_def (dfg_build_function fn) chain_v =
         SOME (EL k bb.bb_instructions) /\
       dfg_tracked_opcode (EL k bb.bb_instructions).inst_opcode /\
       k < SUC st.vs_inst_idx /\ k < LENGTH bb.bb_instructions ==>
       chain_v IN FDOM s1.vs_vars)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- (
    mp_tac dfg_prefix_sound_step >>
    disch_then (qspecl_then [`fn`, `bb`, `st.vs_inst_idx`,
      `fuel`, `ctx`, `st`, `s1`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[]) >>
  conj_tac >- (
    mp_tac nonterm_range_transfer >>
    disch_then (qspecl_then [`fn`, `bb`, `st`, `s1`,
      `fuel`, `ctx`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[]) >>
  rpt strip_tac >>
  mp_tac nonterm_chain_closure >>
  disch_then (qspecl_then [`fn`, `bb`, `st`, `s1`,
    `fuel`, `ctx`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`chain_v`, `k`] mp_tac) >>
  simp[]
QED

(* Helper: if step results are non-OK and lift_result-related,
   then exec_block results (which pass through) are also related *)
Triviality nonOK_exec_block_lift[local]:
  !fuel ctx bb1 bb2 inst1 inst2 st R_ok R_term.
    st.vs_inst_idx < LENGTH bb1.bb_instructions /\
    st.vs_inst_idx < LENGTH bb2.bb_instructions /\
    EL st.vs_inst_idx bb1.bb_instructions = inst1 /\
    EL st.vs_inst_idx bb2.bb_instructions = inst2 /\
    (!s. step_inst fuel ctx inst1 st <> OK s) /\
    lift_result R_ok R_term R_term
      (step_inst fuel ctx inst1 st)
      (step_inst fuel ctx inst2 st) ==>
    (?e. exec_block fuel ctx bb1 st = Error e) \/
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb1 st)
      (exec_block fuel ctx bb2 st)
Proof
  rpt strip_tac >>
  `exec_block fuel ctx bb1 st = step_inst fuel ctx inst1 st` by
    (irule exec_block_nonOK_passthrough >> simp[]) >>
  `!s. step_inst fuel ctx inst2 st <> OK s` by
    metis_tac[lift_result_nonOK] >>
  `exec_block fuel ctx bb2 st = step_inst fuel ctx inst2 st` by
    (irule exec_block_nonOK_passthrough >> simp[]) >>
  Cases_on `step_inst fuel ctx inst1 st`
  >- (DISJ1_TAC >> metis_tac[])
  >> (DISJ2_TAC >> simp[])
QED

(* Core inductive lemma: works on exec_block (which preserves vs_inst_idx).
   run_block resets vs_inst_idx to 0, so it can't be used inductively. *)
Triviality overflow_elim_block_sim_ind:
  !fn bb n fuel ctx st.
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    assert_local fn /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
    dfg_prefix_sound (dfg_build_function fn) bb st.vs_vars st.vs_inst_idx /\
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label st.vs_inst_idx) st /\
    (!chain_v k.
       dfg_get_def (dfg_build_function fn) chain_v =
         SOME (EL k bb.bb_instructions) /\
       dfg_tracked_opcode (EL k bb.bb_instructions).inst_opcode /\
       k < st.vs_inst_idx /\ k < LENGTH bb.bb_instructions ==>
       chain_v IN FDOM st.vs_vars) ==>
    (?e. exec_block fuel ctx bb st = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (exec_block fuel ctx bb st)
      (exec_block fuel ctx
        (analysis_block_transform_widen NONE (range_analyze fn)
           (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                        (range_unwrap v) inst]) bb) st)
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `bt = analysis_block_transform_widen NONE (range_analyze fn)
    (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                 (range_unwrap v) inst])` >>
  Cases_on `st.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (
    qabbrev_tac `dinst = EL st.vs_inst_idx bb.bb_instructions` >>
    qabbrev_tac `idx = st.vs_inst_idx` >>
    qabbrev_tac `v_opt = df_widen_at NONE (range_analyze fn) bb.bb_label idx` >>
    (* Transformed block has same length and known instruction at idx *)
    `idx < LENGTH (bt bb).bb_instructions` by
      simp[Abbr`bt`, analysis_block_transform_widen_def, FLAT_MAPi_SING,
           LENGTH_MAPi] >>
    `EL idx (bt bb).bb_instructions =
       overflow_elim_inst_v (dfg_build_function fn) (range_unwrap v_opt)
         dinst` by
      simp[Abbr`bt`, Abbr`dinst`, Abbr`v_opt`,
           analysis_block_transform_widen_def, FLAT_MAPi_SING, EL_MAPi] >>
    qabbrev_tac `tinst = overflow_elim_inst_v (dfg_build_function fn)
                           (range_unwrap v_opt) dinst` >>
    `inst_wf dinst` by
      (fs[fn_inst_wf_def] >> first_x_assum irule >>
       qexists_tac `bb` >> simp[Abbr`dinst`, MEM_EL] >> metis_tac[]) >>
    (* Per-instruction simulation *)
    mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
              (Q.SPECL [`fn`, `bb`, `idx`, `v_opt`,
                         `fuel`, `ctx`, `dinst`, `st`]
                        overflow_elim_sim_pw))) >>
    (impl_tac
    >- (simp[Abbr`v_opt`, Abbr`dinst`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        rpt strip_tac >> gvs[] >>
        first_x_assum irule >> simp[])) >>
    strip_tac >> pop_assum strip_assume_tac
    >- ((* Error case: step_inst dinst st = Error e *)
      DISJ1_TAC >>
      `exec_block fuel ctx bb st = Error e` by
        (irule exec_block_nonOK_passthrough >> simp[Abbr`dinst`, Abbr`idx`]) >>
      simp[])
    >> (* Lift_result case: we have lift_result on step results *)
    Cases_on `step_inst fuel ctx dinst st`
    >- ( (* OK case *)
      rename1 `step_inst fuel ctx dinst st = OK s1` >>
      qpat_x_assum `lift_result _ _ _ _ _`
        (strip_assume_tac o MATCH_MP lift_result_OK_left) >>
      imp_res_tac state_equiv_empty_eq >> gvs[] >>
      (* OK case *)
      Cases_on `is_terminator dinst.inst_opcode`
      >- ( (* Terminator case *)
        `exec_block fuel ctx bb st =
           if s1.vs_halted then Halt s1 else OK s1` by
          (irule exec_block_terminator_OK >> simp[Abbr`dinst`, Abbr`idx`]) >>
        `exec_block fuel ctx (bt bb) st =
           if s1.vs_halted then Halt s1 else OK s1` by
          (irule exec_block_terminator_OK >> simp[Abbr`idx`] >>
           metis_tac[oe_is_terminator_pres]) >>
        simp[] >>
        IF_CASES_TAC >>
        simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
      )
      >> ( (* Non-terminator case *)
        `exec_block fuel ctx bb st =
           exec_block fuel ctx bb (s1 with vs_inst_idx := SUC st.vs_inst_idx)` by
          (irule exec_block_nonterm_OK >> simp[Abbr`dinst`, Abbr`idx`]) >>
        `exec_block fuel ctx (bt bb) st =
           exec_block fuel ctx (bt bb) (s1 with vs_inst_idx := SUC st.vs_inst_idx)` by
          (irule exec_block_nonterm_OK >>
           simp[Abbr`idx`] >>
           metis_tac[oe_nonterm_pres]) >>
        simp[] >>
        last_x_assum (qspec_then
          `LENGTH bb.bb_instructions - SUC st.vs_inst_idx` mp_tac) >>
        (impl_tac >- simp[Abbr`idx`]) >>
        disch_then (qspecl_then [`fn`, `bb`, `fuel`, `ctx`,
          `s1 with vs_inst_idx := SUC st.vs_inst_idx`] mp_tac) >>
        simp[Abbr`bt`] >>
        (impl_tac >- suspend "ih_preconds") >>
        simp[]
      )
    )
    >> ( (* Non-OK cases: Halt, Abort, IntRet, Error —
           both exec_blocks pass through the non-OK step result *)
      qspecl_then [`fuel`, `ctx`, `bb`, `bt bb`,
        `EL idx bb.bb_instructions`,
        `EL idx (bt bb).bb_instructions`, `st`,
        `state_equiv {}`, `execution_equiv {}`]
        mp_tac nonOK_exec_block_lift >>
      simp[Abbr`idx`] >>
      disch_then match_mp_tac >>
      qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
      simp[Abbr`tinst`, Abbr`dinst`, Abbr`v_opt`]
    )
  )
  >- (
    (* Base case: st.vs_inst_idx >= LENGTH => get_instruction = NONE => Error *)
    simp[Once exec_block_def, get_instruction_def] >>
    simp[Abbr`bt`, analysis_block_transform_widen_def, FLAT_MAPi_SING,
         LENGTH_MAPi] >>
    simp[Once exec_block_def, get_instruction_def]
  )
QED

Resume overflow_elim_block_sim_ind[ih_preconds]:
  conj_tac >- first_assum ACCEPT_TAC >>
  qspecl_then [`fn`, `bb`, `st`, `s1`, `fuel`, `ctx`]
    mp_tac nonterm_ih_step >>
  simp[Abbr`idx`, Abbr`dinst`, Abbr`v_opt`] >>
  disch_then match_mp_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

Finalise overflow_elim_block_sim_ind

Theorem overflow_elim_block_sim[local]:
  !fn bb.
    let dfg = dfg_build_function fn in
    let ra = range_analyze fn in
    let bt = analysis_block_transform_widen NONE ra
               (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) in
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    assert_local fn /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      dfg_ext_sound dfg s.vs_vars /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s ==>
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (run_block fuel ctx bb s)
        (run_block fuel ctx (bt bb) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  mp_tac overflow_elim_block_sim_ind >>
  disch_then (qspecl_then [`fn`, `bb`, `LENGTH bb.bb_instructions`,
    `fuel`, `ctx`, `s`] mp_tac) >>
  `s with vs_inst_idx := 0 = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  simp[run_block_def] >>
  (impl_tac >- (rpt conj_tac >> TRY (metis_tac[dfg_ext_sound_implies_prefix]) >>
                 rpt strip_tac >> fs[])) >>
  simp[]
QED

(* ================================================================
   Function-level correctness
   ================================================================ *)

(* Invariant preservation across a single block execution *)
Triviality overflow_elim_inv_step:
  !fn bb fuel ctx s v.
  wf_function fn /\ fn_inst_wf fn /\
  (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
     MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
  ALL_DISTINCT (fn_labels fn) /\
  dfg_block_local fn /\
  (!bb. MEM bb fn.fn_blocks ==>
    !i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
  (!bb cond false_lbl.
    (LAST bb.bb_instructions).inst_opcode = JNZ ==>
    (LAST bb.bb_instructions).inst_operands =
      [cond; Label false_lbl; Label false_lbl] ==>
    ~MEM bb fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\
  dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
  range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s /\
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  s.vs_inst_idx = 0 /\
  s.vs_current_bb = bb.bb_label /\
  run_block fuel ctx bb s = OK v ==>
  dfg_ext_sound (dfg_build_function fn) v.vs_vars /\
  range_sound (df_widen_at NONE (range_analyze fn) v.vs_current_bb 0) v /\
  MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt gen_tac >> strip_tac >>
  `exec_block fuel ctx bb s = OK v` by
    (gvs[run_block_def] >>
     `s with vs_inst_idx := 0 = s` by simp[venomStateTheory.venom_state_component_equality] >>
     gvs[]) >>
  conj_tac
  >- (
    irule dfg_ext_sound_run_block >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY res_tac >>
    qexistsl_tac [`bb`, `ctx`, `fuel`, `s`] >>
    simp[])
  >> (
    mp_tac assertElimProofsTheory.range_successor_obligation >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> res_tac)) >>
    disch_then (qspecl_then [`bb`, `fuel`, `ctx`, `s`, `v`] mp_tac) >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      fs[dfg_ext_sound_def])) >>
    simp[])
QED

(* Bridge: run_block = exec_block when vs_inst_idx = 0 *)
Triviality run_block_is_exec_block[local]:
  s.vs_inst_idx = 0 ==> run_block f c bb s = exec_block f c bb s
Proof
  strip_tac >> simp[run_block_def] >>
  Cases_on `s` >> gvs[venom_state_fn_updates]
QED

Theorem overflow_elim_function_sim[local]:
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
    MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
    range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx
        (function_map_transform
          (analysis_block_transform_widen NONE (range_analyze fn)
            (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                         (range_unwrap v) inst])) fn) s)
Proof
  rpt strip_tac
  \\ qabbrev_tac `bt = analysis_block_transform_widen NONE (range_analyze fn)
       (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                    (range_unwrap v) inst])`
  \\ qabbrev_tac `Inv = \s:venom_state.
       dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
       range_sound (df_widen_at NONE
         (range_analyze fn : (string |-> value_range) option df_widen_state)
         s.vs_current_bb 0) s /\
       MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre`
  \\ mp_tac (BETA_RULE (ISPECL [
    ``\(s1:venom_state) (s2:venom_state). (Inv : venom_state -> bool) s1``,
    ``state_equiv {} : venom_state -> venom_state -> bool``,
    ``execution_equiv {} : venom_state -> venom_state -> bool``,
    ``bt : basic_block -> basic_block``,
    ``fn : ir_function``]
    block_sim_function_with_pred2_bb))
  \\ impl_tac
  >- (
    rpt conj_tac
    (* P s s ==> R_ok s s *)
    >- metis_tac[state_equiv_refl]
    (* R_ok ==> R_term *)
    >- metis_tac[REWRITE_RULE [execEquivParamDefsTheory.valid_state_rel_def]
          (SPEC ``{}:string set`` state_equiv_execution_equiv_valid_state_rel)]
    (* R_ok ==> current_bb, inst_idx, halted agree *)
    >- (rpt strip_tac >> fs[state_equiv_def, execution_equiv_def])
    (* bt preserves bb_label *)
    >- simp[analysis_block_transform_widen_def, Abbr `bt`]
    (* P preservation after both exec_blocks *)
    >- suspend "p_pres"
    (* Block simulation *)
    >- suspend "block_sim"
  )
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  \\ simp[Abbr `Inv`, Abbr `bt`]
QED

Resume overflow_elim_function_sim[p_pres]:
  rpt gen_tac >> strip_tac >>
  imp_res_tac state_equiv_empty_eq >> gvs[] >>
  `run_block fuel ctx bb s1 = OK s1'` by
    simp[run_block_is_exec_block] >>
  simp[Abbr `Inv`] >>
  match_mp_tac overflow_elim_inv_step >>
  qexistsl_tac [`bb`, `fuel`, `ctx`, `s1`] >>
  BETA_TAC >> gvs[] >> metis_tac[]
QED

Resume overflow_elim_function_sim[block_sim]:
  rpt strip_tac >>
  imp_res_tac state_equiv_empty_eq >> gvs[] >>
  (* Get run_block result from overflow_elim_block_sim *)
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] overflow_elim_block_sim)) >>
  disch_then (qspecl_then [`fn`, `bb`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    gvs[Abbr `Inv`] >> res_tac)) >>
  BETA_TAC >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s1`] mp_tac) >>
  (* Bridge: run_block = exec_block when vs_inst_idx = 0 *)
  simp[run_block_is_exec_block, Abbr `bt`] >>
  gvs[Abbr `Inv`]
QED

Finalise overflow_elim_function_sim

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
    s.vs_inst_idx = 0 ==>
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

Theorem overflow_elim_function_correct_proof:
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
  \\ qabbrev_tac `bt = analysis_block_transform_widen NONE (range_analyze fn)
       (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                    (range_unwrap v) inst])`
  (* Bridge: all run_function = run_blocks *)
  \\ `!fn'. fn_entry_label fn' = fn_entry_label fn ==>
       run_function fuel ctx fn' s = run_blocks fuel ctx fn' s` by
    (rpt strip_tac >> irule run_function_is_run_blocks >> simp[])
  \\ `(bt (HD fn.fn_blocks)).bb_label = (HD fn.fn_blocks).bb_label` by
    simp[analysis_block_transform_widen_def, Abbr `bt`]
  \\ `fn_entry_label (function_map_transform bt fn) = fn_entry_label fn` by
    (irule fn_entry_label_function_map_transform >> simp[Abbr `bt`,
       analysis_block_transform_widen_def])
  \\ `fn_entry_label (clear_nops_function (function_map_transform bt fn)) =
      fn_entry_label fn` by
    simp[fn_entry_label_clear_nops]
  (* Rewrite all run_function to run_blocks *)
  \\ fs[]
  (* Apply overflow_elim_function_sim for run_blocks *)
  \\ mp_tac overflow_elim_function_sim
  \\ disch_then (qspecl_then [`fn`, `fuel`, `ctx`, `s`] mp_tac)
  \\ simp[Abbr `bt`]
  \\ (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    fs[fn_entry_label_def] >> Cases_on `entry_block fn` >> gvs[] >>
    drule cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
    strip_tac >> metis_tac[rich_listTheory.HEAD_MEM]))
  \\ strip_tac
  >- (DISJ1_TAC >> metis_tac[])
  \\ DISJ2_TAC
  \\ irule lift_result_trans
  \\ conj_tac >- metis_tac[state_equiv_trans]
  \\ conj_tac >- metis_tac[execution_equiv_trans]
  \\ qexists_tac `run_blocks fuel ctx
       (function_map_transform
         (analysis_block_transform_widen NONE (range_analyze fn)
           (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                        (range_unwrap v) inst])) fn) s`
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ `run_function fuel ctx
        (clear_nops_function (function_map_transform
           (analysis_block_transform_widen NONE (range_analyze fn)
             (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                          (range_unwrap v) inst])) fn)) s =
      run_blocks fuel ctx
        (clear_nops_function (function_map_transform
           (analysis_block_transform_widen NONE (range_analyze fn)
             (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                          (range_unwrap v) inst])) fn)) s` by
    (first_x_assum irule >> simp[fn_entry_label_clear_nops])
  \\ pop_assum (fn th => REWRITE_TAC [GSYM th])
  \\ simp_tac std_ss [GSYM result_equiv_is_lift_result,
       GSYM analysis_function_transform_widen_def]
  (* run_blocks (aft fn) s = run_function (aft fn) s *)
  \\ `run_blocks fuel ctx
        (analysis_function_transform_widen NONE (range_analyze fn)
           (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                        (range_unwrap v) inst]) fn) s =
      run_function fuel ctx
        (analysis_function_transform_widen NONE (range_analyze fn)
           (\v inst. [overflow_elim_inst_v (dfg_build_function fn)
                        (range_unwrap v) inst]) fn) s` by
    (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM run_function_is_run_blocks])) >>
     simp[fn_entry_label_function_map_transform,
          analysis_function_transform_widen_def,
          analysis_block_transform_widen_def])
  \\ pop_assum SUBST1_TAC
  \\ irule clear_nops_function_correct_run_function
  \\ first_assum ACCEPT_TAC
QED
