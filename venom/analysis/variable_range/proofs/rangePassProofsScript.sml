(*
 * Range analysis soundness across block execution.
 *
 * range_transfer_sound: the per-instruction transfer is sound.
 * range_exit_sound: soundness at block entry gives soundness at block exit.
 * range_successor_sound / range_successor_obligation: soundness at block
 *   entry, with DFG soundness, gives soundness at the successor's entry.
 * range_pass_correct: a 1:1 pass whose instruction rewrite uses the widened
 *   range at each index and simulates the original instruction there is
 *   correct for run_blocks.  assert_elim and overflow_elim are instances.
 *)

Theory rangePassProofs
Ancestors
  analysisSimDefs
  analysisSimProps
  analysisSimProofsWiden
  dfAnalyzeWidenDefs
  dfgAnalysisProps
  dfgSoundDefs
  dfgSoundProofs
  execEquivParamProps
  finite_map
  indexedLists
  list
  passSimulationDefs
  passSimulationProps
  rangeAnalysisDefs
  rangeAnalysisProofs
  rangeEvalDefs
  rangeEvalProofs
  stateEquiv
  stateEquivProps
  valueRangeDefs
  venomExecProofs
  venomExecProps
  venomExecSemantics
  venomInst
  venomInstProps
  venomState
  venomWf
  worklistDefs cfgCorrectnessProof dfAnalyzeWidenProofs
Libs
  pairLib

(* transfer_sound for range analysis — shared by all range-based passes *)
Theorem range_transfer_sound:
  !fn. transfer_sound range_sound range_transfer_opt
         (dfg_build_function fn, fn.fn_blocks)
Proof
  simp[transfer_sound_def] >> rpt strip_tac >>
  Cases_on `v` >> fs[range_sound_def, range_transfer_opt_def, LET_THM] >>
  irule per_inst_range_sound
  >- (qexistsl_tac [`run_ctx`, `fuel`, `s`] >>
      simp[in_range_state_def, FLOOKUP_DEF])
  >- (qexistsl_tac [`run_ctx`, `fuel`, `s`] >> simp[])
QED

(* Restrict transfer soundness once, outside the lifting proofs' contexts. *)
Theorem range_transfer_sound_wf[local]:
  !fn. transfer_sound_wf range_sound range_transfer_opt
         (dfg_build_function fn, fn.fn_blocks)
Proof
  gen_tac >> PURE_REWRITE_TAC [transfer_sound_wf_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `run_ctx`, `v`, `inst`, `s`, `s'`]
    (REWRITE_RULE [transfer_sound_def] (Q.SPEC `fn` range_transfer_sound))) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* range_sound stable under state_equiv {} *)
Theorem range_sound_state_equiv:
  !v s1 s2. state_equiv {} s1 s2 /\ range_sound v s1 ==>
             range_sound v s2
Proof
  rpt strip_tac >> Cases_on `v` >> fs[range_sound_def] >>
  fs[in_range_state_def] >> rpt strip_tac >>
  `FLOOKUP s1.vs_vars v = SOME w` by
    (qpat_x_assum `state_equiv _ _ _` mp_tac >>
     simp[state_equiv_def, execution_equiv_def, lookup_var_def] >>
     metis_tac[]) >>
  res_tac
QED

(* ===== Pre-instantiated framework lemma for range analysis ===== *)

(* ===== Range analysis fixpoint wrappers ===== *)
(* Range-analysis specializations of dfAnalyzeWiden theorems, used by
   range_exit_sound, range_widen_at_some, range_successor_sound, and
   future range-based passes. *)


(* PHI-prefix range soundness helpers live in rangeAnalysisProofsTheory. *)

Triviality phi_prefix_length_lt_wf[local]:
  !bb. bb_well_formed bb ==>
       phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  CCONTR_TAC >>
  `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions` by
    decide_tac >>
  `PRE (LENGTH bb.bb_instructions) < phi_prefix_length bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_el_phi] >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  gvs[is_terminator_def]
QED

(* Inter-block transfer: df_widen_at at position 0 = df_widen_entry *)
Theorem range_entry_eq:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    df_widen_at NONE (range_analyze fn) lbl 0 =
    df_widen_entry NONE (range_analyze fn) lbl
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
    (ISPECL [
      ``Forward``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``lbl : string``,
      ``bb : basic_block``]
    dfAnalyzeWidenProofsTheory.df_widen_at_inter_transfer))) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
  simp[]
QED

(* df_fold_forward result agrees with df_widen_at at every position,
   and the fold output equals df_widen_at at exit position. *)
Triviality df_fold_widen_at_agree:
  !n transfer lbl instrs entry fv im fn bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    transfer = range_transfer_opt (dfg_build_function fn, fn.fn_blocks) /\
    instrs = bb.bb_instructions /\
    entry = df_widen_entry NONE (range_analyze fn) lbl /\
    df_fold_forward transfer lbl instrs 0 entry FEMPTY = (fv, im) /\
    n <= LENGTH instrs ==>
    FLOOKUP im (lbl, n) = SOME (df_widen_at NONE (range_analyze fn) lbl n)
Proof
  Induct >> rpt strip_tac
  >- ((* base: n=0, entry *)
    imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_at >>
    `df_widen_at NONE (range_analyze fn) lbl 0 =
     df_widen_entry NONE (range_analyze fn) lbl` by (
      irule (SIMP_RULE std_ss [LET_THM] range_entry_eq) >> simp[]) >>
    gvs[])
  >> (* inductive: n = SUC n' *)
  gvs[] >>
  `n < LENGTH bb.bb_instructions` by DECIDE_TAC >>
  `FLOOKUP im (lbl, n) =
   SOME (df_widen_at NONE (range_analyze fn) lbl n)` by (
    first_x_assum match_mp_tac >> simp[]) >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_at >>
  `df_widen_at NONE (range_analyze fn) lbl (SUC n) =
   range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
     (EL n bb.bb_instructions)
     (df_widen_at NONE (range_analyze fn) lbl n)` by (
    irule (SIMP_RULE std_ss [LET_THM] range_intra_transfer) >> simp[]) >>
  fs[]
QED

Theorem df_fold_fv_eq_widen_at:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    let ra = range_analyze fn in
    let entry = df_widen_entry NONE ra lbl in
    let (fv, im) = df_fold_block Forward
      (range_transfer_opt (dfg_build_function fn, fn.fn_blocks))
      lbl bb.bb_instructions entry in
    fv = df_widen_at NONE ra lbl (LENGTH bb.bb_instructions)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  pairarg_tac >> simp[] >>
  fs[dfAnalyzeDefsTheory.df_fold_block_def] >>
  imp_res_tac dfAnalyzeProofsTheory.df_fold_forward_at >>
  (* fv = THE (FLOOKUP im (lbl, LENGTH instrs)) *)
  (* Show FLOOKUP im (lbl, LENGTH instrs) = SOME (df_widen_at ...) *)
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
    `range_transfer_opt (dfg_build_function fn, fn.fn_blocks)`,
    `lbl`, `bb.bb_instructions`,
    `df_widen_entry NONE (range_analyze fn) lbl`,
    `fv`, `im`, `fn`, `bb`] df_fold_widen_at_agree) >>
  simp[]
QED

(* Precompute the ISPECL of process_fixpoint_absorbs for range analysis *)
fun mk_range_pfa () =
  CONV_RULE (DEPTH_CONV PairRules.PBETA_CONV)
  (SIMP_RULE std_ss [LET_THM, dfAnalyzeDefsTheory.direction_case_def]
  (SIMP_RULE std_ss [LET_THM]
  (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
  (ISPECL [
    ``Forward``,
    ``NONE : (string |-> value_range) option``,
    ``range_join_opt``,
    ``range_widen_opt : (string |-> value_range) option
        -> (string |-> value_range) option
        -> (string |-> value_range) option``,
    ``WIDEN_THRESHOLD``,
    ``range_transfer_opt``,
    ``range_edge_transfer_opt``,
    ``(dfg_build_function fn, fn.fn_blocks)``,
    ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
        (fn_entry_label fn)``,
    ``cfg_analyze fn``,
    ``fn.fn_blocks``,
    ``lbl : string``,
    ``range_analyze fn``]
  dfAnalyzeWidenProofsTheory.process_fixpoint_absorbs))));

(* Boundary absorption at fixpoint: boundary = join(boundary, exit_val) *)
Theorem range_fixpoint_absorbs:
  !fn lbl.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    let ra = range_analyze fn in
    let cfg = cfg_analyze fn in
    let neighbors = cfg_preds_of cfg lbl in
    let edge_vals = MAP (\nbr. range_edge_transfer_opt
          (dfg_build_function fn, fn.fn_blocks) nbr lbl
          (df_widen_boundary NONE ra nbr)) neighbors in
    let joined = (case edge_vals of
        [] => (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
                 NONE => NONE
               | SOME (ev_lbl, v) => if lbl = ev_lbl then v else NONE)
      | v4::v5 => FOLDL range_join_opt NONE edge_vals) in
    let entry = (if df_widen_visits ra lbl >= WIDEN_THRESHOLD
                 then range_widen_opt (df_widen_entry NONE ra lbl) joined
                 else joined) in
      entry = df_widen_entry NONE ra lbl /\
      range_join_opt (df_widen_boundary NONE ra lbl)
        (df_widen_at NONE ra lbl
          (case lookup_block lbl fn.fn_blocks of
             NONE => 0
           | SOME bb => LENGTH bb.bb_instructions)) =
      df_widen_boundary NONE ra lbl
Proof
  rpt strip_tac
  \\ simp_tac std_ss [LET_THM]
  \\ mp_tac (mk_range_pfa ())
  \\ impl_tac
  >- (mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >>
      simp[is_fixpoint_def, EVERY_MEM])
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ conj_tac
  >- first_assum ACCEPT_TAC
  \\ Cases_on `lookup_block lbl fn.fn_blocks`
  >- ((* NONE case: impossible - reachable labels have blocks *)
      imp_res_tac dfAnalyzeProofsTheory.cfg_dfs_pre_subset_fn_labels >>
      gvs[fn_labels_def, MEM_MAP, wf_function_def] >>
      imp_res_tac venomExecPropsTheory.MEM_lookup_block >> gvs[])
  \\ rename1 `SOME bb`
  \\ mp_tac (SIMP_RULE std_ss [LET_THM] df_fold_fv_eq_widen_at)
  \\ disch_then (qspecl_then [`fn`, `lbl`, `bb`] mp_tac)
  \\ simp[] >> strip_tac
  \\ Cases_on `df_fold_block Forward
        (range_transfer_opt (dfg_build_function fn,fn.fn_blocks)) lbl
        bb.bb_instructions
        (df_widen_entry NONE (range_analyze fn) lbl)`
  \\ gvs[]
QED

(* ===== Range soundness at successor entry ===== *)

(* Exit soundness: range_sound at block entry ==> range_sound at block exit.
   PHI-prefix evaluation advances the analysis point before exec_block. *)
Theorem range_exit_sound:
  !fn bb fuel run_ctx s v.
    let ra = range_analyze fn in
      wf_function fn /\
      fn_inst_wf fn /\
      ALL_DISTINCT (fn_labels fn) /\
      (!bb. MEM bb fn.fn_blocks ==>
        !i. i < LENGTH bb.bb_instructions - 1 ==>
          ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      s.vs_inst_idx = 0 /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
      run_block fuel run_ctx bb s = OK v ==>
      range_sound (df_widen_at NONE ra bb.bb_label
        (LENGTH bb.bb_instructions)) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    irule venomExecPropsTheory.MEM_lookup_block >>
    qpat_assum `ALL_DISTINCT _` mp_tac >>
    simp_tac std_ss [fn_labels_def] >> metis_tac[]) >>
  qpat_x_assum `run_block fuel run_ctx bb s = OK v` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
  strip_tac >>
  qabbrev_tac `result = widen_to_df (range_analyze fn)` >>
  `!idx. df_widen_at NONE (range_analyze fn) bb.bb_label idx =
         df_at NONE result bb.bb_label idx` by
    simp[Abbr `result`, analysisSimProofsWidenTheory.widen_to_df_def,
         dfAnalyzeWidenDefsTheory.df_widen_at_def,
         dfAnalyzeDefsTheory.df_at_def] >>
  `!idx. SUC idx <= LENGTH bb.bb_instructions ==>
     df_at NONE result bb.bb_label (SUC idx) =
     range_transfer_opt (dfg_build_function fn, fn.fn_blocks)
       (EL idx bb.bb_instructions)
       (df_at NONE result bb.bb_label idx)` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`fn`, `bb.bb_label`, `bb`, `idx`] range_intra_transfer) >>
    impl_tac >- simp[] >>
    strip_tac >> gvs[]) >>
  `range_sound (df_at NONE result bb.bb_label
       (phi_prefix_length bb.bb_instructions))
     ((s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        with vs_inst_idx := 0)` by (
    simp[] >>
    mp_tac (Q.SPECL [`fn`, `bb`, `s`, `s_phi`] eval_phis_range_sound) >>
    simp[]) >>
  mp_tac (ISPECL [
    ``state_equiv {} : venom_state -> venom_state -> bool``,
    ``execution_equiv {} : venom_state -> venom_state -> bool``,
    ``range_sound``,
    ``range_transfer_opt``,
    ``(dfg_build_function fn, fn.fn_blocks)``,
    ``bb : basic_block``,
    ``NONE : (string |-> value_range) option``,
    ``result : (string |-> value_range) option df_state``]
    analysisSimProofsTheory.transfer_sound_exit_from_wf_len) >>
  impl_tac >- (
    rpt conj_tac
    >- simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel]
    >- ACCEPT_TAC (Q.SPEC `fn` range_transfer_sound_wf)
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- metis_tac[range_sound_state_equiv]
    >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`fuel`, `run_ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `v`] mp_tac) >>
  simp[] >>
  impl_tac >- (
    conj_tac >- (
      `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
        metis_tac[phi_prefix_length_lt_wf] >>
      Cases_on `bb.bb_instructions` >> fs[]) >>
    gvs[]) >>
  simp[]
QED

(* ===== Successor soundness (main) ===== *)

(* range_transfer_opt always returns SOME *)
Theorem range_transfer_opt_is_some:
  !ctx inst v. ?rs. range_transfer_opt ctx inst v = SOME rs
Proof
  rpt gen_tac >> Cases_on `v` >>
  simp[range_transfer_opt_def, LET_THM]
QED

(* df_widen_at is SOME at any position >= 1 in a non-empty block,
   since range_transfer_opt always produces SOME. *)
Theorem range_widen_at_some:
  !fn bb n.
    let ra = range_analyze fn in
      wf_function fn /\
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      ALL_DISTINCT (fn_labels fn) /\
      0 < n /\ n <= LENGTH bb.bb_instructions ==>
      ?rs. df_widen_at NONE ra bb.bb_label n = SOME rs
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    irule venomExecPropsTheory.MEM_lookup_block >>
    qpat_assum `ALL_DISTINCT _` mp_tac >>
    simp_tac std_ss [fn_labels_def] >> metis_tac[]) >>
  Induct_on `n` >> simp[] >> rpt strip_tac >>
  (* Get the intra-transfer equation at position n *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
    (ISPECL [
      ``Forward``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``bb.bb_label``,
      ``bb : basic_block``,
      ``n : num``]
    dfAnalyzeWidenProofsTheory.df_widen_at_intra_transfer))) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
  simp[] >> strip_tac >>
  metis_tac[range_transfer_opt_is_some]
QED

(* Helper: range_widen_opt at fixpoint produces NONE, SOME FEMPTY, or the joined value.
   In all cases either trivially sound or reduces to showing joined is sound. *)
Theorem range_widen_opt_fixpoint_cases:
  !old joined.
    range_widen_opt old joined = old ==>
    old = NONE \/ old = SOME FEMPTY \/ old = joined
Proof
  Cases_on `old` >> Cases_on `joined` >>
  simp[range_widen_opt_def] >>
  rpt strip_tac >> BasicProvers.every_case_tac >> fs[]
QED

(* Helper: JNZ branch condition for range_branch_refine_sound.
   When JNZ always has distinct labels, we can derive the branch condition
   from run_block_jnz_condition. *)
Theorem jnz_branch_condition_from_run_block:
  !fn bb fuel run_ctx s v succ.
    run_block fuel run_ctx bb s = OK v /\
    succ = v.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) ==>
    !bb' cond_op true_lbl false_lbl.
      lookup_block bb.bb_label fn.fn_blocks = SOME bb' /\
      bb'.bb_instructions <> [] /\
      (LAST bb'.bb_instructions).inst_opcode = JNZ /\
      (LAST bb'.bb_instructions).inst_operands =
        [cond_op; Label true_lbl; Label false_lbl] ==>
      !var. cond_op = Var var ==>
        ?w. FLOOKUP v.vs_vars var = SOME w /\
            (succ = true_lbl ==> w <> 0w) /\
            (succ = false_lbl ==> w = 0w)
Proof
  rpt strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `bb' = bb` by fs[] >> BasicProvers.VAR_EQ_TAC >>
  `true_lbl <> false_lbl` by (
    CCONTR_TAC >> fs[] >> res_tac) >>
  mp_tac run_block_jnz_condition >>
  disch_then (qspecl_then [`fuel`, `run_ctx`, `bb`, `s`, `v`,
    `var`, `true_lbl`, `false_lbl`] mp_tac) >>
  simp[]
QED

(* Helper: combines jnz_branch_condition_from_run_block with
   range_branch_refine_sound to get in_range_state of the refined range
   at a successor, given run_block + boundary soundness. *)
Theorem range_branch_refine_after_run_block:
  !fn bb fuel run_ctx s v succ boundary_rs.
    run_block fuel run_ctx bb s = OK v /\
    succ = v.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    in_range_state boundary_rs v.vs_vars /\
    dfg_sound (dfg_build_function fn) v.vs_vars ==>
    in_range_state (range_branch_refine (dfg_build_function fn)
      fn.fn_blocks bb.bb_label succ boundary_rs) v.vs_vars
Proof
  rpt strip_tac >>
  mp_tac range_branch_refine_sound >>
  disch_then (qspecl_then [`dfg_build_function fn`, `fn.fn_blocks`,
    `bb.bb_label`, `succ`, `boundary_rs`, `v.vs_vars`] mp_tac) >>
  `!bb' cond_op true_lbl false_lbl.
      lookup_block bb.bb_label fn.fn_blocks = SOME bb' /\
      bb'.bb_instructions <> [] /\
      (LAST bb'.bb_instructions).inst_opcode = JNZ /\
      (LAST bb'.bb_instructions).inst_operands =
        [cond_op; Label true_lbl; Label false_lbl] ==>
      !var. cond_op = Var var ==>
        ?w. FLOOKUP v.vs_vars var = SOME w /\
            (succ = true_lbl ==> w <> 0w) /\
            (succ = false_lbl ==> w = 0w)` by (
    mp_tac jnz_branch_condition_from_run_block >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`,
      `succ`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC)
  \\ impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  \\ strip_tac
QED

Theorem range_edge_transfer_opt_some:
  !dfg bbs pred succ rs.
    range_edge_transfer_opt (dfg, bbs) pred succ (SOME rs) =
    SOME (range_branch_refine dfg bbs pred succ rs)
Proof
  simp[range_edge_transfer_opt_def]
QED

(* Successor soundness: after running a block at a fixpoint,
   the successor has range_sound, dfg_sound+ops_defined, and is in cfg_dfs_pre.
   Requires ssa_form + dfg_sound for edge_transfer soundness. *)
(* range_sound at successor entry point *)
Theorem range_sound_at_successor:
  !fn bb fuel run_ctx s v.
    let ra = range_analyze fn in
      wf_function fn /\
      fn_inst_wf fn /\
      (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
         MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
      ALL_DISTINCT (fn_labels fn) /\
      dfg_block_local fn /\
      (!bb. MEM bb fn.fn_blocks ==>
        !i. i < LENGTH bb.bb_instructions - 1 ==>
          ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
      (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
        (LAST bb.bb_instructions).inst_opcode = JNZ /\
        (LAST bb.bb_instructions).inst_operands =
          [cond; Label true_lbl; Label false_lbl] ==>
        true_lbl <> false_lbl) /\
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
      dfg_sound (dfg_build_function fn) s.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM s.vs_vars) /\
      run_block fuel run_ctx bb s = OK v /\
      dfg_sound (dfg_build_function fn) v.vs_vars /\
      MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label) ==>
      range_sound (df_widen_at NONE ra v.vs_current_bb 0) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    irule venomExecPropsTheory.MEM_lookup_block >>
    fs[fn_labels_def]) >>
  (* Exit soundness *)
  `range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label
     (LENGTH bb.bb_instructions)) v` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_exit_sound) >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
    simp[]) >>
  (* Exit value is SOME *)
  `?exit_rs. df_widen_at NONE (range_analyze fn) bb.bb_label
     (LENGTH bb.bb_instructions) = SOME exit_rs` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_widen_at_some) >>
    disch_then (qspecl_then [`fn`, `bb`, `LENGTH bb.bb_instructions`] mp_tac) >>
    simp[] >> impl_tac >- (Cases_on `bb.bb_instructions` >> fs[]) >>
    simp[]) >>
  qabbrev_tac `ra = range_analyze fn` >>
  qabbrev_tac `succ = v.vs_current_bb` >>
  `MEM succ (cfg_analyze fn).cfg_dfs_pre` by (
    imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
    gvs[EVERY_MEM]) >>
  (* Fixpoint absorption at bb.bb_label *)
  `range_join_opt (df_widen_boundary NONE ra bb.bb_label)
     (df_widen_at NONE ra bb.bb_label (LENGTH bb.bb_instructions)) =
   df_widen_boundary NONE ra bb.bb_label` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint_absorbs) >>
    disch_then (qspecl_then [`fn`, `bb.bb_label`] mp_tac) >>
    simp[Abbr `ra`]) >>
  (* Boundary is SOME *)
  `?boundary_rs. df_widen_boundary NONE ra bb.bb_label = SOME boundary_rs` by (
    CCONTR_TAC >> gvs[] >>
    Cases_on `df_widen_boundary NONE ra bb.bb_label` >> gvs[] >>
    fs[range_join_opt_def]) >>
  `range_join_opt (SOME boundary_rs) (SOME exit_rs) = SOME boundary_rs` by
    gvs[] >>
  `in_range_state boundary_rs v.vs_vars` by (
    mp_tac (Q.SPECL [`SOME boundary_rs`, `exit_rs`, `v`]
      range_join_opt_some_sound_right) >>
    simp[range_sound_def] >> gvs[range_sound_def]) >>
  (* Successor lookup + pred *)
  `?succ_bb. lookup_block succ fn.fn_blocks = SOME succ_bb` by (
    `MEM succ (fn_labels fn)` by (
      `cfg_reachable_of (cfg_analyze fn) succ` by (
        imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
        fs[pred_setTheory.EXTENSION, Abbr `succ`]) >>
      metis_tac[cfgCorrectnessProofTheory.cfg_analyze_reachable_in_labels]) >>
    fs[fn_labels_def, MEM_MAP] >>
    metis_tac[venomExecPropsTheory.MEM_lookup_block, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) succ)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond, Abbr `succ`] >>
  (* Entry = df_widen_entry *)
  `df_widen_at NONE ra succ 0 = df_widen_entry NONE ra succ` by (
    mp_tac range_entry_eq >>
    disch_then (qspecl_then [`fn`, `succ`, `succ_bb`] mp_tac) >>
    simp[Abbr `ra`, Abbr `succ`]) >>
  simp[] >>
  (* Fixpoint at succ *)
  qabbrev_tac `neighbors = cfg_preds_of (cfg_analyze fn) succ` >>
  qabbrev_tac `edge_vals = MAP (\nbr. range_edge_transfer_opt
        (dfg_build_function fn, fn.fn_blocks) nbr succ
        (df_widen_boundary NONE ra nbr)) neighbors` >>
  qabbrev_tac `joined = (case edge_vals of
      [] => (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
               NONE => NONE
             | SOME (ev_lbl, v') => if succ = ev_lbl then v' else NONE)
    | v4::v5 => FOLDL range_join_opt NONE edge_vals)` >>
  qabbrev_tac `entry = (if df_widen_visits ra succ >= WIDEN_THRESHOLD
               then range_widen_opt (df_widen_entry NONE ra succ) joined
               else joined)` >>
  `entry = df_widen_entry NONE ra succ` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint_absorbs) >>
    disch_then (qspecl_then [`fn`, `succ`] mp_tac) >>
    simp[Abbr `ra`, Abbr `succ`] >>
    simp_tac std_ss [LET_THM] >> strip_tac >>
    unabbrev_all_tac >> gvs[]) >>
  Cases_on `entry = NONE` >- gvs[range_sound_def] >>
  Cases_on `entry = SOME FEMPTY` >- gvs[range_sound_def, in_range_state_def] >>
  `entry = joined` by (
    Cases_on `df_widen_visits ra succ >= WIDEN_THRESHOLD` >> gvs[Abbr `entry`] >>
    metis_tac[range_widen_opt_fixpoint_cases]) >>
  `edge_vals <> []` by (
    CCONTR_TAC >> gvs[Abbr `edge_vals`] >>
    `neighbors = []` by gvs[Abbr `neighbors`] >>
    gvs[Abbr `joined`] >>
    BasicProvers.every_case_tac >> gvs[]) >>
  `?hd tl. edge_vals = hd::tl` by (Cases_on `edge_vals` >> gvs[]) >>
  `joined = FOLDL range_join_opt NONE edge_vals` by
    gvs[Abbr `joined`]
  (* refined_rs via edge_transfer *)
  \\ qabbrev_tac `refined_rs = range_branch_refine (dfg_build_function fn)
        fn.fn_blocks bb.bb_label succ boundary_rs`
  \\ `SOME refined_rs = range_edge_transfer_opt (dfg_build_function fn,
       fn.fn_blocks) bb.bb_label succ (df_widen_boundary NONE ra bb.bb_label)`
      by (qunabbrev_tac `refined_rs` >>
          qpat_x_assum `df_widen_boundary NONE ra bb.bb_label = SOME boundary_rs`
            SUBST1_TAC >>
          REWRITE_TAC [GSYM range_edge_transfer_opt_some])
  \\ `MEM (SOME refined_rs) edge_vals` by (
    pop_assum SUBST1_TAC >>
    qunabbrev_tac `edge_vals` >> qunabbrev_tac `neighbors` >>
    REWRITE_TAC [MEM_MAP] >>
    qexists_tac `bb.bb_label` >>
    conj_tac >- (BETA_TAC >> REFL_TAC) >>
    first_assum ACCEPT_TAC)
  (* Re-derive JNZ distinct-labels in original form *)
  \\ `!bb' cond true_lbl false_lbl. MEM bb' fn.fn_blocks /\
        (LAST bb'.bb_instructions).inst_opcode = JNZ /\
        (LAST bb'.bb_instructions).inst_operands =
          [cond; Label true_lbl; Label false_lbl] ==>
        true_lbl <> false_lbl` by (
    rpt gen_tac >> strip_tac >> CCONTR_TAC >>
    `true_lbl = false_lbl` by (pop_assum mp_tac >> REWRITE_TAC[]) >>
    BasicProvers.VAR_EQ_TAC >> res_tac)
  (* Specialize non-terminator hypothesis for bb *)
  \\ `!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[]
  (* in_range_state of branch_refine *)
  \\ `in_range_state refined_rs v.vs_vars` by (
    qpat_x_assum `Abbrev (refined_rs = _)` (REWRITE_TAC o single o
      REWRITE_RULE [markerTheory.Abbrev_def])
    \\ qpat_x_assum `Abbrev (succ = _)` (REWRITE_TAC o single o
      REWRITE_RULE [markerTheory.Abbrev_def])
    \\ mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`,
      `v.vs_current_bb`, `boundary_rs`] range_branch_refine_after_run_block)
    \\ REWRITE_TAC[]
    \\ impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
    \\ strip_tac \\ first_assum ACCEPT_TAC)
  (* range_sound via FOLDL *)
  \\ `range_sound (FOLDL range_join_opt NONE edge_vals) v` by (
    irule foldl_range_join_opt_sound >>
    qexists_tac `refined_rs` >>
    conj_tac >> first_assum ACCEPT_TAC)
  \\ metis_tac[]
QED

Theorem range_successor_sound:
  !fn bb fuel run_ctx s v.
    let ra = range_analyze fn in
      wf_function fn /\
      fn_inst_wf fn /\
      (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
         MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
      ALL_DISTINCT (fn_labels fn) /\
      dfg_block_local fn /\
      (!bb. MEM bb fn.fn_blocks ==>
        !i. i < LENGTH bb.bb_instructions - 1 ==>
          ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
      (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
        (LAST bb.bb_instructions).inst_opcode = JNZ /\
        (LAST bb.bb_instructions).inst_operands =
          [cond; Label true_lbl; Label false_lbl] ==>
        true_lbl <> false_lbl) /\
      MEM bb fn.fn_blocks /\
      MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
      s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
      range_sound (df_widen_at NONE ra bb.bb_label 0) s /\
      dfg_sound (dfg_build_function fn) s.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM s.vs_vars) /\
      run_block fuel run_ctx bb s = OK v ==>
      MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
      range_sound (df_widen_at NONE ra v.vs_current_bb 0) v /\
      dfg_sound (dfg_build_function fn) v.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
         u IN FDOM v.vs_vars)
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Derive block well-formedness *)
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  (* Successor in cfg_dfs_pre *)
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
      ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    (imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
     gvs[EVERY_MEM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  (* dfg_sound + ops_defined *)
  `dfg_sound (dfg_build_function fn) v.vs_vars /\
   (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
      vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==>
      u IN FDOM v.vs_vars)` by (
    mp_tac dfg_sound_run_block >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[])
  (* range_sound via extracted helper *)
  \\ conj_tac >- (
    mp_tac (SIMP_RULE std_ss [LET_THM] range_sound_at_successor) >>
    disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC)
  >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

(* Re-derive original JNZ distinct-labels from HOL-simplified form.
   HOL simplifies (!bb cond tl fl. ... ==> tl <> fl) to
   (!bb cond fl. JNZ ==> ops=[...fl;fl] ==> ~MEM bb bbs).
   range_successor_sound needs the original form. *)
Theorem jnz_distinct_labels_from_simplified:
  (!bb cond false_lbl.
     (LAST bb.bb_instructions).inst_opcode = JNZ ==>
     (LAST bb.bb_instructions).inst_operands =
       [cond; Label false_lbl; Label false_lbl] ==>
     ~MEM bb bbs) ==>
  (!bb cond true_lbl false_lbl.
     MEM bb bbs /\
     (LAST bb.bb_instructions).inst_opcode = JNZ /\
     (LAST bb.bb_instructions).inst_operands =
       [cond; Label true_lbl; Label false_lbl] ==>
     true_lbl <> false_lbl)
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[]
QED

(* Successor obligation adapted for the framework call context.
   Uses range_successor_sound but handles the JNZ hypothesis form mismatch. *)
Theorem range_successor_obligation:
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
     ~MEM bb fn.fn_blocks) ==>
  !bb fuel run_ctx s v.
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
    range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label 0) s /\
    (dfg_sound (dfg_build_function fn) s.vs_vars /\
     !vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
        vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
        MEM (Var u) dinst.inst_operands ==>
        u IN FDOM s.vs_vars) /\
    run_block fuel run_ctx bb s = OK v ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    range_sound (df_widen_at NONE (range_analyze fn) v.vs_current_bb 0) v /\
    dfg_sound (dfg_build_function fn) v.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM v.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM v.vs_vars)
Proof
  strip_tac
  >> imp_res_tac jnz_distinct_labels_from_simplified
  >> rpt gen_tac >> strip_tac
  >> mp_tac (SIMP_RULE std_ss [LET_THM] range_successor_sound)
  >> disch_then (qspecl_then [`fn`, `bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac)
  >> (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC))
  >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem range_sound_inst_idx:
  !X n s. range_sound X (s with vs_inst_idx := n) = range_sound X s
Proof
  rw[range_sound_def] >> Cases_on `X` >> simp[]
QED

(* Correctness of a 1:1 transform g guided by the range analysis.  Each
   instruction's simulation may use an index-indexed invariant P, which
   holds at every block's PHI boundary and is preserved by each
   non-terminator step.  Across blocks the lift carries DFG soundness and
   the operand closure, with range_successor_obligation. *)
Theorem range_pass_correct:
  !fn P g.
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb cond true_lbl false_lbl. MEM bb fn.fn_blocks /\
      (LAST bb.bb_instructions).inst_opcode = JNZ /\
      (LAST bb.bb_instructions).inst_operands =
        [cond; Label true_lbl; Label false_lbl] ==>
      true_lbl <> false_lbl) /\
    inst_transform_structural_1 g /\
    (!bb t. MEM bb fn.fn_blocks ==>
       P bb (phi_prefix_length bb.bb_instructions) t) /\
    (!bb idx fuel ctx t t'.
       MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
       t.vs_inst_idx = idx /\ P bb idx t /\
       ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
       step_inst fuel ctx (EL idx bb.bb_instructions) t = OK t' ==>
       P bb (SUC idx) (t' with vs_inst_idx := SUC idx)) /\
    (!bb idx fuel ctx t.
       MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
       t.vs_inst_idx = idx /\ P bb idx t /\
       range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label idx) t ==>
       (?e. step_inst fuel ctx (EL idx bb.bb_instructions) t = Error e) \/
       lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
         (step_inst fuel ctx (EL idx bb.bb_instructions) t)
         (step_inst fuel ctx
            (g (df_widen_at NONE (range_analyze fn) bb.bb_label idx)
               (EL idx bb.bb_instructions)) t)) ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
      dfg_sound (dfg_build_function fn) s.vs_vars /\
      (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
         vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
         MEM (Var u) dinst.inst_operands ==> u IN FDOM s.vs_vars) /\
      range_sound (df_widen_at NONE (range_analyze fn) s.vs_current_bb 0) s ==>
      (?e. run_blocks fuel ctx fn s = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx
          (analysis_function_transform_widen NONE (range_analyze fn)
             (\v inst. [g v inst]) fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!bb. MEM bb fn.fn_blocks ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb`
    by (rpt strip_tac >> irule MEM_lookup_block >>
        qpat_assum `ALL_DISTINCT _` mp_tac >>
        simp_tac std_ss [fn_labels_def] >> metis_tac[]) >>
  `!lbl idx. df_at NONE (widen_to_df (range_analyze fn)) lbl idx =
             df_widen_at NONE (range_analyze fn) lbl idx`
    by simp[widen_to_df_def, df_widen_at_def, dfAnalyzeDefsTheory.df_at_def] >>
  mp_tac (
    REWRITE_RULE [SIMP_RULE std_ss [LET_THM] (GSYM range_analyze_def)]
    (BETA_RULE (PURE_REWRITE_RULE [LET_DEF]
    (ISPECL [
      ``state_equiv {} : venom_state -> venom_state -> bool``,
      ``execution_equiv {} : venom_state -> venom_state -> bool``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn, fn.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn)``,
      ``fn : ir_function``,
      ``range_sound``,
      ``\s:venom_state. dfg_sound (dfg_build_function fn) s.vs_vars /\
          !vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
            vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
            MEM (Var u) dinst.inst_operands ==> u IN FDOM s.vs_vars``,
      ``\v inst. [(g : (string |-> value_range) option -> instruction ->
                       instruction) v inst]``]
    analysisSimProofsWidenTheory.df_analysis_pass_correct_widen_block_sim_proof)))) >>
  impl_tac
  >- (rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- (mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[])
      >- suspend "successor"
      >- suspend "block_sim"
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- metis_tac[range_sound_state_equiv]
      >- (rpt strip_tac >> imp_res_tac state_equiv_empty_eq >> gvs[] >>
          metis_tac[])
      >> rpt strip_tac >> fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  rpt strip_tac >> first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume range_pass_correct[successor]:
  rpt gen_tac >> strip_tac >>
  mp_tac range_successor_obligation >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> res_tac >> fs[]) >>
  disch_then (qspecl_then [`bb`, `fuel`, `run_ctx`, `s`, `v`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume range_pass_correct[block_sim]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `range_sound _ s` mp_tac >>
  REWRITE_TAC [abt_singleton_eq_mapi] >>
  qpat_assum `!lbl idx. df_at _ _ _ _ = _` (fn th => REWRITE_TAC [th]) >>
  strip_tac >>
  mp_tac (ISPECL [
    ``g : (string |-> value_range) option -> instruction -> instruction``,
    ``df_widen_at NONE (range_analyze fn) (bb : basic_block).bb_label``,
    ``(bb : basic_block).bb_instructions``] inst_transform_structural_1_mapi_phis) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  simp[run_block_def] >>
  qpat_x_assum `!s. eval_phis _ _ = _` (fn th => REWRITE_TAC [th]) >>
  qpat_x_assum `phi_prefix_length _ = _` (fn th => REWRITE_TAC [th]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >>
  qpat_assum `eval_phis s _ = _` (fn th => REWRITE_TAC [th]) >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
  mp_tac (BETA_RULE (Q.SPECL [
    `\i t. P bb i t /\
           range_sound (df_widen_at NONE (range_analyze fn) bb.bb_label i) t`,
    `\idx inst. g (df_widen_at NONE (range_analyze fn) bb.bb_label idx) inst`,
    `bb`, `fuel`, `run_ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
    exec_block_mapi_sim)) >>
  disch_then match_mp_tac >> rpt conj_tac
  >- (rpt gen_tac >> irule inst_transform_structural_1_terminator >>
      first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_x_assum `!bb idx fuel ctx t. _ ==> (?e. _) \/ _`
        (qspecl_then [`bb`, `i`, `fuel`, `run_ctx`, `t`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (qpat_x_assum `!bb idx fuel ctx t t'. _`
            (qspecl_then [`bb`, `i`, `fuel`, `run_ctx`, `t`, `t'`] mp_tac) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC) >>
      REWRITE_TAC [range_sound_inst_idx] >>
      mp_tac (Q.SPECL [`fn`, `bb.bb_label`, `bb`, `i`] range_intra_transfer) >>
      impl_tac
      >- (rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC >>
          qpat_x_assum `i < LENGTH _` mp_tac >> simp[]) >>
      disch_then (fn th => REWRITE_TAC [th]) >>
      mp_tac (Q.SPECL [`fn`, `fuel`, `run_ctx`,
        `df_widen_at NONE (range_analyze fn) bb.bb_label i`,
        `EL i bb.bb_instructions`, `t`, `t'`]
        (REWRITE_RULE [transfer_sound_def] range_transfer_sound)) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
  >- (simp_tac (srw_ss()) [] >>
      qpat_x_assum `!bb t. MEM bb fn.fn_blocks ==> P _ _ _` irule >>
      first_assum ACCEPT_TAC) >>
  REWRITE_TAC [range_sound_inst_idx] >>
  simp_tac (srw_ss()) [] >>
  mp_tac (Q.SPECL [`fn`, `bb`, `s`, `s_phi`] eval_phis_range_sound) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  REWRITE_TAC [range_sound_inst_idx]
QED

Finalise range_pass_correct
