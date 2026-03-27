(*
 * Analysis-Driven Simulation — Proofs (Main)
 *
 * TOP-LEVEL:
 *   df_analysis_pass_correct_sound_proof
 *   df_analysis_pass_correct_widen_sound_proof
 *   df_analysis_pass_correct_prepend_proof
 *   analysis_function_transform_compare_proof
 *
 * Depends on analysisSimProofsBase for all shared helpers.
 *)

Theory analysisSimProofs
Ancestors
  analysisSimProofsBase analysisSimProofsCompare
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState cfgAnalysisProps
Libs
  listTheory finite_mapTheory pred_setTheory stringTheory

(* Forward-specialized dataflow theorems for sound/widen proofs *)
val fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_proof));
val inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_inter_transfer_proof));
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));
val widen_fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeWidenProofsTheory.df_analyze_widen_fixpoint_proof));
val widen_inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeWidenProofsTheory.df_widen_at_inter_transfer_proof));
val widen_intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeWidenProofsTheory.df_widen_at_intra_transfer_proof));
val widen_entry_sound = SIMP_RULE (srw_ss()) [LET_THM]
  dfAnalyzeWidenProofsTheory.df_widen_entry_sound_proof;

(* Successors of cfg_dfs_pre labels are in cfg_dfs_pre.
   Follows from dfs_pre_walk_closure + dfs_pre_walk_visited_eq. *)
Theorem cfg_dfs_pre_succs_closed:
  !fn lbl.
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    EVERY (\t. MEM t (cfg_analyze fn).cfg_dfs_pre)
          (cfg_succs_of (cfg_analyze fn) lbl)
Proof
  rw[cfgDefsTheory.cfg_analyze_def, cfgDefsTheory.cfg_succs_of_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  Cases_on `entry_block fn` >> gvs[] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  qabbrev_tac `succs = build_succs fn.fn_blocks` >>
  qabbrev_tac `entry = x.bb_label` >>
  `MEM lbl (SND (dfs_pre_walk succs [] entry))` by gvs[] >>
  `MEM t (FST (dfs_pre_walk succs [] entry))` by
    metis_tac[cj 1 cfgHelpersTheory.dfs_pre_walk_closure] >>
  `set _0 = set pre` by (
    `set (FST (dfs_pre_walk succs [] entry)) =
     set [] UNION set (SND (dfs_pre_walk succs [] entry))` by
      metis_tac[cj 1 cfgHelpersTheory.dfs_pre_walk_visited_eq] >>
    gvs[]) >>
  `MEM t _0` by gvs[] >>
  metis_tac[]
QED

(* df_process_block only adds keys with FST = lbl to ds_inst *)
Triviality df_process_block_keys:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbl st k.
    k IN FDOM (df_process_block dir bottom join transfer edge_transfer
                 ctx entry_val cfg bbs lbl st).ds_inst ==>
    FST k = lbl \/ k IN FDOM st.ds_inst
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `k IN _` mp_tac >>
  simp[df_process_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> strip_tac
  >- (imp_res_tac dfAnalyzeProofsTheory.df_fold_block_keys >>
      fs[FLOOKUP_DEF])
  >- fs[]
QED

(* Key-domain invariant: all keys in df_analyze result have first component
   in cfg_dfs_pre. Uses combined P∧Q predicate for wl_iterate invariant. *)
Triviality df_analyze_keys_in_dfs_pre:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      dir = Forward /\
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps
    ==>
      !k. k IN FDOM result.ds_inst ==> MEM (FST k) cfg.cfg_dfs_pre
Proof
  simp[LET_THM] >> rpt strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `bbs = fn.fn_blocks` >>
  qabbrev_tac `process = df_process_block Forward bottom join transfer
                           edge_transfer ctx entry_val cfg bbs` >>
  qabbrev_tac `st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs)` >>
  (* Unfold df_analyze to wl_iterate, abbreviate the initial state *)
  `df_analyze Forward bottom join transfer edge_transfer ctx entry_val fn =
   SND (wl_iterate process (cfg_succs_of cfg) cfg.cfg_dfs_pre
     (case entry_val of NONE => st0
      | SOME (lbl,v) => st0 with ds_boundary := st0.ds_boundary |+ (lbl,v)))` by
    simp[df_analyze_def, LET_THM, Abbr `process`, Abbr `st0`, Abbr `cfg`,
         Abbr `bbs`] >>
  qabbrev_tac `st0' = case entry_val of NONE => st0
    | SOME (lbl,v) => st0 with ds_boundary := st0.ds_boundary |+ (lbl,v)` >>
  fs[] >>
  (* Now goal is: MEM (FST k) cfg.cfg_dfs_pre
     with k IN FDOM (SND (wl_iterate process ... st0')).ds_inst *)
  qsuff_tac
    `(\(st:'a df_state). P st /\
        !k. k IN FDOM st.ds_inst ==> MEM (FST k) cfg.cfg_dfs_pre)
     (SND (wl_iterate process (cfg_succs_of cfg) cfg.cfg_dfs_pre st0'))`
  >- (BETA_TAC >> rpt strip_tac >> res_tac) >>
  MATCH_MP_TAC (SIMP_RULE std_ss [LET_THM]
    worklistProofsTheory.wl_iterate_invariant_process_restricted) >>
  qexistsl_tac [`m`, `b`, `\l. MEM l cfg.cfg_dfs_pre`] >>
  BETA_TAC >> rpt conj_tac
  >| [ (* 1. monotonicity *)
       rpt gen_tac >> strip_tac >> fs[] >>
       qpat_x_assum `bounded_measure _ _ _ _` mp_tac >>
       simp[latticeDefsTheory.bounded_measure_def] >>
       strip_tac >> first_x_assum irule >> rpt conj_tac >> fs[] >>
       metis_tac[],
       (* 2. preservation *)
       rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
       rpt strip_tac >>
       qpat_x_assum `_ IN FDOM (process _ _).ds_inst` mp_tac >>
       simp[Abbr `process`] >> strip_tac >>
       imp_res_tac df_process_block_keys >> metis_tac[],
       (* 3. P st0' *)
       Cases_on `entry_val` >> fs[Abbr `st0'`] >>
       Cases_on `x` >> fs[],
       (* 4. Q st0': ds_inst is FEMPTY *)
       Cases_on `entry_val` >>
       fs[Abbr `st0'`, Abbr `st0`, init_df_state_def, FDOM_FEMPTY] >>
       Cases_on `x` >> fs[FDOM_FEMPTY],
       (* 5. bounded *)
       rpt strip_tac >>
       qpat_x_assum `bounded_measure _ _ _ _` mp_tac >>
       simp[latticeDefsTheory.bounded_measure_def] >>
       metis_tac[],
       (* 6. wl0 valid *)
       simp[EVERY_MEM],
       (* 7. deps closed *)
       rpt strip_tac >>
       metis_tac[cfg_dfs_pre_succs_closed, EVERY_MEM]
     ]
QED

(* For labels NOT in cfg_dfs_pre, df_at returns bottom.
   Proof: wl_iterate only processes labels from the worklist, which stays
   within cfg_dfs_pre (closed under successors). So ds_inst only has
   keys with first component in cfg_dfs_pre. *)
Triviality df_at_bottom_unreachable:
  !(dir : direction) (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (leq : 'a df_state -> 'a df_state -> bool)
   m b (P : 'a df_state -> bool).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block dir bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let deps = (case dir of
                  Forward => cfg_succs_of cfg
                | Backward => cfg_preds_of cfg) in
    let st0 = init_df_state bottom (MAP (\bb. bb.bb_label) bbs) in
    let result = df_analyze dir bottom join transfer edge_transfer
                            ctx entry_val fn in
      dir = Forward /\
      (!lbl st. P st ==> leq st (process lbl st)) /\
      (!lbl st. P st ==> P (process lbl st)) /\
      (case entry_val of NONE => P st0
       | SOME (lbl, v) =>
           P (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))) /\
      bounded_measure P leq m b /\
      wl_deps_complete process deps /\
      ~MEM lbl (cfg_analyze fn).cfg_dfs_pre
    ==>
      !idx. df_at bottom result lbl idx = bottom
Proof
  simp[LET_THM] >> rpt strip_tac >>
  simp[df_at_def] >>
  Cases_on `FLOOKUP (df_analyze Forward bottom join transfer edge_transfer
              ctx entry_val fn).ds_inst (lbl, idx)` >> simp[] >>
  (* SOME case: derive contradiction from key-domain invariant *)
  `!k. k IN FDOM (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn).ds_inst ==>
     MEM (FST k) (cfg_analyze fn).cfg_dfs_pre` by (
    MATCH_MP_TAC (SIMP_RULE (srw_ss()) [LET_THM] df_analyze_keys_in_dfs_pre) >>
    qexistsl_tac [`leq`, `m`, `b`, `P`] >> fs[]) >>
  `(lbl, idx) IN FDOM (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn).ds_inst` by fs[FLOOKUP_DEF] >>
  res_tac >> fs[]
QED

(* Two-sided join FOLDL soundness: when all list elements are
   universally sound and join preserves soundness from both sides. *)
Triviality foldl_sound_two_sided:
  !l (bottom : 'a) join sound.
    (!s. sound bottom s) /\
    (!a b s. sound a s /\ sound b s ==> sound (join a b) s) /\
    EVERY (\v. !s. sound v s) l ==>
    !s. sound (FOLDL join bottom l) s
Proof
  Induct
  >- (rpt strip_tac >> simp_tac (srw_ss()) [] >>
      qpat_x_assum `!s. sound bottom s` (fn th => ACCEPT_TAC (SPEC_ALL th)))
  >> rpt strip_tac >> simp_tac (srw_ss()) [] >>
  first_x_assum irule >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> qpat_assum `!a b s. _` irule >> rpt conj_tac
      >- (qpat_x_assum `!s. sound bottom s`
            (fn th => ACCEPT_TAC (SPEC_ALL th)))
      >> qpat_x_assum `EVERY _ _` mp_tac >>
      simp_tac (srw_ss()) [] >> strip_tac >>
      qpat_x_assum `!s. sound h s` (fn th => ACCEPT_TAC (SPEC_ALL th)))
  >> qpat_x_assum `EVERY _ _` mp_tac >>
  simp_tac (srw_ss()) []
QED

(* Transfer-sound chain: running original block from sound entry gives
   sound exit value. Uses the same idx-0 trick as analysis_block_sim. *)
(* Helper: terminator step_inst_base is idx-independent for OK results *)
Triviality term_step_base_idx_0:
  !inst s v.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK v ==>
    step_inst_base inst (s with vs_inst_idx := 0) = OK v
Proof
  rpt strip_tac >>
  `v.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  qabbrev_tac `f = \st:venom_state. st with vs_inst_idx := 0` >>
  `exec_result_map f (step_inst_base inst (s with vs_inst_idx := 0)) =
   exec_result_map f (step_inst_base inst s)` by
    (unabbrev_all_tac >>
     metis_tac[instIdxIndepTheory.terminator_step_inst_base_idx_norm0]) >>
  `exec_result_map f (step_inst_base inst s) = OK v` by
    (simp[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
     `v with vs_inst_idx := 0 = v` by
       simp[venom_state_component_equality] >> fs[]) >>
  fs[] >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := 0)` >>
  fs[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
  `v'.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  fs[venom_state_component_equality]
QED

(* Helper: apply transfer_sound to get soundness at SUC idx *)
Theorem transfer_sound_step:
  !sound transfer run_ctx inst fuel ctx s s' v_in v_out.
    transfer_sound sound transfer run_ctx /\
    sound v_in s /\
    step_inst fuel ctx inst s = OK s' /\
    v_out = transfer run_ctx inst v_in ==>
    sound v_out s'
Proof
  rw[transfer_sound_def] >> res_tac
QED

(* Transfer-sound chain through a block: running the original block from
   a state where sound(df_at lbl idx) gives sound(df_at lbl (SUC exit_idx))
   at the exit state. The exit index is wherever run_block terminates.
   
   Note: concludes at SUC of the terminator index, NOT at LENGTH.
   For well-formed blocks where the terminator is last, SUC exit = LENGTH. *)
Theorem transfer_sound_exit:
  !R_ok R_term sound transfer run_ctx bb bottom result.
    valid_state_rel R_ok R_term /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s v i.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      run_block fuel ctx bb s = OK v /\
      i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  rpt strip_tac >>
  `!n fuel ctx s.
     n = i + 1 - s.vs_inst_idx /\
     s.vs_inst_idx <= i /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) /\
     run_block fuel ctx bb s = OK v ==>
     sound (df_at bottom result bb.bb_label (SUC i)) v`
    suffices_by (
      disch_then (qspecl_then
        [`i + 1`, `fuel`, `ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by
        fs[venom_state_component_equality] >> simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `idx = s'.vs_inst_idx` >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `run_block fuel' ctx' bb s' =
   case step_inst fuel' ctx' inst s' of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else run_block fuel' ctx' bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel' ctx' inst s'` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = i`
    >- (
      (* At the terminator index: idx = i *)
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      Cases_on `s''.vs_halted` >- fs[] >>
      (* Non-halted: fs[] applies intra_fwd, rewrites df_at(SUC i) to
         transfer run_ctx inst (df_at lbl i). Also s'' = v. *)
      fs[] >>
      (* Goal: sound (transfer run_ctx inst (df_at lbl i)) v *)
      (* Use transfer_sound: need step_inst at idx=0 *)
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> fs[is_terminator_def]) >>
      `step_inst_base inst s' = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      metis_tac[transfer_sound_def]
    )
    >- (
      (* Before the terminator: step through non-terminator, advance idx *)
      `idx < i` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < i ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      fs[] >>
      (* Normalize step_inst to idx=0 *)
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      (* Derive soundness at SUC idx *)
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      `sound (df_at bottom result bb.bb_label (SUC idx))
             (s'' with vs_inst_idx := 0)` by
        metis_tac[transfer_sound_def, markerTheory.Abbrev_def] >>
      (* Apply IH *)
      first_x_assum (qspec_then `i + 1 - SUC idx` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
      simp[] >>
      metis_tac[transfer_sound_def, markerTheory.Abbrev_def]
    )
  )
  >> fs[AllCaseEqs()]
QED


(* ===== End-to-end dataflow pass correctness =====
 *
 * Given:
 *   - is_fixpoint: the analysis (df_analyze) has converged
 *   - Soundness conditions: transfer_sound, edge_transfer_sound, FOLDL-sound
 *   - Per-instruction simulation: analysis_inst_simulates
 * Prove: the transformed function gives lift_result-related results.
 *
 * The caller establishes is_fixpoint however they want (e.g., via
 * df_analyze_fixpoint_process_restricted with valid_lbl restriction).
 * This theorem only needs the fixpoint fact, not the convergence machinery.
 *
 * Forward direction only (backward has known counterexample, see
 * backwardCexScript.sml).
 *)

Theorem df_analysis_pass_correct_sound_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join transfer edge_transfer
                                   ctx entry_val cfg bbs in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (* Entry soundness: at the function entry, the analysis value is sound *)
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (* Successor soundness: after running a block to OK (not halted),
         the successor label is in dfs_pre and its entry value is sound *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx (analysis_function_transform bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  (* Derive entry label and dfs_pre membership *)
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
    ctx entry_val fn` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, analysisSimProofsBaseTheory.abt_label] >>
  (* Strengthen: add R_ok s1 s2, sound, MEM as induction invariant *)
  qsuff_tac
    `!fuel run_ctx s1 s2.
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       MEM s1.vs_current_bb cfg.cfg_dfs_pre /\
       sound (df_at bottom result s1.vs_current_bb 0) s1 ==>
       (?e. run_function fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel run_ctx fn s1)
         (run_function fuel run_ctx (function_map_transform bt fn) s2)`
  >- (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `ctx'`, `s`, `s`] mp_tac) >>
    impl_tac
    >- (rpt conj_tac
        >- (irule vsr_R_ok_refl >> metis_tac[])
        >- first_assum ACCEPT_TAC
        >- (fs[fn_entry_label_def, Abbr `cfg`] >>
            Cases_on `entry_block fn` >> gvs[] >>
            imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
            metis_tac[rich_listTheory.HEAD_MEM])
        >- metis_tac[])
    >> simp[analysis_function_transform_def])
  >>
  (* Main fuel induction *)
  Induct_on `fuel`
  >- (rw[run_function_def, lift_result_def])
  >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof,
       analysisSimProofsBaseTheory.abt_label] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb.bb_label = s2.vs_current_bb` by (
    fs[lookup_block_def, FIND_def] >> Cases_on `z` >> gvs[] >>
    imp_res_tac
      (prove(``!n P (l:'a list) i x. INDEX_FIND n P l = SOME (i,x) ==> P x``,
        Induct_on `l` >> rw[INDEX_FIND_def] >>
        gvs[AllCaseEqs()] >> metis_tac[])) >> gvs[]) >>
  (* sound at s2 via R_ok preservation *)
  sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  (* Per-block R_ok preservation: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    mp_tac (cj 1 run_block_preserves_R_proof) >>
    disch_then (qspecl_then [`R_ok`, `R_term`, `fn`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then drule_all >> simp[]) >>
  (* Per-block sim: run_block bb s2 ~ run_block (bt bb) s2 *)
  `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
      df_at bottom result bb.bb_label (SUC idx) =
      transfer ctx (EL idx bb.bb_instructions)
        (df_at bottom result bb.bb_label idx))` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`bottom`, `join`, `transfer`, `edge_transfer`, `ctx`,
       `entry_val`, `fn`, `bb.bb_label`, `bb`, `idx`] intra_fwd) >>
     impl_tac >- gvs[Abbr `result`, Abbr `cfg`] >>
     simp[Abbr `result`]) >>
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    simp_tac std_ss [Abbr `bt`] >>
    mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
      `result`, `transfer`, `ctx`]
      analysisSimProofsBaseTheory.analysis_block_sim) >>
    impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
      rpt strip_tac >> res_tac) >>
    disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`] mp_tac) >>
    impl_tac >- gvs[] >>
    simp[]) >>
  (* Case: run_block bb s2 errors *)
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  (* Compose: s1 ~ s2 ~ bt via transitivity *)
  `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  (* Case split on run_block result *)
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx (bt bb) s2` >>
  gvs[lift_result_def]
  (* Only OK-OK survives after gvs *)
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[venomExecProofsTheory.run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac venomExecProofsTheory.run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1` by
      metis_tac[] >>
    REWRITE_TAC [GSYM function_map_transform_def] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  (* Non-OK cases: Halt, Abort, IntRet *)
  >> (
    Cases_on `run_block fuel run_ctx bb s2` >> gvs[lift_result_def] >>
    Cases_on `run_block fuel run_ctx (bt bb) s2` >> gvs[lift_result_def])
QED

(* ===== Widening variant with soundness ===== *)

(* Bridge: convert df_widen_state to df_state so we can reuse
   the sound proof without duplicating it *)
val widen_to_df_def = Define `
  widen_to_df (st : 'a df_widen_state) : 'a df_state =
    <| ds_inst := st.dws_inst; ds_boundary := st.dws_boundary |>`;

Triviality df_widen_at_eq_df_at:
  !bottom st lbl idx.
    df_widen_at bottom st lbl idx = df_at bottom (widen_to_df st) lbl idx
Proof
  rw[df_widen_at_def, df_at_def, widen_to_df_def]
QED

Triviality abt_widen_eq_abt:
  !bottom result f bb.
    analysis_block_transform_widen bottom result f bb =
    analysis_block_transform bottom (widen_to_df result) f bb
Proof
  rw[analysis_block_transform_widen_def, analysis_block_transform_def,
     df_widen_at_eq_df_at]
QED

Triviality aft_widen_eq_aft:
  !bottom result f fn.
    analysis_function_transform_widen bottom result f fn =
    analysis_function_transform bottom (widen_to_df result) f fn
Proof
  rw[analysis_function_transform_widen_def, analysis_function_transform_def,
     function_map_transform_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  rw[FUN_EQ_THM, listTheory.MAP_EQ_f, abt_widen_eq_abt]
QED

Triviality df_widen_boundary_eq_df_boundary:
  !bottom st lbl.
    df_widen_boundary bottom st lbl = df_boundary bottom (widen_to_df st) lbl
Proof
  rw[df_widen_boundary_def, df_boundary_def, widen_to_df_def]
QED

(* Widening variant. Uses widen_to_df bridge to reduce to non-widen case.
 * The caller must establish is_fixpoint for the WIDEN process. *)
Theorem df_analysis_pass_correct_widen_sound_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (* Entry soundness *)
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_widen_at bottom result lbl 0) s) /\
      (* Successor soundness *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  (* Reduce to non-widen via bridge lemmas *)
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `wresult = df_analyze_widen Forward bottom join widen threshold
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `result = widen_to_df wresult` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, analysisSimProofsBaseTheory.abt_label] >>
  (* Strengthen with induction invariant *)
  qsuff_tac
    `!fuel run_ctx s1 s2.
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       MEM s1.vs_current_bb cfg.cfg_dfs_pre /\
       sound (df_at bottom result s1.vs_current_bb 0) s1 ==>
       (?e. run_function fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel run_ctx fn s1)
         (run_function fuel run_ctx (function_map_transform bt fn) s2)`
  >- (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `ctx'`, `s`, `s`] mp_tac) >>
    impl_tac
    >- (rpt conj_tac
        >- (irule vsr_R_ok_refl >> metis_tac[])
        >- first_assum ACCEPT_TAC
        >- (fs[fn_entry_label_def, Abbr `cfg`] >>
            Cases_on `entry_block fn` >> gvs[] >>
            imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
            metis_tac[rich_listTheory.HEAD_MEM])
        >- metis_tac[])
    >> simp[analysis_function_transform_def])
  >>
  Induct_on `fuel`
  >- (rw[run_function_def, lift_result_def])
  >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof,
       analysisSimProofsBaseTheory.abt_label] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb.bb_label = s2.vs_current_bb` by (
    fs[lookup_block_def, FIND_def] >> Cases_on `z` >> gvs[] >>
    imp_res_tac
      (prove(``!n P (l:'a list) i x. INDEX_FIND n P l = SOME (i,x) ==> P x``,
        Induct_on `l` >> rw[INDEX_FIND_def] >>
        gvs[AllCaseEqs()] >> metis_tac[])) >> gvs[]) >>
  sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    mp_tac (cj 1 run_block_preserves_R_proof) >>
    disch_then (qspecl_then [`R_ok`, `R_term`, `fn`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then drule_all >> simp[]) >>
  (* Intra-block transfer for widen *)
  `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
      df_at bottom result bb.bb_label (SUC idx) =
      transfer ctx (EL idx bb.bb_instructions)
        (df_at bottom result bb.bb_label idx))` by
    (rpt strip_tac >>
     qunabbrev_tac `result` >>
     ONCE_REWRITE_TAC [GSYM df_widen_at_eq_df_at] >>
     qunabbrev_tac `wresult` >>
     mp_tac (Q.SPECL [`bottom`, `join`, `widen`, `threshold`, `transfer`,
       `edge_transfer`, `ctx`, `entry_val`, `fn`,
       `bb.bb_label`, `bb`, `idx`] widen_intra_fwd) >>
     impl_tac >- (qunabbrev_tac `cfg` >> gvs[]) >>
     disch_then ACCEPT_TAC) >>
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    simp_tac std_ss [Abbr `bt`] >>
    mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
      `result`, `transfer`, `ctx`]
      analysisSimProofsBaseTheory.analysis_block_sim) >>
    impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
      rpt strip_tac >> res_tac) >>
    disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`] mp_tac) >>
    impl_tac >- gvs[] >>
    simp[]) >>
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[venomExecProofsTheory.run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac venomExecProofsTheory.run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    (* Successor soundness: already in df_at form thanks to initial simp *)
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1` by
      metis_tac[] >>
    REWRITE_TAC [GSYM function_map_transform_def] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  >> (
    Cases_on `run_block fuel run_ctx bb s2` >> gvs[lift_result_def] >>
    Cases_on `run_block fuel run_ctx (bt bb) s2` >> gvs[lift_result_def])
QED

(* ===== Generic function-level correctness, parameterized by block sim =====
   All function-level widen theorems are derived from this single proof.
   The block_sim hypothesis abstracts how per-block simulation is established
   (e.g. via analysis_block_sim, analysis_inst_sim_block_sim_inv, etc.). *)
Theorem df_analysis_pass_correct_widen_block_sim_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      (* Successor soundness - with state_inv *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (* Block simulation - abstract *)
      (!bb fuel run_ctx s.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
         lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom
           (widen_to_df (df_analyze_widen Forward bottom join widen
             threshold transfer edge_transfer ctx entry_val fn))
           bb.bb_label 0) s /\
         state_inv s ==>
         (?e. run_block fuel run_ctx bb s = Error e) \/
         lift_result R_ok R_term (run_block fuel run_ctx bb s)
           (run_block fuel run_ctx
             (analysis_block_transform bottom
               (widen_to_df (df_analyze_widen Forward bottom join widen
                 threshold transfer edge_transfer ctx entry_val fn)) f bb)
             s)) /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `wresult = df_analyze_widen Forward bottom join widen threshold
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `result = widen_to_df wresult` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, analysisSimProofsBaseTheory.abt_label] >>
  qsuff_tac
    `!fuel run_ctx s1 s2.
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       MEM s1.vs_current_bb cfg.cfg_dfs_pre /\
       sound (df_at bottom result s1.vs_current_bb 0) s1 /\
       state_inv s1 ==>
       (?e. run_function fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term (run_function fuel run_ctx fn s1)
         (run_function fuel run_ctx (function_map_transform bt fn) s2)`
  >- (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel`, `ctx'`, `s`, `s`] mp_tac) >>
    impl_tac
    >- (rpt conj_tac
        >- (irule vsr_R_ok_refl >> metis_tac[])
        >- first_assum ACCEPT_TAC
        >- (fs[fn_entry_label_def, Abbr `cfg`] >>
            Cases_on `entry_block fn` >> gvs[] >>
            imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
            metis_tac[rich_listTheory.HEAD_MEM])
        >- first_assum ACCEPT_TAC
        >- first_assum ACCEPT_TAC)
    >> simp[analysis_function_transform_def])
  >>
  Induct_on `fuel`
  >- (rw[run_function_def, lift_result_def])
  >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_function_def] >>
  simp[function_map_transform_def, lookup_block_map_proof,
       analysisSimProofsBaseTheory.abt_label] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb.bb_label = s2.vs_current_bb` by (
    fs[lookup_block_def, FIND_def] >> Cases_on `z` >> gvs[] >>
    imp_res_tac
      (prove(``!n P (l:'a list) i x. INDEX_FIND n P l = SOME (i,x) ==> P x``,
        Induct_on `l` >> rw[INDEX_FIND_def] >>
        gvs[AllCaseEqs()] >> metis_tac[])) >> gvs[]) >>
  sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  sg `state_inv s2`
  >- metis_tac[] >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    mp_tac (cj 1 run_block_preserves_R_proof) >>
    disch_then (qspecl_then [`R_ok`, `R_term`, `fn`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then drule_all >> simp[]) >>
  (* Block sim - from hypothesis *)
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    qpat_x_assum `!bb fuel run_ctx s. MEM bb fn.fn_blocks /\ _ ==> _`
      (qspecl_then [`bb`, `fuel`, `run_ctx`, `s2`] mp_tac) >>
    simp_tac std_ss [Abbr `bt`, Abbr `result`, Abbr `wresult`, Abbr `cfg`] >>
    impl_tac >- gvs[] >> simp[]) >>
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[venomExecProofsTheory.run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac venomExecProofsTheory.run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1 /\
     state_inv v1` by
      metis_tac[] >>
    REWRITE_TAC [GSYM function_map_transform_def] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  >> (
    Cases_on `run_block fuel run_ctx bb s2` >> gvs[lift_result_def] >>
    Cases_on `run_block fuel run_ctx (bt bb) s2` >> gvs[lift_result_def])
QED

(* Widening + state_inv: uses transfer_sound + analysis_inst_simulates *)
Theorem df_analysis_pass_correct_widen_sound_inv_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `wresult = df_analyze_widen Forward bottom join widen threshold
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `result = widen_to_df wresult` >>
  (* Reduce to df_analysis_pass_correct_widen_block_sim_proof
     by instantiating its block_sim with analysis_block_sim *)
  mp_tac df_analysis_pass_correct_widen_block_sim_proof >>
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  disch_then (qspecl_then [`R_ok`, `R_term`, `bottom`, `join`, `widen`,
    `threshold`, `transfer`, `edge_transfer`, `ctx`, `entry_val`, `fn`,
    `sound`, `state_inv`, `f`] mp_tac) >>
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  impl_tac
  >- (
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    (* Expand Abbrevs for hypotheses that don't match directly *)
    TRY (fs[Abbr `result`, Abbr `wresult`, Abbr `cfg`] >>
         first_assum ACCEPT_TAC) >>
    (* Block simulation - instantiate analysis_block_sim *)
    rpt strip_tac >>
    `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
        df_at bottom result bb.bb_label (SUC idx) =
        transfer ctx (EL idx bb.bb_instructions)
          (df_at bottom result bb.bb_label idx))` by (
      rpt strip_tac >>
      qunabbrev_tac `result` >>
      ONCE_REWRITE_TAC [GSYM df_widen_at_eq_df_at] >>
      qunabbrev_tac `wresult` >>
      mp_tac (Q.SPECL [`bottom`, `join`, `widen`, `threshold`, `transfer`,
        `edge_transfer`, `ctx`, `entry_val`, `fn`,
        `bb.bb_label`, `bb`, `idx`] widen_intra_fwd) >>
      impl_tac >- gvs[Abbr `cfg`] >>
      disch_then ACCEPT_TAC) >>
    mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
      `result`, `transfer`, `ctx`]
      analysisSimProofsBaseTheory.analysis_block_sim) >>
    impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
      rpt strip_tac >> res_tac) >>
    disch_then (qspecl_then [`fuel`, `run_ctx`, `s`] mp_tac) >>
    impl_tac >- gvs[] >>
    simp[Abbr `result`, Abbr `wresult`]) >>
  simp[Abbr `result`, Abbr `wresult`]
QED

(* Widening + state_inv + transfer_sound_wf + per-inst state_inv threading *)
Theorem df_analysis_pass_correct_widen_sound_inv2_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join widen threshold
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block_widen Forward bottom join widen threshold
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze_widen Forward bottom join widen threshold
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      transfer_sound_wf sound transfer ctx /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_widen_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (!fuel ctx' v inst s.
         sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
         (?e. step_inst fuel ctx' inst s = Error e) \/
         lift_result R_ok R_term (step_inst fuel ctx' inst s)
           (run_insts fuel ctx' (f v inst) s)) /\
      inst_transform_structural f /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!fuel ctx' bb inst s s'.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         inst_wf inst /\
         state_inv (s with vs_inst_idx := 0) /\
         step_inst fuel ctx' inst s = OK s' ==>
         state_inv (s' with vs_inst_idx := 0)) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_function fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx' fn s)
          (run_function fuel ctx'
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `wresult = df_analyze_widen Forward bottom join widen threshold
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `result = widen_to_df wresult` >>
  (* Reduce to block_sim via analysis_block_sim_inv *)
  mp_tac df_analysis_pass_correct_widen_block_sim_proof >>
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  disch_then (qspecl_then [`R_ok`, `R_term`, `bottom`, `join`, `widen`,
    `threshold`, `transfer`, `edge_transfer`, `ctx`, `entry_val`, `fn`,
    `sound`, `state_inv`, `f`] mp_tac) >>
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  impl_tac
  >- (
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    (* Expand Abbrevs for hypotheses that don't match directly *)
    TRY (fs[Abbr `result`, Abbr `wresult`, Abbr `cfg`] >>
         first_assum ACCEPT_TAC) >>
    (* Block simulation - instantiate analysis_block_sim_inv *)
    rpt strip_tac >>
    `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
        df_at bottom result bb.bb_label (SUC idx) =
        transfer ctx (EL idx bb.bb_instructions)
          (df_at bottom result bb.bb_label idx))` by (
      rpt strip_tac >>
      qunabbrev_tac `result` >>
      ONCE_REWRITE_TAC [GSYM df_widen_at_eq_df_at] >>
      qunabbrev_tac `wresult` >>
      mp_tac (Q.SPECL [`bottom`, `join`, `widen`, `threshold`, `transfer`,
        `edge_transfer`, `ctx`, `entry_val`, `fn`,
        `bb.bb_label`, `bb`, `idx`] widen_intra_fwd) >>
      impl_tac >- gvs[Abbr `cfg`] >>
      disch_then ACCEPT_TAC) >>
    mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `state_inv`, `f`, `bb`,
      `bottom`, `result`, `transfer`, `ctx`]
      analysisSimProofsBaseTheory.analysis_block_sim_inv) >>
    impl_tac >- (
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY (fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
           rpt strip_tac >> res_tac >> NO_TAC)) >>
    disch_then (qspecl_then [`fuel`, `run_ctx`, `s`] mp_tac) >>
    impl_tac >- gvs[] >>
    simp[Abbr `result`, Abbr `wresult`]) >>
  simp[Abbr `result`, Abbr `wresult`]
QED

(* ===== Prepend correctness ===== *)

(* Label of prepend-transformed block = original label *)
Triviality abtp_label:
  !bottom result prepend f bb.
    (analysis_block_transform_prepend bottom result prepend f bb).bb_label =
    bb.bb_label
Proof
  simp[analysis_block_transform_prepend_def]
QED

(* Prepend-aware pass correctness.
   Extends df_analysis_pass_correct_sound_proof for transforms that
   add new instructions before each block. *)
Theorem df_analysis_pass_correct_prepend_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list)
   (prepend : string -> instruction list).
    let cfg = cfg_analyze fn in
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    let fn' = analysis_function_transform_prepend
                bottom result prepend f fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint (df_process_block Forward bottom join transfer edge_transfer
                     ctx entry_val cfg fn.fn_blocks) cfg.cfg_dfs_pre result /\
      transfer_sound sound transfer ctx /\
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v) /\
      analysis_inst_simulates R_ok R_term sound f /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* Prepend succeeds and preserves R_ok *)
      (!lbl fuel ctx s.
         s.vs_inst_idx = 0 ==>
         ?s'. run_insts fuel ctx (prepend lbl) s = OK s' /\ R_ok s s') /\
      (* Prepend instructions are non-terminator, non-INVOKE *)
      (!lbl inst. MEM inst (prepend lbl) ==>
         ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE) /\
      (* Operand agreement for full transformed function *)
      (!bb inst x.
         MEM bb fn'.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_function fuel ctx fn s = Error e) \/
        lift_result R_ok R_term (run_function fuel ctx fn s)
          (run_function fuel ctx fn' s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac
  \\ qabbrev_tac `cfg = cfg_analyze fn`
  \\ qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
       ctx entry_val fn`
  \\ qabbrev_tac `bt = analysis_block_transform bottom result f`
  \\ qabbrev_tac `btp = analysis_block_transform_prepend bottom result prepend f`
  \\ `!b. (bt b).bb_label = b.bb_label` by
       simp[Abbr `bt`, abt_label]
  \\ `!b. (btp b).bb_label = b.bb_label` by
       simp[Abbr `btp`, abtp_label]
  (* Strengthen: add R_ok s1 s2, sound, MEM as induction invariant *)
  \\ qsuff_tac
       `!fuel run_ctx s1 s2.
          R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
          MEM s1.vs_current_bb cfg.cfg_dfs_pre /\
          sound (df_at bottom result s1.vs_current_bb 0) s1 ==>
          (?e. run_function fuel run_ctx fn s1 = Error e) \/
          lift_result R_ok R_term (run_function fuel run_ctx fn s1)
            (run_function fuel run_ctx (function_map_transform btp fn) s2)`
  >- (
    rpt strip_tac
    \\ first_x_assum (qspecl_then [`fuel`, `ctx'`, `s`, `s`] mp_tac)
    \\ impl_tac
    >- (rpt conj_tac
        >- (irule vsr_R_ok_refl >> metis_tac[])
        >- first_assum ACCEPT_TAC
        >- (fs[fn_entry_label_def, Abbr `cfg`]
            \\ Cases_on `entry_block fn` >> gvs[]
            \\ imp_res_tac cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first
            \\ metis_tac[rich_listTheory.HEAD_MEM])
        >- metis_tac[])
    \\ simp[analysis_function_transform_prepend_def, Abbr `btp`])
  (* Main fuel induction *)
  \\ Induct_on `fuel`
  >- (rw[run_function_def, lift_result_def])
  \\ rpt gen_tac \\ strip_tac
  \\ `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
      (s1.vs_halted <=> s2.vs_halted)` by
       metis_tac[vsr_R_ok_fields]
  \\ ONCE_REWRITE_TAC[run_function_def]
  \\ simp[function_map_transform_def, lookup_block_map_proof, abtp_label,
          Abbr `btp`]
  \\ Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  \\ rename1 `lookup_block _ _ = SOME bb`
  \\ imp_res_tac venomExecProofsTheory.lookup_block_MEM
  \\ `bb.bb_label = s2.vs_current_bb` by (
       fs[lookup_block_def, FIND_def] >> Cases_on `z` >> gvs[] >>
       imp_res_tac
         (prove(``!n P (l:'a list) i x. INDEX_FIND n P l = SOME (i,x) ==> P x``,
           Induct_on `l` >> rw[INDEX_FIND_def] >>
           gvs[AllCaseEqs()] >> metis_tac[])) >> gvs[])
  (* sound at s2 via R_ok preservation *)
  \\ sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
        (fn th => irule th) >>
      qexists_tac `s1` >> simp[])
  (* Step 1: R_ok bridge on original bb: run_block bb s1 ~ run_block bb s2 *)
  \\ `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                               (run_block fuel run_ctx bb s2)` by (
       mp_tac (cj 1 run_block_preserves_R_proof) >>
       disch_then (qspecl_then [`R_ok`, `R_term`, `fn`] mp_tac) >>
       impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
       disch_then drule_all >> simp[])
  (* Intra-block transfer for analysis_block_sim *)
  \\ `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
         df_at bottom result bb.bb_label (SUC idx) =
         transfer ctx (EL idx bb.bb_instructions)
           (df_at bottom result bb.bb_label idx))` by
       (rpt strip_tac >>
        mp_tac (Q.SPECL [`bottom`, `join`, `transfer`, `edge_transfer`, `ctx`,
          `entry_val`, `fn`, `bb.bb_label`, `bb`, `idx`] intra_fwd) >>
        impl_tac >- gvs[Abbr `result`, Abbr `cfg`] >>
        simp[Abbr `result`])
  (* Step 2: Block sim: run_block bb s2 ~ run_block (bt bb) s2 *)
  \\ `(?e. run_block fuel run_ctx bb s2 = Error e) \/
      lift_result R_ok R_term (run_block fuel run_ctx bb s2)
        (run_block fuel run_ctx (bt bb) s2)` by (
       simp_tac std_ss [Abbr `bt`] >>
       mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
         `result`, `transfer`, `ctx`]
         analysis_block_sim) >>
       impl_tac >- (
         rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >>
         fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
         rpt strip_tac >> res_tac) >>
       disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`] mp_tac) >>
       impl_tac >- gvs[] >>
       simp[])
  (* Handle error *)
  \\ Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  \\ `lift_result R_ok R_term (run_block fuel run_ctx bb s2)
                               (run_block fuel run_ctx (bt bb) s2)` by metis_tac[]
  (* Step 3: Prepend insertion: run_block (bt bb) s2 ~ run_block (btp bb) s2 *)
  \\ qabbrev_tac `btp = analysis_block_transform_prepend bottom result prepend f`
  \\ `!b. (btp b).bb_label = b.bb_label` by
       simp[Abbr `btp`, abtp_label]
  \\ `lift_result R_ok R_term (run_block fuel run_ctx (bt bb) s2)
                                (run_block fuel run_ctx (btp bb) s2)` by (
    irule run_block_with_prefix >> rpt conj_tac
    (* operand condition for (bt bb) instructions *)
    >- (rpt strip_tac
        \\ `MEM (btp bb)
              (analysis_function_transform_prepend bottom result prepend f fn).fn_blocks` by
              (simp[analysis_function_transform_prepend_def,
                    function_map_transform_def, MEM_MAP] >>
               qexists_tac `bb` >> simp[Abbr `btp`])
        \\ `MEM inst (btp bb).bb_instructions` by
              (simp[Abbr `btp`, analysis_block_transform_prepend_def,
                    MEM_APPEND] >>
               DISJ2_TAC >>
               qpat_x_assum `MEM inst (bt bb).bb_instructions` mp_tac >>
               simp[Abbr `bt`, analysis_block_transform_def])
        \\ res_tac)
    >- first_assum ACCEPT_TAC  (* R_ok trans *)
    >- first_assum ACCEPT_TAC  (* R_term trans *)
    >- simp[Abbr `btp`, Abbr `bt`, analysis_block_transform_prepend_def,
            analysis_block_transform_def]  (* label equality *)
    >- first_assum ACCEPT_TAC  (* vs_inst_idx *)
    >- (qexists_tac `prepend bb.bb_label` >> rpt conj_tac
        >- (first_x_assum
              (qspecl_then [`bb.bb_label`, `fuel`, `run_ctx`, `s2`] mp_tac) >>
            simp[])
        >- simp[Abbr `btp`, Abbr `bt`, analysis_block_transform_prepend_def,
                analysis_block_transform_def]
        >> (fs[EVERY_MEM] >> rpt strip_tac >> res_tac))
    >> first_assum ACCEPT_TAC  (* valid_state_rel *))
  (* Compose steps 1+2+3: bb s1 ~ bb s2 ~ bt s2 ~ btp s2 *)
  \\ `lift_result R_ok R_term (run_block fuel run_ctx bb s1)
                               (run_block fuel run_ctx (btp bb) s2)` by (
       irule lift_result_trans_proof
       \\ conj_tac >- first_assum ACCEPT_TAC
       \\ conj_tac >- first_assum ACCEPT_TAC
       \\ qexists_tac `run_block fuel run_ctx (bt bb) s2`
       \\ conj_tac
       >- (irule lift_result_trans_proof
           \\ conj_tac >- first_assum ACCEPT_TAC
           \\ conj_tac >- first_assum ACCEPT_TAC
           \\ qexists_tac `run_block fuel run_ctx bb s2`
           \\ conj_tac >> first_assum ACCEPT_TAC)
       \\ first_assum ACCEPT_TAC)
  (* Case split on run_block results for IH *)
  \\ Cases_on `run_block fuel run_ctx bb s1`
  \\ Cases_on `run_block fuel run_ctx (btp bb) s2`
  \\ gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2`
    \\ `~v1.vs_halted` by metis_tac[venomExecProofsTheory.run_block_OK_not_halted]
    \\ `~v2.vs_halted` by metis_tac[vsr_R_ok_fields]
    \\ simp[lift_result_def]
    \\ imp_res_tac venomExecProofsTheory.run_block_OK_inst_idx_0
    \\ `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields]
    \\ `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
        sound (df_at bottom result v1.vs_current_bb 0) v1` by
         metis_tac[]
    \\ REWRITE_TAC [GSYM function_map_transform_def]
    \\ first_x_assum irule \\ simp[]
    \\ rpt conj_tac >> first_assum ACCEPT_TAC)
  >> gvs[lift_result_def]
QED

(* ===== Transform comparison ===== *)

Triviality aft_fn_blocks:
  !bottom result f fn.
    (analysis_function_transform bottom result f fn).fn_blocks =
    MAP (analysis_block_transform bottom result f) fn.fn_blocks
Proof
  simp[analysis_function_transform_def, function_map_transform_def]
QED

(* Compare two analysis_function_transforms of the same function.
   Useful when a pass decomposes into substitution + elimination phases
   that use different transform functions on the same analysis result. *)
Theorem analysis_function_transform_compare_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f1 : 'a -> instruction -> instruction list)
   (f2 : 'a -> instruction -> instruction list) fn.
    let fn1 = analysis_function_transform bottom result f1 fn in
    let fn2 = analysis_function_transform bottom result f2 fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb idx fuel ctx s.
       MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions ==>
       let inst = EL idx bb.bb_instructions in
       let v = df_at bottom result bb.bb_label idx in
       (?e. run_insts fuel ctx (f1 v inst) s = Error e) \/
       lift_result R_ok R_term
         (run_insts fuel ctx (f1 v inst) s)
         (run_insts fuel ctx (f2 v inst) s)) /\
    inst_transform_structural f1 /\
    inst_transform_structural f2 /\
    fn_inst_wf fn /\
    (!bb inst x.
       MEM bb fn1.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_function fuel ctx fn1 s = Error e) \/
      lift_result R_ok R_term
        (run_function fuel ctx fn1 s)
        (run_function fuel ctx fn2 s)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac
  \\ simp[analysis_function_transform_def]
  \\ irule analysisSimProofsCompareTheory.block_sim_function_compare
  \\ simp[abt_label]
  \\ REWRITE_TAC [GSYM aft_fn_blocks]
  \\ rpt conj_tac
  \\ TRY (first_assum ACCEPT_TAC)
  (* Remaining: per-block sim (single goal) *)
  \\ rpt strip_tac
  \\ drule venomExecProofsTheory.lookup_block_MEM \\ strip_tac
  \\ irule analysisSimProofsCompareTheory.analysis_block_compare
  \\ REWRITE_TAC [GSYM aft_fn_blocks]
  \\ rpt conj_tac
  \\ TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac
      \\ qpat_assum `!bb inst x. MEM bb _ /\ MEM inst _ /\ _ ==> _`
           (qspecl_then [`analysis_block_transform bottom result f1 bb`,
                         `inst`, `x`] mp_tac)
      \\ (impl_tac >- (
            rpt conj_tac
            >- (REWRITE_TAC [aft_fn_blocks, listTheory.MEM_MAP]
                \\ qexists_tac `bb`
                \\ REWRITE_TAC [analysis_block_transform_def]
                \\ first_assum ACCEPT_TAC)
            >- (simp_tac (srw_ss()) [analysis_block_transform_def]
                \\ first_assum ACCEPT_TAC)
            \\ first_assum ACCEPT_TAC))
      \\ disch_then drule
      \\ disch_then ACCEPT_TAC)
  >- (rpt strip_tac
      \\ qpat_assum `!bb idx fuel ctx s. _`
           (qspecl_then [`bb`, `i`] mp_tac)
      \\ simp_tac std_ss [LET_THM]
      \\ (impl_tac >- (rpt conj_tac \\ first_assum ACCEPT_TAC))
      \\ simp_tac std_ss [])
  (* Goal 3: EVERY inst_wf *)
  \\ REWRITE_TAC [listTheory.EVERY_MEM] \\ rpt strip_tac
  \\ qpat_assum `fn_inst_wf _` mp_tac
  \\ REWRITE_TAC [venomWfTheory.fn_inst_wf_def]
  \\ disch_then drule \\ disch_then drule \\ simp_tac std_ss []
QED

(* After running a block OK, the successor block is in cfg_dfs_pre *)
Theorem successor_in_cfg_dfs_pre:
  !fn bb fuel ctx s v.
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecProofsTheory.run_block_ok_nonempty] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecProofsTheory.run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgHelpersTheory.bb_succs_in_cfg_succs] >>
  imp_res_tac cfg_dfs_pre_succs_closed >> fs[EVERY_MEM]
QED
