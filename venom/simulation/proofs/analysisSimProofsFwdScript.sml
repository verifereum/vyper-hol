(*
 * Analysis-Driven Simulation — Proofs (Part 5: Forward Analysis)
 *
 * Main theorems:
 *   analysis_function_transform_compare_proof
 *   successor_in_cfg_dfs_pre
 *   fwd_df_at_entry_eq_joined, fwd_df_at_exit_not_none
 *   fwd_joined_sound_from_pred, fwd_successor_entry_sound
 *   fwd_df_at_entry_not_none
 *)

Theory analysisSimProofsFwd
Ancestors
  analysisSimProofsPrepend analysisSimProofsWiden analysisSimProofsSound analysisSimProofs analysisSimProofsBase analysisSimProofsCompare
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState venomWf cfgAnalysisProps execEquivProofs
  list finite_map pred_set string

(* Forward-specialized dataflow theorems for fwd proofs *)
val inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_inter_transfer_proof));
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));

Triviality aft_fn_blocks:
  !bottom result f fn.
    (analysis_function_transform bottom result f fn).fn_blocks =
    MAP (analysis_block_transform bottom result f) fn.fn_blocks
Proof
  simp[analysis_function_transform_def, function_map_transform_def]
QED

(* Boundary lemma: abt bb is in aft fn whenever bb is in fn.fn_blocks *)
Triviality abt_mem_aft_fn_blocks:
  !bottom result f fn bb.
    MEM bb fn.fn_blocks ==>
    MEM (analysis_block_transform bottom result f bb)
        (analysis_function_transform bottom result f fn).fn_blocks
Proof
  rpt strip_tac >>
  simp[aft_fn_blocks, MEM_MAP] >>
  qexists_tac `bb` >> simp[]
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
       lift_result R_ok R_term R_term
         (run_insts fuel ctx (f1 v inst) s)
         (run_insts fuel ctx (f2 v inst) s)) /\
    inst_transform_structural f1 /\
    inst_transform_structural f2 /\
    wf_function fn /\
    fn_inst_wf fn /\
    (!bb inst x.
       MEM bb fn1.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_blocks fuel ctx fn1 s = Error e) \/
      lift_result R_ok R_term R_term
        (run_blocks fuel ctx fn1 s)
        (run_blocks fuel ctx fn2 s)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  simp[analysis_function_transform_def] >>
  irule analysisSimProofsCompareTheory.block_sim_function_compare >>
  simp[abt_label] >>
  REWRITE_TAC [GSYM aft_fn_blocks] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  (* Remaining: per-block sim (single goal) *)
  rpt strip_tac >>
  irule analysisSimProofsCompareTheory.analysis_run_block_compare >>
  REWRITE_TAC [GSYM aft_fn_blocks] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  (* 4 remaining goals *)
  rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!bb inst x. MEM bb _ /\ MEM inst _ /\ _ ==> _`
           (qspecl_then [`analysis_block_transform bottom result f1 bb`,
                         `inst`, `x`] mp_tac) >>
      impl_tac >- (
        rpt conj_tac >~
        [`MEM (analysis_block_transform _ _ _ bb) _`]
        >- (simp[analysisSimDefsTheory.analysis_function_transform_def,
                 passSimulationDefsTheory.function_map_transform_def, MEM_MAP] >>
            qexists_tac `bb` >> simp[] >>
            metis_tac[venomExecProofsTheory.lookup_block_MEM]) >~
        [`MEM inst _`]
        >- (simp[analysis_block_transform_def] >> first_assum ACCEPT_TAC) >>
        first_assum ACCEPT_TAC) >>
      disch_then drule >>
      disch_then ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!bb idx fuel ctx s. _`
           (qspecl_then [`bb`, `i`] mp_tac) >>
      simp_tac std_ss [LET_THM] >>
      impl_tac >- (
        rpt conj_tac >-
          metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
        first_assum ACCEPT_TAC) >>
      simp_tac std_ss [])
  >- (`bb_well_formed bb` by
        metis_tac[venomExecProofsTheory.wf_function_bb_well_formed,
                 venomExecProofsTheory.lookup_block_MEM] >>
      fs[venomWfTheory.fn_inst_wf_def, EVERY_MEM] >>
      metis_tac[venomExecProofsTheory.lookup_block_MEM])
  >- (REWRITE_TAC[listTheory.EVERY_MEM] >> rpt strip_tac >>
      metis_tac[venomExecProofsTheory.lookup_block_MEM,
                venomWfTheory.fn_inst_wf_def])
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
    exec_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecProofsTheory.exec_block_ok_nonempty] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecProofsTheory.exec_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgHelpersTheory.bb_succs_in_cfg_succs] >>
  imp_res_tac cfg_dfs_pre_succs_closed >> fs[EVERY_MEM]
QED

(* ===== General forward analysis successor entry soundness =====
   Shared infrastructure for all forward dataflow analysis passes.
   Parameters: bottom, join, transfer, edge_transfer, ctx, entry_val, sound.
   Avoids duplicating 6 boilerplate helpers per pass. *)

(* At fixpoint (Forward), df_at bottom result lbl 0 = joined value. *)
Theorem fwd_df_at_entry_eq_joined:
  !(bottom : 'a) join transfer edge_transfer ctx entry_val fn lbl.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    wf_function fn /\
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
    ==>
    df_at bottom result lbl 0 =
    df_joined_val Forward bottom join edge_transfer ctx entry_val
      (cfg_analyze fn) result lbl
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  (* Derive lookup_block from wf_function + MEM lbl cfg_dfs_pre *)
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by (
    `cfg_reachable_of (cfg_analyze fn) lbl` by (
      mp_tac (Q.SPEC `fn` cfgAnalysisPropsTheory.cfg_analyze_reachable_sets) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      strip_tac >> gvs[EXTENSION, IN_DEF]) >>
    `MEM lbl (fn_labels fn)` by
      metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels] >>
    gvs[venomInstTheory.fn_labels_def, MEM_MAP] >>
    rename [`MEM blk fn.fn_blocks`] >>
    qexists_tac `blk` >>
    irule venomExecProofsTheory.MEM_lookup_block >>
    gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  mp_tac inter_fwd >>
  disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
    `ctx`, `entry_val`, `fn`, `lbl`, `bb`] mp_tac) >> simp[]
QED

(* At fixpoint, if transfer always preserves SOME (non-bottom), then
   df_at at any instruction index <= LENGTH instrs is not NONE. *)
Triviality fwd_df_at_not_none_idx[local]:
  !(bottom : 'a option) join transfer edge_transfer ctx entry_val fn lbl bb.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    (!inst v. v <> NONE ==> transfer ctx inst v <> NONE) /\
    df_at bottom result lbl 0 <> NONE
    ==>
    !n. n <= LENGTH bb.bb_instructions ==>
        df_at bottom result lbl n <> NONE
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  Induct >> simp[] >> strip_tac >>
  drule_all intra_fwd >> strip_tac >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  first_x_assum match_mp_tac >>
  first_x_assum irule >> simp[]
QED

(* Corollary: exit value is not NONE *)
Theorem fwd_df_at_exit_not_none:
  !(bottom : 'a option) join transfer edge_transfer ctx entry_val fn lbl bb.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    (!inst v. v <> NONE ==> transfer ctx inst v <> NONE) /\
    df_at bottom result lbl 0 <> NONE
    ==>
    df_at bottom result lbl (LENGTH bb.bb_instructions) <> NONE
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  irule (SIMP_RULE std_ss [LET_THM] fwd_df_at_not_none_idx) >>
  rpt conj_tac >> simp[]
QED

(* ===== General joined-value soundness from one predecessor ===== *)

(* General FOLDL soundness: if one member is sound and non-NONE,
   the FOLDL result is sound, given that join preserves soundness
   from both sides and preserves non-NONE-ness. *)
(* General FOLDL soundness: if join preserves soundness from both sides,
   and one element of acc::vals is sound and non-NONE,
   then FOLDL join acc vals is sound. *)
Triviality fwd_foldl_join_sound_gen[local]:
  !(join : 'a option -> 'a option -> 'a option)
   (sound : 'a option -> 'b -> bool) vals acc v s.
    (!a b s. sound a s /\ a <> NONE ==> sound (join a b) s) /\
    (!a b s. sound b s /\ b <> NONE ==> sound (join a b) s) /\
    (!a b. a <> NONE \/ b <> NONE ==> join a b <> NONE) /\
    MEM v (acc :: vals) /\ v <> NONE /\ sound v s ==>
    sound (FOLDL join acc vals) s
Proof
  Induct_on `vals` >> simp[] >> rpt strip_tac >> gvs[] >>
  (* Step case: need sound (FOLDL join (join acc h) vals) s *)
  first_x_assum (qspecl_then [`join`, `sound`, `join acc h`] mp_tac) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexists_tac `v` >> simp[]
QED

(* Corollary: if MEM v vals and v is sound/non-NONE, FOLDL join NONE vals is sound. *)
Triviality fwd_foldl_join_sound[local]:
  !(join : 'a option -> 'a option -> 'a option)
   (sound : 'a option -> 'b -> bool) vals v s.
    (!a b s. sound a s /\ a <> NONE ==> sound (join a b) s) /\
    (!a b s. sound b s /\ b <> NONE ==> sound (join a b) s) /\
    (!a b. a <> NONE \/ b <> NONE ==> join a b <> NONE) /\
    MEM v vals /\ v <> NONE /\ sound v s ==>
    sound (FOLDL join NONE vals) s
Proof
  rpt strip_tac >> irule fwd_foldl_join_sound_gen >>
  simp[] >> conj_tac >- metis_tac[] >>
  qexists_tac `v` >> simp[MEM]
QED

(* General: if one predecessor's boundary is sound and non-NONE,
   then df_joined_val is sound.

   Hypotheses:
   H1-H3: join preserves soundness (left, right) and non-NONE-ness
   H4: entry value wrapping preserves soundness
   H5-H7: MEM nbr, edge_transfer boundary <> NONE, sound of edge_transfer boundary

   When edge_transfer is identity: H5-H7 simplify to boundary conditions. *)
Theorem fwd_joined_sound_from_pred:
  !(join : 'a option -> 'a option -> 'a option)
   (edge_transfer : 'b -> string -> string -> 'a option -> 'a option)
   (ctx : 'b) (entry_val : (string # 'a option) option) cfg
   (result : 'a option df_state)
   (sound : 'a option -> 'd -> bool) fn lbl nbr v.
    (* H1: join preserves soundness from left *)
    (!a b s. sound a s /\ a <> NONE ==> sound (join a b) s) /\
    (* H2: join preserves soundness from right *)
    (!a b s. sound b s /\ b <> NONE ==> sound (join a b) s) /\
    (* H3: join preserves non-NONE *)
    (!a b. a <> NONE \/ b <> NONE ==> join a b <> NONE) /\
    (* H4: entry wrapping preserves soundness *)
    (!ev_lbl ev a s. entry_val = SOME (ev_lbl, ev) ==>
                     sound a s ==> sound (join ev a) s) /\
    (* H5: MEM nbr *)
    MEM nbr (cfg_preds_of cfg lbl) /\
    (* H6: edge_transfer boundary <> NONE *)
    edge_transfer ctx nbr lbl (df_boundary NONE result nbr) <> NONE /\
    (* H7: soundness of edge_transferred boundary *)
    sound (edge_transfer ctx nbr lbl (df_boundary NONE result nbr)) v
    ==>
    sound (df_joined_val Forward NONE join edge_transfer ctx entry_val
             cfg result lbl) v
Proof
  rpt strip_tac >>
  simp[df_joined_val_def, LET_THM] >>
  Cases_on `MAP (\nbr'. edge_transfer ctx nbr' lbl
                          (df_boundary NONE result nbr'))
                (cfg_preds_of cfg lbl)` >>
  gvs[MAP_EQ_NIL, MEM] >>
  (* Establish FOLDL soundness on h::t *)
  `sound (FOLDL join NONE (h::t)) v` by suspend "foldl" >>
  Cases_on `entry_val`
  >- (FULL_SIMP_TAC std_ss [FOLDL])
  >>
  rename1 `SOME ev` >> Cases_on `ev` >> simp[] >>
  IF_CASES_TAC >> gvs[FOLDL]
QED

Resume fwd_joined_sound_from_pred[foldl]:
  irule fwd_foldl_join_sound >> simp[] >>
  qexists_tac `edge_transfer ctx nbr lbl (df_boundary NONE result nbr)` >>
  simp[] >>
  `MEM (edge_transfer ctx nbr lbl (df_boundary NONE result nbr))
       (MAP (\nbr'. edge_transfer ctx nbr' lbl (df_boundary NONE result nbr'))
            (cfg_preds_of cfg lbl))` by
    (simp[MEM_MAP] >> qexists_tac `nbr` >> simp[]) >>
  gvs[]
QED

Finalise fwd_joined_sound_from_pred

(* General forward analysis successor entry soundness.
   After running a block OK at fixpoint with a sound entry lattice value,
   the successor's entry lattice value is also sound.

   Pass-specific hypotheses:
   H1: transfer_sound (transfer steps preserve soundness)
   H2: valid_state_rel R_ok R_term holds
   H3: sound respects R_ok (R_ok s1 s2 /\ sound v0 s1 ==> sound v0 s2)
   H4: transfer preserves SOME (transfer ctx inst v <> NONE when v <> NONE)
   H5: join-right soundness (sound b s /\ b <> NONE ==> sound (join a b) s)
   H6: edge_transfer preserves soundness
   H7: joined_sound: one predecessor edge-transferred boundary sound + non-NONE
       implies the full df_joined_val is sound
   H8: entry lattice value at current block is non-bottom (df_at lbl 0 <> NONE)
   H9: join preserves non-bottom (b <> NONE ==> join a b <> NONE)
*)

Theorem fwd_successor_entry_sound:
  !(bottom : 'a option) join transfer edge_transfer
   (ctx : 'b) entry_val fn
   (sound : 'a option -> venom_state -> bool)
   (R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   bb (fuel : num) run_ctx s v.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    let cfg = cfg_analyze fn in
    (* Fixpoint *)
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val cfg fn.fn_blocks)
      cfg.cfg_dfs_pre result /\
    (* Function well-formedness *)
    wf_function fn /\
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (* Block and state *)
    MEM bb fn.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    MEM s.vs_current_bb cfg.cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    sound (df_at bottom result s.vs_current_bb 0) s /\
    (exec_block : num -> venom_context -> basic_block -> venom_state -> exec_result)
      fuel run_ctx bb s = OK v /\
    (* H1: transfer sound *)
    transfer_sound sound transfer ctx /\
    (* H2: sound respects R_ok *)
    valid_state_rel R_ok R_term /\
    (!v0 s1 s2. R_ok s1 s2 /\ sound v0 s1 ==> sound v0 s2) /\
    (* H3: transfer preserves SOME *)
    (!inst v0. v0 <> NONE ==> transfer ctx inst v0 <> NONE) /\
    (* H4: join right soundness *)
    (!a b s. sound b s /\ b <> NONE ==> sound (join a b) s) /\
    (* H5: edge_transfer preserves soundness *)
    (!src dst val s.
       sound val s ==> sound (edge_transfer ctx src dst val) s) /\
    (* H6: edge_transfer preserves SOME *)
    (!src dst val. val <> NONE ==> edge_transfer ctx src dst val <> NONE) /\
    (* H7: joined sound from one pred *)
    (!lbl nbr.
       MEM nbr (cfg_preds_of cfg lbl) /\
       edge_transfer ctx nbr lbl (df_boundary bottom result nbr) <> NONE /\
       sound (edge_transfer ctx nbr lbl (df_boundary bottom result nbr)) v
       ==>
       sound (df_joined_val Forward bottom join edge_transfer ctx entry_val
                cfg result lbl) v) /\
    (* H8: entry value at current block is non-bottom *)
    df_at bottom result s.vs_current_bb 0 <> NONE /\
    (* H9: join preserves non-bottom *)
    (!a b. b <> NONE ==> join a b <> NONE)
    ==>
    MEM v.vs_current_bb cfg.cfg_dfs_pre /\
    sound (df_at bottom result v.vs_current_bb 0) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecProofsTheory.exec_block_ok_nonempty] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[venomWfTheory.fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     simp[GSYM venomInstTheory.fn_labels_def]) >>
  qpat_x_assum `bb.bb_label = s.vs_current_bb`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  (* Step 1: Exit soundness via transfer_sound_exit *)
  qabbrev_tac `ti = PRE (LENGTH bb.bb_instructions)` >>
  `ti < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  imp_res_tac venomExecProofsTheory.wf_function_bb_well_formed >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[venomWfTheory.bb_well_formed_def] >>
  `is_terminator (EL ti bb.bb_instructions).inst_opcode` by (
    fs[Abbr `ti`] >> Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  `!j. j < ti ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> first_x_assum (qspec_then `bb` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspec_then `j` mp_tac) >>
    impl_tac >- fs[Abbr `ti`] >> simp[]) >>
  `SUC ti = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  `sound (df_at bottom (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn) bb.bb_label (SUC ti)) v` by
    suspend "exit_sound" >>
  `sound (df_at bottom (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn) bb.bb_label (LENGTH bb.bb_instructions)) v` by
    metis_tac[] >>
  (* Step 2: df_at entry <> NONE (from sound + H8) *)
  `df_at bottom (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn) bb.bb_label 0 <> NONE` by metis_tac[] >>
  `df_at bottom (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn) bb.bb_label (LENGTH bb.bb_instructions) <> NONE` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] fwd_df_at_exit_not_none) >>
    disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
      `ctx`, `entry_val`, `fn`, `bb.bb_label`, `bb`] mp_tac) >>
    simp[]) >>
  (* Step 3: Boundary fixpoint *)
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
      dfAnalyzeProofsTheory.df_boundary_fixpoint_proof))) >>
  strip_tac >>
  (* Step 4: Boundary soundness via join_right *)
  `sound (df_boundary bottom (df_analyze Forward bottom join transfer
     edge_transfer ctx entry_val fn) bb.bb_label) v` by
    metis_tac[] >>
  (* Step 5: Boundary <> NONE (from fixpoint + exit <> NONE) *)
  `df_boundary bottom (df_analyze Forward bottom join transfer edge_transfer
     ctx entry_val fn) bb.bb_label <> NONE` by metis_tac[] >>
  (* Step 6: Successor location *)
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecProofsTheory.exec_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgHelpersTheory.bb_succs_in_cfg_succs] >>
  conj_tac
  >- (imp_res_tac cfg_dfs_pre_succs_closed >> fs[EVERY_MEM])
  >- suspend "succ_sound"
QED

Resume fwd_successor_entry_sound[succ_sound]:
  imp_res_tac (GSYM cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond) >>
  (* Step 7: df_at = joined at successor entry *)
  `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    (imp_res_tac cfg_dfs_pre_succs_closed >> fs[EVERY_MEM]) >>
  drule_all (SIMP_RULE std_ss [LET_THM] fwd_df_at_entry_eq_joined) >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  (* Step 8: Use H7 (joined_sound_from_pred) *)
  first_x_assum irule >>
  qexists_tac `bb.bb_label` >>
  simp[]
QED

Resume fwd_successor_entry_sound[exit_sound]:
  `!idx. SUC idx <= LENGTH bb.bb_instructions ==>
     df_at bottom (df_analyze Forward bottom join transfer edge_transfer
       ctx entry_val fn) bb.bb_label (SUC idx) =
     transfer ctx (EL idx bb.bb_instructions)
       (df_at bottom (df_analyze Forward bottom join transfer edge_transfer
         ctx entry_val fn) bb.bb_label idx)` by
    (rpt strip_tac >> drule_all intra_fwd >> simp[]) >>
  irule transfer_sound_exit >> simp[] >>
  metis_tac[]
QED

Finalise fwd_successor_entry_sound

(* ===== General: df_at at entry is non-bottom when transfer always non-bottom =====
 *
 * When transfer always returns non-bottom (regardless of input), every DFS-reachable
 * block has df_at bottom result lbl 0 ≠ bottom. This eliminates H8 from
 * fwd_successor_entry_sound for the common case (MCE, assign_elim, load_elim, etc.).
 *
 * Proof outline:
 * 1. Transfer always non-bottom ⇒ df_at lbl (SUC n) ≠ bottom ⇒ exit ≠ bottom
 * 2. Fixpoint boundary = join(boundary, exit), exit ≠ bottom, join preserves ⇒ boundary ≠ bottom
 * 3. edge_transfer preserves ⇒ edge values ≠ bottom
 * 4. Entry label: join(entry_value, base) ≠ bottom directly
 * 5. Non-entry: predecessors non-empty (DFS property), edge values ≠ bottom ⇒ FOLDL ≠ bottom
 *)

(* Helper: non-entry DFS-reachable block has a reachable predecessor *)
Triviality fwd_dfs_non_entry_has_reachable_pred[local]:
  !fn lbl.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    fn_entry_label fn <> SOME lbl ==>
    ?p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) /\
        MEM p (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `fn_has_entry fn` by fs[venomWfTheory.wf_function_def] >>
  `fn.fn_blocks <> []` by fs[venomWfTheory.fn_has_entry_def] >>
  `entry_block fn = SOME (HD fn.fn_blocks)` by
    (simp[venomInstTheory.entry_block_def] >> Cases_on `fn.fn_blocks` >> gvs[]) >>
  qabbrev_tac `x = HD fn.fn_blocks` >>
  qabbrev_tac `succs = build_succs fn.fn_blocks` >>
  qabbrev_tac `entry = x.bb_label` >>
  `fn_entry_label fn = SOME entry` by
    simp[venomInstTheory.fn_entry_label_def, Abbr `entry`] >>
  `lbl <> entry` by (strip_tac >> gvs[]) >>
  (* Expand cfg_analyze to access dfs_pre and cfg_succs *)
  `(cfg_analyze fn).cfg_dfs_pre =
     SND (dfs_pre_walk succs [] entry) /\
   (cfg_analyze fn).cfg_succs = succs` by (
    simp[cfgDefsTheory.cfg_analyze_def, LET_THM, Abbr `succs`, Abbr `entry`] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  `ALL_DISTINCT (cfg_analyze fn).cfg_dfs_pre` by
    simp[cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct] >>
  `MEM lbl (SND (dfs_pre_walk succs [] entry))` by metis_tac[] >>
  `ALL_DISTINCT (SND (dfs_pre_walk succs [] entry))` by metis_tac[] >>
  (* Apply dfs_pre_walk_has_pred: get a predecessor p IN the DFS walk *)
  mp_tac (cj 1 cfgHelpersTheory.dfs_pre_walk_has_pred) >>
  disch_then (qspecl_then [`succs`, `[] : string list`, `entry`, `lbl`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `p` >>
  (* p is in cfg_dfs_pre (from INDEX_OF = SOME => MEM) *)
  `MEM p (SND (dfs_pre_walk succs [] entry))` by
    (CCONTR_TAC >> gvs[GSYM INDEX_OF_eq_NONE]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by metis_tac[] >>
  (* p is a predecessor of lbl (from edge relation) *)
  `MEM lbl (cfg_succs_of (cfg_analyze fn) p)` by
    simp[cfgDefsTheory.cfg_succs_of_def] >>
  metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
QED

(* Helper: at fixpoint with transfer always non-bottom, exit is non-bottom *)
Triviality fwd_exit_not_none_strong[local]:
  !(bottom : 'a) join transfer edge_transfer ctx entry_val fn lbl bb.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    wf_function fn /\
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    (!ctx' inst v. transfer ctx' inst v <> bottom)
    ==>
    df_at bottom result lbl (LENGTH bb.bb_instructions) <> bottom
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
    ctx entry_val fn` >>
  (* Induction: df_at lbl n <> bottom for 0 < n <= LENGTH instrs *)
  `!n. 0 < n /\ n <= LENGTH bb.bb_instructions ==>
     df_at bottom result lbl n <> bottom` suffices_by (
    strip_tac >> first_x_assum match_mp_tac >>
    Cases_on `bb.bb_instructions` >> fs[]) >>
  Induct >> simp[] >> strip_tac >>
  Cases_on `n`
  >- ((* n = 0: df_at lbl 1 = transfer ctx inst0 (df_at lbl 0) <> bottom *)
    `SUC 0 <= LENGTH bb.bb_instructions` by simp[] >>
    `df_at bottom result lbl (SUC 0) =
     transfer ctx (EL 0 bb.bb_instructions) (df_at bottom result lbl 0)` by
      (mp_tac intra_fwd >>
       disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
         `ctx`, `entry_val`, `fn`, `lbl`, `bb`, `0`] mp_tac) >>
       simp[Abbr `result`]) >>
    metis_tac[])
  >> ((* n = SUC n': df_at lbl (SUC (SUC n')) = transfer ... <> bottom *)
    rename [`SUC (SUC n')`] >>
    `SUC (SUC n') <= LENGTH bb.bb_instructions` by simp[] >>
    `df_at bottom result lbl (SUC (SUC n')) =
     transfer ctx (EL (SUC n') bb.bb_instructions)
       (df_at bottom result lbl (SUC n'))` by
      (mp_tac intra_fwd >>
       disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
         `ctx`, `entry_val`, `fn`, `lbl`, `bb`, `SUC n'`] mp_tac) >>
       simp[Abbr `result`]) >>
    metis_tac[])
QED

(* Helper: at fixpoint with exit non-bottom, boundary is non-bottom *)
Triviality fwd_boundary_not_none[local]:
  !(bottom : 'a) join transfer edge_transfer ctx entry_val fn lbl bb.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    wf_function fn /\
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    df_at bottom result lbl (LENGTH bb.bb_instructions) <> bottom /\
    (!a b. b <> bottom ==> join a b <> bottom)
    ==>
    df_boundary bottom result lbl <> bottom
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
      dfAnalyzeProofsTheory.df_boundary_fixpoint_proof))) >>
  strip_tac >> metis_tac[]
QED

(* Helper: FOLDL join preserves non-bottom accumulator *)
Triviality foldl_join_acc_non_bottom[local]:
  !join (bottom : 'a) vals acc.
    (!a b. a <> bottom \/ b <> bottom ==> join a b <> bottom) /\
    acc <> bottom ==>
    FOLDL join acc vals <> bottom
Proof
  Induct_on `vals` >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `join acc h <> bottom` by metis_tac[] >>
  simp[] >> first_x_assum match_mp_tac >> metis_tac[]
QED

(* Helper: FOLDL join bottom with at least one non-bottom element is non-bottom *)
Triviality foldl_join_non_bottom[local]:
  !join (bottom : 'a) vals v.
    (!a b. a <> bottom \/ b <> bottom ==> join a b <> bottom) /\
    MEM v vals /\ v <> bottom ==>
    FOLDL join bottom vals <> bottom
Proof
  Induct_on `vals` >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- ((* v = h: join bottom h <> bottom, then propagate *)
    `join bottom h <> bottom` by metis_tac[] >>
    mp_tac foldl_join_acc_non_bottom >>
    disch_then (qspecl_then [`join`, `bottom`, `vals`, `join bottom h`] mp_tac) >>
    simp[] >> metis_tac[])
  >> (* v in tail: need FOLDL join (join bottom h) vals <> bottom *)
  Cases_on `join bottom h = bottom`
  >- ((* acc stays bottom, use IH *)
    first_x_assum (qspecl_then [`join`, `bottom`, `v`] mp_tac) >>
    simp[] >> metis_tac[])
  >> (* acc non-bottom, propagate *)
  mp_tac foldl_join_acc_non_bottom >>
  disch_then (qspecl_then [`join`, `bottom`, `vals`, `join bottom h`] mp_tac) >>
  simp[]
QED

(* Main theorem: df_at at entry (index 0) is non-bottom for all DFS-reachable
   blocks, when transfer always returns non-bottom. *)
Theorem fwd_df_at_entry_not_none:
  !(bottom : 'a) join transfer edge_transfer ctx entry_val fn lbl.
    let result = df_analyze Forward bottom join transfer edge_transfer
                            ctx entry_val fn in
    is_fixpoint
      (df_process_block Forward bottom join transfer edge_transfer
                        ctx entry_val (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    (* transfer always returns non-bottom *)
    (!ctx' inst v. transfer ctx' inst v <> bottom) /\
    (* join preserves non-bottom from either side *)
    (!a b. a <> bottom \/ b <> bottom ==> join a b <> bottom) /\
    (* edge_transfer preserves non-bottom *)
    (!ctx' src dst v. v <> bottom ==> edge_transfer ctx' src dst v <> bottom) /\
    (* entry_val covers the entry label with a non-bottom value *)
    (?ev_lbl ev. entry_val = SOME (ev_lbl, ev) /\
       fn_entry_label fn = SOME ev_lbl /\
       ev <> bottom)
    ==>
    df_at bottom result lbl 0 <> bottom
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
    ctx entry_val fn` >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  (* Step 1: rewrite df_at 0 to df_joined_val *)
  `df_at bottom result lbl 0 =
   df_joined_val Forward bottom join edge_transfer ctx entry_val cfg result lbl` by (
    mp_tac (SIMP_RULE std_ss [LET_THM] fwd_df_at_entry_eq_joined) >>
    disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
      `ctx`, `entry_val`, `fn`, `lbl`] mp_tac) >>
    simp[Abbr `result`, Abbr `cfg`]) >>
  simp[] >>
  (* Step 2: Get block info from wf_function + DFS membership *)
  `!lbl'. MEM lbl' cfg.cfg_dfs_pre ==>
    ?bb. lookup_block lbl' fn.fn_blocks = SOME bb /\
         bb.bb_instructions <> []` by (
    rpt strip_tac >>
    `cfg_reachable_of cfg lbl'` by (
      `set cfg.cfg_dfs_pre = {l | cfg_reachable_of cfg l}` by (
        mp_tac (SIMP_RULE std_ss [Abbr `cfg`]
          (Q.SPEC `fn` cfgAnalysisPropsTheory.cfg_analyze_reachable_sets)) >>
        impl_tac >- first_assum ACCEPT_TAC >> simp[EXTENSION] >> metis_tac[]) >>
      gvs[EXTENSION, IN_DEF]) >>
    `MEM lbl' (fn_labels fn)` by
      metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels,
                Abbr `cfg`] >>
    gvs[venomInstTheory.fn_labels_def, MEM_MAP] >>
    rename [`MEM bb fn.fn_blocks`] >>
    qexists_tac `bb` >>
    `bb_well_formed bb` by
      (gvs[venomWfTheory.wf_function_def] >> metis_tac[]) >>
    gvs[venomWfTheory.bb_well_formed_def] >>
    irule venomExecProofsTheory.MEM_lookup_block >>
    gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  (* Step 3: Every DFS block has non-bottom boundary *)
  `!lbl'. MEM lbl' cfg.cfg_dfs_pre ==>
    df_boundary bottom result lbl' <> bottom` by (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `!lbl'. MEM lbl' cfg.cfg_dfs_pre ==> ?bb. _`
      (qspec_then `lbl'` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    (* exit <> bottom via fwd_exit_not_none_strong *)
    sg `df_at bottom result lbl' (LENGTH bb.bb_instructions) <> bottom`
    >- (mp_tac (SIMP_RULE std_ss [LET_THM] fwd_exit_not_none_strong) >>
        disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
          `ctx`, `entry_val`, `fn`, `lbl'`, `bb`] mp_tac) >>
        simp[Abbr `result`, Abbr `cfg`]) >>
    (* boundary <> bottom via fwd_boundary_not_none *)
    mp_tac (SIMP_RULE std_ss [LET_THM] fwd_boundary_not_none) >>
    disch_then (qspecl_then [`bottom`, `join`, `transfer`, `edge_transfer`,
      `ctx`, `entry_val`, `fn`, `lbl'`, `bb`] mp_tac) >>
    simp[Abbr `result`, Abbr `cfg`]) >>
  (* Step 4: Expand df_joined_val and case split entry vs non-entry *)
  simp[df_joined_val_def, LET_THM] >>
  sg `entry_val = SOME (ev_lbl, ev)` >- simp[] >> simp[] >>
  Cases_on `lbl = ev_lbl`
  >- ((* Entry label: join ev base <> bottom, ev <> bottom gives left side *)
    sg `!b. join ev b <> bottom` >- metis_tac[] >>
    simp[])
  >> (* Non-entry: FOLDL join bottom edge_vals <> bottom *)
  (* First establish a reachable predecessor with non-bottom edge value *)
  sg `?p. MEM p (cfg_preds_of cfg lbl) /\ MEM p cfg.cfg_dfs_pre`
  >- (simp[Abbr `cfg`] >>
      mp_tac fwd_dfs_non_entry_has_reachable_pred >>
      disch_then (qspecl_then [`fn`, `lbl`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  (* The edge value for this predecessor is non-bottom *)
  sg `edge_transfer ctx p lbl (df_boundary bottom result p) <> bottom`
  >- (first_x_assum match_mp_tac >> metis_tac[]) >>
  (* This edge value is a member of the FOLDL list *)
  sg `MEM (edge_transfer ctx p lbl (df_boundary bottom result p))
       (MAP (\nbr. edge_transfer ctx nbr lbl
         (df_boundary bottom result nbr)) (cfg_preds_of cfg lbl))`
  >- (simp[MEM_MAP] >> qexists_tac `p` >> simp[]) >>
  (* Apply foldl_join_non_bottom *)
  mp_tac foldl_join_non_bottom >>
  disch_then (qspecl_then [`join`, `bottom`,
    `MAP (\nbr. edge_transfer ctx nbr lbl
      (df_boundary bottom result nbr)) (cfg_preds_of cfg lbl)`,
    `edge_transfer ctx p lbl (df_boundary bottom result p)`] mp_tac) >>
  simp[] >>
  (* Resolve the case expression: MAP is non-empty since p is in preds *)
  sg `cfg_preds_of cfg lbl <> []`
  >- (strip_tac >> gvs[MEM]) >>
  Cases_on `cfg_preds_of cfg lbl` >> gvs[]
QED
