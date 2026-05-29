(*
 * Analysis-Driven Simulation — Proofs (Part 3: Widen Correctness)
 *
 * Main theorems:
 *   df_analysis_pass_correct_widen_sound_proof
 *   df_analysis_pass_correct_widen_block_sim_proof
 *   df_analysis_pass_correct_block_sim_proof
 *   df_analysis_pass_correct_widen_sound_inv_proof
 *   df_analysis_pass_correct_widen_sound_inv2_proof
 *)

Theory analysisSimProofsWiden
Ancestors
  analysisSimProofsSound analysisSimProofs analysisSimProofsBase analysisSimProofsCompare
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState venomWf cfgAnalysisProps execEquivProofs
  list finite_map pred_set string

(* Forward-specialized widen dataflow theorems *)
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
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* eval_phis preserves entry-point soundness *)
      (!bb s s_phi.
         MEM bb fn.fn_blocks /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_widen_at bottom result bb.bb_label 0) s ==>
         sound (df_widen_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
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
       (?e. run_blocks fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks fuel run_ctx fn s1)
         (run_blocks fuel run_ctx (function_map_transform bt fn) s2)`
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
  >- (simp[run_blocks_def, lift_result_def])
  >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
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
  (* Normalize sound assumption: s1.vs_current_bb → s2.vs_current_bb
     (can't use gvs[] in widen context — times out with Abbrev) *)
  qpat_x_assum `sound (df_at bottom result s1.vs_current_bb 0) s1`
    (fn th =>
      qpat_assum `s1.vs_current_bb = s2.vs_current_bb`
        (fn eq => assume_tac (REWRITE_RULE [eq] th))) >>
  sg `sound (df_at bottom result bb.bb_label 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
        (fn th => irule th) >>
      qexists_tac `s1` >> simp[]) >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    irule run_block_preserves_R_helper >> metis_tac[]) >>
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
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by (
    fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
    rpt strip_tac >> res_tac) >>
  `!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
    !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2` by (
    rpt strip_tac >>
    imp_res_tac execEquivParamProofsTheory.operand_agreement_flat >>
    simp[]) >>
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    DISJ_CASES_TAC (ISPECL [``s2:venom_state``, ``bb.bb_instructions``]
      eval_phis_ok_or_error_defs)
    >- (* eval_phis OK case -- use analysis_run_block_sim *)
       (first_x_assum strip_assume_tac >>
        rename1 `eval_phis s2 bb.bb_instructions = OK s_phi` >>
        `sound (df_at bottom result bb.bb_label
             (phi_prefix_length bb.bb_instructions))
          (s_phi with vs_inst_idx := 0)` by (
          first_x_assum (qspecl_then [`bb`, `s2`, `s_phi`] mp_tac) >>
          simp[Abbr `result`]) >>
        mp_tac analysis_run_block_sim >>
        disch_then (qspecl_then [`R_ok`, `R_term`, `sound`, `f`, `bb`,
          `bottom`, `result`, `transfer`, `ctx`] mp_tac) >>
        impl_tac >- (
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          rpt strip_tac >> fs[transfer_sound_def] >> res_tac) >>
        disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`, `s_phi`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        fs[Abbr `bt`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        gvs[run_block_def])) >>
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
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
         lift_result R_ok R_term R_term (run_block fuel run_ctx bb s)
           (run_block fuel run_ctx
             (analysis_block_transform bottom
               (widen_to_df (df_analyze_widen Forward bottom join widen
                 threshold transfer edge_transfer ctx entry_val fn)) f bb)
             s)) /\
      wf_function fn /\
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
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
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
       (?e. run_blocks fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks fuel run_ctx fn s1)
         (run_blocks fuel run_ctx (function_map_transform bt fn) s2)`
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
  >- (simp[run_blocks_def, lift_result_def])
  >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
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
  (* Normalize sound assumption: s1.vs_current_bb → s2.vs_current_bb
     (can't use gvs[] in widen context — times out with Abbrev) *)
  qpat_x_assum `sound (df_at bottom result s1.vs_current_bb 0) s1`
    (fn th =>
      qpat_assum `s1.vs_current_bb = s2.vs_current_bb`
        (fn eq => assume_tac (REWRITE_RULE [eq] th))) >>
  sg `sound (df_at bottom result bb.bb_label 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  sg `state_inv s2`
  >- metis_tac[] >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    irule run_block_preserves_R_helper >> metis_tac[]) >>
  (* Block sim - from hypothesis *)
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    qpat_x_assum `!bb fuel run_ctx s. MEM bb fn.fn_blocks /\ _ ==> _`
      (qspecl_then [`bb`, `fuel`, `run_ctx`, `s2`] mp_tac) >>
    simp_tac std_ss [Abbr `bt`, Abbr `result`, Abbr `wresult`, Abbr `cfg`] >>
    impl_tac >- gvs[] >> simp[]) >>
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
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

(* Non-widen block-level simulation: like widen_block_sim but for df_analyze.
   Takes block-level sim + cross-block hypotheses, NO per-inst transfer/state_inv. *)
Theorem df_analysis_pass_correct_block_sim_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join
   transfer edge_transfer ctx entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list).
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let process = df_process_block Forward bottom join
                    transfer edge_transfer ctx entry_val cfg bbs in
    let result = df_analyze Forward bottom join
                   transfer edge_transfer ctx entry_val fn in
      valid_state_rel R_ok R_term /\
      (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
      (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
      is_fixpoint process cfg.cfg_dfs_pre result /\
      (* Successor soundness — block-level *)
      (!bb fuel run_ctx s v.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s /\
         run_block fuel run_ctx bb s = OK v ==>
         MEM v.vs_current_bb cfg.cfg_dfs_pre /\
         sound (df_at bottom result v.vs_current_bb 0) v /\
         state_inv v) /\
      (* Block simulation — abstract *)
      (!bb fuel run_ctx s.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
         lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
         s.vs_inst_idx = 0 /\ s.vs_current_bb = bb.bb_label /\
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s ==>
         (?e. run_block fuel run_ctx bb s = Error e) \/
         lift_result R_ok R_term R_term (run_block fuel run_ctx bb s)
           (run_block fuel run_ctx
             (analysis_block_transform bottom result f bb) s)) /\
      wf_function fn /\
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
        sound (df_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `result = df_analyze Forward bottom join
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, analysisSimProofsBaseTheory.abt_label] >>
  qsuff_tac
    `!fuel run_ctx s1 s2.
       R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
       MEM s1.vs_current_bb cfg.cfg_dfs_pre /\
       sound (df_at bottom result s1.vs_current_bb 0) s1 /\
       state_inv s1 ==>
       (?e. run_blocks fuel run_ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks fuel run_ctx fn s1)
         (run_blocks fuel run_ctx (function_map_transform bt fn) s2)`
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
  >- (simp[run_blocks_def, lift_result_def])
  >>
  rpt gen_tac >> strip_tac >>
  `s2.vs_inst_idx = 0 /\ s1.vs_current_bb = s2.vs_current_bb /\
   (s1.vs_halted <=> s2.vs_halted)` by
    metis_tac[vsr_R_ok_fields] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  simp[function_map_transform_def, lookup_block_map_proof,
       analysisSimProofsBaseTheory.abt_label] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb.bb_label = s2.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  sg `state_inv s2`
  >- metis_tac[] >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    irule run_block_preserves_R_helper >> metis_tac[]) >>
  (* Block sim — from hypothesis *)
  `(?e. run_block fuel run_ctx bb s2 = Error e) \/
   lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
     (run_block fuel run_ctx (bt bb) s2)` by (
    qpat_x_assum `!bb fuel run_ctx s. MEM bb fn.fn_blocks /\ _ ==> _`
      (qspecl_then [`bb`, `fuel`, `run_ctx`, `s2`] mp_tac) >>
    simp_tac std_ss [Abbr `bt`, Abbr `result`, Abbr `cfg`] >>
    impl_tac >- gvs[] >> simp[]) >>
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel run_ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel run_ctx bb s1` >>
  Cases_on `run_block fuel run_ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    rename1 `R_ok v1 v2` >>
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
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
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* eval_phis preserves entry-point soundness *)
      (!bb s s_phi.
         MEM bb fn.fn_blocks /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s ==>
         sound (df_widen_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `wresult = df_analyze_widen Forward bottom join widen threshold
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `result = widen_to_df wresult` >>
  (* Reduce to df_analysis_pass_correct_widen_block_sim_proof
     by instantiating its block_sim with analysis_run_block_sim *)
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
    (* Block simulation - instantiate analysis_run_block_sim *)
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
    `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
    `EVERY inst_wf bb.bb_instructions` by (
      fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
      rpt strip_tac >> res_tac) >>
    (* eval_phis case split *)
    DISJ_CASES_TAC (ISPECL [``s:venom_state``, ``bb.bb_instructions``]
      eval_phis_ok_or_error_defs)
    >- (* eval_phis OK case -- use analysis_run_block_sim *)
       (first_x_assum strip_assume_tac >>
        rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
        `sound (df_at bottom result bb.bb_label
             (phi_prefix_length bb.bb_instructions))
          (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0)` by (
          first_x_assum (qspecl_then [`bb`, `s`, `s_phi`] mp_tac) >>
          simp[Abbr `result`, Abbr `wresult`]) >>
        mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
          `result`, `transfer`, `ctx`]
          analysisSimProofsBaseTheory.analysis_run_block_sim) >>
        impl_tac >- (
          rpt conj_tac >>
          TRY (first_assum ACCEPT_TAC) >>
          fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
          rpt strip_tac >> res_tac) >>
        disch_then (qspecl_then [`fuel`, `run_ctx`, `s`, `s_phi`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        simp[Abbr `result`, Abbr `wresult`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        gvs[run_block_def])) >>
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
         lift_result R_ok R_term R_term (step_inst fuel ctx' inst s)
           (run_insts fuel ctx' (f v inst) s)) /\
      inst_transform_structural f /\
      wf_function fn /\
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
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* eval_phis preserves entry-point soundness and state_inv *)
      (!bb s s_phi.
         MEM bb fn.fn_blocks /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_widen_at bottom result bb.bb_label 0) s /\
         state_inv s ==>
         sound (df_widen_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s /\
        sound (df_widen_at bottom result s.vs_current_bb 0) s ==>
        (?e. run_blocks fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx' fn s)
          (run_blocks fuel ctx'
            (analysis_function_transform_widen bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM, aft_widen_eq_aft, df_widen_at_eq_df_at] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `wresult = df_analyze_widen Forward bottom join widen threshold
    transfer edge_transfer ctx entry_val fn` >>
  qabbrev_tac `result = widen_to_df wresult` >>
  (* Reduce to block_sim via analysis_run_block_sim_inv *)
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
    (* Block simulation - instantiate analysis_run_block_sim_inv *)
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
    `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
    `EVERY inst_wf bb.bb_instructions` by (
      fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
      rpt strip_tac >> res_tac) >>
    (* eval_phis case split *)
    DISJ_CASES_TAC (ISPECL [``s:venom_state``, ``bb.bb_instructions``]
      eval_phis_ok_or_error_defs)
    >- (* eval_phis OK case -- use analysis_run_block_sim_inv *)
       (first_x_assum strip_assume_tac >>
        rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
        `sound (df_at bottom result bb.bb_label
             (phi_prefix_length bb.bb_instructions))
          (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0)` by (
          first_x_assum (qspecl_then [`bb`, `s`, `s_phi`] mp_tac) >>
          simp[Abbr `result`, Abbr `wresult`]) >>
        mp_tac (Q.SPECL [`R_ok`, `R_term`, `sound`, `state_inv`, `f`, `bb`,
          `bottom`, `result`, `transfer`, `ctx`]
          analysisSimProofsBaseTheory.analysis_run_block_sim_inv) >>
        impl_tac >- (
          rpt conj_tac >>
          TRY (first_assum ACCEPT_TAC) >>
          TRY (fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
               rpt strip_tac >> res_tac >> NO_TAC)) >>
        disch_then (qspecl_then [`fuel`, `run_ctx`, `s`, `s_phi`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        simp[Abbr `result`, Abbr `wresult`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        gvs[run_block_def])) >>
  simp[Abbr `result`, Abbr `wresult`]
QED

(* ===== Prepend correctness ===== *)
