(*
 * Analysis-Driven Simulation — Proofs (Part 2: Sound Correctness)
 *
 * Main theorems:
 *   df_analysis_pass_correct_sound_proof
 *   df_analysis_pass_correct_sound_inv2_proof
 *   df_analysis_pass_correct_sound_inv3_proof
 *)

Theory analysisSimProofsSound
Ancestors
  analysisSimProofs analysisSimProofsBase analysisSimProofsCompare
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState venomWf cfgAnalysisProps execEquivProofs
  list finite_map pred_set string

(* Forward-specialized dataflow theorems for sound proofs *)
val fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_proof));
val inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_inter_transfer_proof));
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));

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
      wf_function fn /\
      fn_inst_wf fn /\
      (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
      (!bb inst x.
         MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
         MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      (* eval_phis preserves entry-point soundness: PHI outputs are
         over-approximated by the joined analysis value at index 0 *)
      (!bb s s_phi.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_at bottom result bb.bb_label 0) s ==>
         sound (df_at bottom result bb.bb_label
                   (phi_prefix_length bb.bb_instructions))
               (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb ==>
        (?e. run_blocks fuel ctx fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
          (run_blocks fuel ctx (analysis_function_transform bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
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
  (* Main fuel induction *)
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
  gvs[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  `bb.bb_label = s2.vs_current_bb` by (
    fs[lookup_block_def, FIND_def] >> Cases_on `z` >> gvs[] >>
    imp_res_tac
      (prove(``!n P (l:'a list) i x. INDEX_FIND n P l = SOME (i,x) ==> P x``,
        Induct_on `l` >> rw[INDEX_FIND_def] >>
        gvs[AllCaseEqs()] >> metis_tac[])) >> gvs[]) >>
  (* sound at s2 via R_ok preservation *)
  sg `sound (df_at bottom result bb.bb_label 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  (* Per-block R_ok preservation: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    irule run_block_preserves_R_helper >> metis_tac[]) >>
  (* Derive block-level well-formedness and inst_wf *)
  `bb_well_formed bb` by metis_tac[venomWfTheory.wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by (
    fs[EVERY_MEM, venomWfTheory.fn_inst_wf_def] >>
    rpt strip_tac >> res_tac) >>
  (* Per-block operand agreement *)
  `!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
    !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2` by (
    rpt strip_tac >>
    imp_res_tac execEquivParamProofsTheory.operand_agreement_flat >>
    simp[]) >>
  (* Transfer chain *)
  `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
      df_at bottom result bb.bb_label (SUC idx) =
      transfer ctx (EL idx bb.bb_instructions)
        (df_at bottom result bb.bb_label idx))` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`bottom`, `join`, `transfer`, `edge_transfer`, `ctx`,
       `entry_val`, `fn`, `bb.bb_label`, `bb`, `idx`] intra_fwd) >>
     impl_tac >- gvs[Abbr `result`, Abbr `cfg`] >>
     simp[Abbr `result`]) >>
  (* Per-block sim: run_block bb s2 ~ run_block (bt bb) s2 via two-step bridge *)
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
        impl_tac >- (
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        fs[Abbr `bt`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        gvs[run_block_def])) >>
  (* Case: run_block bb s2 errors *)
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  (* Compose: s1 ~ s2 ~ bt via transitivity *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
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
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1` by metis_tac[] >>
    REWRITE_TAC [GSYM function_map_transform_def] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  (* Non-OK cases: Halt, Abort, IntRet *)
  >> (
    Cases_on `run_block fuel run_ctx bb s2` >> gvs[lift_result_def] >>
    Cases_on `run_block fuel run_ctx (bt bb) s2` >> gvs[lift_result_def])
QED

(* ===== Non-widen variant with state_inv + transfer_sound_wf ===== *)

(* Like df_analysis_pass_correct_sound_proof but:
   - Uses transfer_sound_wf (inst_wf available)
   - Threads state_inv alongside soundness
   - Per-inst sim gets both sound and state_inv
   Useful when soundness depends on a property (e.g. dfg_assigns_sound)
   that's preserved by well-formed step_inst but not by arbitrary ones. *)
Theorem df_analysis_pass_correct_sound_inv2_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
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
      transfer_sound_wf sound transfer ctx /\
      (* Entry soundness *)
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (* Successor soundness + state_inv preservation *)
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
      (* Per-inst sim with sound AND state_inv *)
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
      (* state_inv preserved by well-formed step_inst *)
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
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s ==>
         sound (df_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s ==>
        (?e. run_blocks fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx' fn s)
          (run_blocks fuel ctx' (analysis_function_transform bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
    ctx entry_val fn` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, analysisSimProofsBaseTheory.abt_label] >>
  (* Strengthen: add R_ok, sound, state_inv, MEM as induction invariant *)
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
        >- metis_tac[]
        >- first_assum ACCEPT_TAC)
    >> simp[analysis_function_transform_def])
  >>
  (* Main fuel induction *)
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
  (* sound at s2 via R_ok preservation *)
  sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  (* state_inv at s2 via R_ok preservation *)
  sg `state_inv s2`
  >- metis_tac[] >>
  (* Per-block R_ok preservation: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    irule run_block_preserves_R_helper >> metis_tac[]) >>
  (* Per-block sim using analysis_run_block_sim_inv *)
  `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
      df_at bottom result bb.bb_label (SUC idx) =
      transfer ctx (EL idx bb.bb_instructions)
        (df_at bottom result bb.bb_label idx))` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`bottom`, `join`, `transfer`, `edge_transfer`, `ctx`,
       `entry_val`, `fn`, `bb.bb_label`, `bb`, `idx`] intra_fwd) >>
     impl_tac >- gvs[Abbr `result`, Abbr `cfg`] >>
     simp[Abbr `result`]) >>
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
    >- (* eval_phis OK case -- use analysis_run_block_sim_inv *)
       (first_x_assum strip_assume_tac >>
        rename1 `eval_phis s2 bb.bb_instructions = OK s_phi` >>
        `sound (df_at bottom result bb.bb_label
             (phi_prefix_length bb.bb_instructions))
          (s_phi with vs_inst_idx := 0) /\
          state_inv (s_phi with vs_inst_idx := 0)` by metis_tac[] >>
        mp_tac analysis_run_block_sim_inv >>
        disch_then (qspecl_then [`R_ok`, `R_term`, `sound`, `state_inv`, `f`,
          `bb`, `bottom`, `result`, `transfer`, `ctx`] mp_tac) >>
        impl_tac >- (
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          rpt strip_tac >> fs[transfer_sound_wf_def] >> res_tac) >>
        disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`, `s_phi`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        fs[Abbr `bt`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        gvs[run_block_def])) >>
  (* Case: run_block bb s2 errors *)
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  (* Compose: s1 ~ s2 ~ bt via transitivity *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
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
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1 /\
     state_inv v1` by metis_tac[] >>
    REWRITE_TAC [GSYM function_map_transform_def] >>
    first_x_assum irule >> simp[] >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  (* Non-OK cases: Halt, Abort, IntRet *)
  >> (
    Cases_on `run_block fuel run_ctx bb s2` >> gvs[lift_result_def] >>
    Cases_on `run_block fuel run_ctx (bt bb) s2` >> gvs[lift_result_def])
QED


(* Variant of inv2 with block-restricted transfer soundness.
   transfer_sound_block only requires transfer to preserve soundness for
   instructions from the function's blocks, not for arbitrary instructions.
   Essential for passes where soundness depends on SSA/DFG properties
   (e.g. load_elim, where lattice entries reference variables). *)
Theorem df_analysis_pass_correct_sound_inv3_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (bottom : 'a) join transfer edge_transfer ctx
   entry_val fn
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
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
      transfer_sound_block_inv sound state_inv transfer ctx fn /\
      (* Entry soundness *)
      (!s lbl. fn_entry_label fn = SOME lbl ==>
         sound (df_at bottom result lbl 0) s) /\
      (* Successor soundness + state_inv preservation *)
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
      (* Per-inst sim with sound AND state_inv *)
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
      (* state_inv preserved by well-formed step_inst *)
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
         MEM bb.bb_label cfg.cfg_dfs_pre /\
         eval_phis s bb.bb_instructions = OK s_phi /\
         sound (df_at bottom result bb.bb_label 0) s /\
         state_inv s ==>
         sound (df_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0) /\
         state_inv (s_phi with vs_inst_idx := 0))
    ==>
      !fuel ctx' s.
        s.vs_inst_idx = 0 /\
        fn_entry_label fn = SOME s.vs_current_bb /\
        state_inv s ==>
        (?e. run_blocks fuel ctx' fn s = Error e) \/
        lift_result R_ok R_term R_term (run_blocks fuel ctx' fn s)
          (run_blocks fuel ctx' (analysis_function_transform bottom result f fn) s)
Proof
  simp_tac std_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `cfg = cfg_analyze fn` >>
  qabbrev_tac `result = df_analyze Forward bottom join transfer edge_transfer
    ctx entry_val fn` >>
  qabbrev_tac `bt = analysis_block_transform bottom result f` >>
  `!b. (bt b).bb_label = b.bb_label` by
    simp[Abbr `bt`, analysisSimProofsBaseTheory.abt_label] >>
  (* Strengthen: add R_ok, sound, state_inv, MEM as induction invariant *)
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
        >- metis_tac[]
        >- first_assum ACCEPT_TAC)
    >> simp[analysis_function_transform_def])
  >>
  (* Main fuel induction *)
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
  (* sound at s2 via R_ok preservation *)
  sg `sound (df_at bottom result s1.vs_current_bb 0) s2`
  >- (qpat_x_assum `!v a b. R_ok a b /\ sound v a ==> sound v b`
      (fn th => irule th) >>
    qexists_tac `s1` >> simp[]) >>
  (* state_inv at s2 via R_ok preservation *)
  sg `state_inv s2`
  >- metis_tac[] >>
  (* Per-block R_ok preservation: run_block bb s1 ~ run_block bb s2 *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx bb s2)` by (
    irule run_block_preserves_R_helper >> metis_tac[]) >>
  (* Per-block sim using analysis_run_block_sim_inv_block *)
  `(!idx. SUC idx <= LENGTH bb.bb_instructions ==>
      df_at bottom result bb.bb_label (SUC idx) =
      transfer ctx (EL idx bb.bb_instructions)
        (df_at bottom result bb.bb_label idx))` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`bottom`, `join`, `transfer`, `edge_transfer`, `ctx`,
       `entry_val`, `fn`, `bb.bb_label`, `bb`, `idx`] intra_fwd) >>
     impl_tac >- gvs[Abbr `result`, Abbr `cfg`] >>
     simp[Abbr `result`]) >>
  (* Bridge: sound at bb.bb_label via equality chain:
       s1.vs_current_bb = s2.vs_current_bb, bb.bb_label = s2.vs_current_bb *)
  sg `sound (df_at bottom result bb.bb_label 0) s2`
  >- (qpat_assum `sound (df_at bottom result s1.vs_current_bb 0) s2`
        (fn th_sound =>
          qpat_assum `bb.bb_label = s2.vs_current_bb`
            (fn th_lbl =>
              qpat_assum `s1.vs_current_bb = s2.vs_current_bb`
                (fn th_eq =>
                  ACCEPT_TAC (REWRITE_RULE [SYM th_lbl]
                    (REWRITE_RULE [th_eq] th_sound)))))) >>
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
    >- (* eval_phis OK case -- use analysis_run_block_sim_inv_block *)
       (first_x_assum strip_assume_tac >>
        rename1 `eval_phis s2 bb.bb_instructions = OK s_phi` >>
        `sound (df_at bottom result bb.bb_label
             (phi_prefix_length bb.bb_instructions))
          (s_phi with vs_inst_idx := 0) /\
          state_inv (s_phi with vs_inst_idx := 0)` by
          (qpat_x_assum
             `!bb s s_phi. MEM bb fn.fn_blocks /\ MEM bb.bb_label cfg.cfg_dfs_pre /\
               eval_phis s bb.bb_instructions = OK s_phi /\
               sound (df_at bottom result bb.bb_label 0) s /\ state_inv s ==>
               sound (df_at bottom result bb.bb_label (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0) /\
               state_inv (s_phi with vs_inst_idx := 0)`
             (fn th => mp_tac (SPECL
               [``bb:basic_block``, ``s2:venom_state``,
                 ``s_phi:venom_state``] th)) >>
           impl_tac >- (
             rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
             metis_tac[]) >>
           simp[]) >>
        mp_tac analysis_run_block_sim_inv_block >>
        disch_then (qspecl_then [`R_ok`, `R_term`, `sound`, `state_inv`, `f`,
          `bb`, `fn`, `bottom`, `result`, `transfer`, `ctx`] mp_tac) >>
        impl_tac >- (
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          rpt strip_tac >> fs[transfer_sound_block_inv_def] >> res_tac) >>
        disch_then (qspecl_then [`fuel`, `run_ctx`, `s2`, `s_phi`] mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
        fs[Abbr `bt`])
    >- (* eval_phis Error case *)
       (disj1_tac >>
        first_x_assum (X_CHOOSE_THEN ``e:string`` STRIP_ASSUME_TAC) >>
        qexists_tac `e` >>
        gvs[run_block_def])) >>
  (* Case: run_block bb s2 errors *)
  Cases_on `?e. run_block fuel run_ctx bb s2 = Error e`
  >- (fs[] >> imp_res_tac lift_result_error_left >> gvs[])
  >>
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s2)
                            (run_block fuel run_ctx (bt bb) s2)` by metis_tac[] >>
  (* Compose: s1 ~ s2 ~ bt via transitivity *)
  `lift_result R_ok R_term R_term (run_block fuel run_ctx bb s1)
                            (run_block fuel run_ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
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
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[vsr_R_ok_fields] >>
    simp[lift_result_def] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
    `v1.vs_current_bb = v2.vs_current_bb` by metis_tac[vsr_R_ok_fields] >>
    `MEM v1.vs_current_bb cfg.cfg_dfs_pre /\
     sound (df_at bottom result v1.vs_current_bb 0) v1 /\
     state_inv v1` by metis_tac[] >>
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
