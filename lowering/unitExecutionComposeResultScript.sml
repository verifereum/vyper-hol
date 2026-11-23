(* Preserve a call-result property derived from the body's unread-tail equation. *)
Theory unitExecutionComposeResult
Ancestors
  unitExecutionCompose gasOutcomeFull sourceExemptMods vyperStorageFootprint

Theorem unit_execution_compose_result_horizon_mods:
  !(P : 'call_res -> bool) DF E ctx func cx st0 mods
    (source : evaluation_state -> ('body_res + exception) # evaluation_state)
    es0 s0 G0 tn0 Q R vs0 CT REL
    (EX : ('call_res # 'call_accounts # 'call_requests) -> bool) marks0.
    storage_trace_frame source /\
    storage_trace_domain cx st0 es0.storage_trace /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
       gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
         (vs0, FEMPTY, entry_taint) marks0 (OK s0, G0, tn0) /\
       ((!fuel. ptr_safe_run (DF H) 0 fuel ctx func [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY entry_taint
                 vs0)) /\
    gas_outcome_full_mods (DF, 0, E, ctx, func, []) mods cx st0 source
      (es0, s0, G0, tn0) Q R /\
    (!gobs res ee. source (es0 with gas_obs := gobs) = (res, ee) ==>
       (storage_trace_domain cx st0 (SND (SND (SND (CT gobs)))) <=>
        storage_trace_domain cx st0 ee.storage_trace) /\
       (!H. valid_horizon cx st0 H (SND (SND (SND (CT gobs)))) <=>
            valid_horizon cx st0 H ee.storage_trace)) /\
    (!gx res ee.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) ==>
       !tail. CT (gx ++ tail) = CT gx) /\
    (!gx err ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (INR (Error err), ee with gas_obs := tail)) /\
       unspecified_behaviour_exempt_mods mods err /\
       CT gx = (cr, am', rqs, obs) ==>
       EX (cr, am', rqs)) /\
    (!gx res ee t.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       (?H G tn. valid_horizon cx st0 H ee.storage_trace /\
                 Q H res (ee with gas_obs := []) G tn t) ==>
       ?r. exit_result r /\
         !H G tn. valid_horizon cx st0 H ee.storage_trace /\
                  Q H res (ee with gas_obs := []) G tn t ==>
           ?G' tn'.
             gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
               (t, G, tn) [] (r, G', tn') /\
             !cr am' rqs obs. CT gx = (cr, am', rqs, obs) ==>
               REL H (cr, am', rqs) r) /\
    (!gx res ee H gt r cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       valid_horizon cx st0 H ee.storage_trace /\
       exit_result r /\ R H res (ee with gas_obs := []) gt r /\
       CT gx = (cr, am', rqs, obs) ==>
       REL H (cr, am', rqs) r) /\
    (!gx res ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       CT gx = (cr, am', rqs, obs) ==> P cr) ==>
    ?marks.
      ((!tail. ~storage_trace_domain cx st0
                 (SND (SND (SND
                   (CT (gas_explicit marks s0.vs_gas_readings ++ tail)))))) /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
           (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
           (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      ?res am' rqs obs.
        (!tail. CT (gas_explicit marks s0.vs_gas_readings ++ tail) =
                (res, am', rqs, obs)) /\
        P res /\
        ((EX (res, am', rqs) /\
          ?H leaf leaf_pg leaf_g leaf_tn finish.
            gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
              (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
              (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
         (?r. exit_result r /\ storage_trace_domain cx st0 obs /\
            gas_origin_path T E ctx func vs0 (marks0 ++ marks) r /\
            !H. valid_horizon cx st0 H obs ==>
              REL H (res, am', rqs) r /\
              !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY
                       entry_taint vs0))
Proof
  rpt gen_tac >> strip_tac >>
  drule_at_then (Pat `gas_outcome_full_mods _ _ _ _ _ _ _ _`)
    (Q.ISPECL_THEN
      [`vs0`, `CT`, `\H c r. REL H c r /\ P (FST c)`,
       `\c. EX c /\ P (FST c)`, `marks0`] mp_tac)
    unit_execution_compose_horizon_mods >>
  simp[] >> impl_tac
  >- (conj_tac >- (rpt strip_tac >> metis_tac[]) >>
      conj_tac >- (rpt strip_tac >> metis_tac[]) >>
      reverse conj_tac >- (rpt strip_tac >> metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!gx res ee t. _ ==> ?r. _`
        (qspecl_then [`gx`, `res`, `ee`, `t`] mp_tac) >>
      impl_tac >- metis_tac[] >>
      strip_tac >> qexists_tac `r` >> simp[] >>
      map_every qx_gen_tac [`h`, `g`, `tn_in`] >> strip_tac >>
      qpat_x_assum `!H G tn. _ ==> ?G' tn'. _`
        (qspecl_then [`h`, `g`, `tn_in`] mp_tac) >>
      simp[] >>
      disch_then (qx_choose_then `g_out` (qx_choose_then `tn_out` strip_assume_tac)) >>
      qexistsl_tac [`g_out`, `tn_out`] >> simp[] >>
      rpt strip_tac >> metis_tac[]) >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> metis_tac[]) >>
  rename1 `!tail. CT (_ ++ tail) = (cr,am',rqs,obs)` >>
  disj2_tac >> qexistsl_tac [`cr`, `am'`, `rqs`, `obs`]
  >- (simp[] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon obs) obs` by
    fs[storage_trace_domain_def] >>
  simp[] >> metis_tac[]
QED

Theorem unit_execution_compose_result_mods:
  !(P : 'call_res -> bool) DF E ctx func cx st0 mods
    (source : evaluation_state -> ('body_res + exception) # evaluation_state)
    es0 s0 G0 tn0 Q R vs0 CT REL
    (EX : ('call_res # 'call_accounts # 'call_requests) -> bool) marks0.
    storage_trace_frame source /\
    storage_trace_domain cx st0 es0.storage_trace /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
       gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
         (vs0, FEMPTY, entry_taint) marks0 (OK s0, G0, tn0) /\
       ((!fuel. ptr_safe_run (DF H) 0 fuel ctx func [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY entry_taint
                 vs0)) /\
    gas_outcome_full_mods (DF, 0, E, ctx, func, []) mods cx st0 source
      (es0, s0, G0, tn0) Q R /\
    (!gobs res ee. source (es0 with gas_obs := gobs) = (res, ee) ==>
       SND (SND (SND (CT gobs))) = ee.storage_trace) /\
    (!gx res ee.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) ==>
       !tail. CT (gx ++ tail) = CT gx) /\
    (!gx err ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (INR (Error err), ee with gas_obs := tail)) /\
       unspecified_behaviour_exempt_mods mods err /\
       CT gx = (cr, am', rqs, obs) ==>
       EX (cr, am', rqs)) /\
    (!gx res ee t.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       (?H G tn. valid_horizon cx st0 H ee.storage_trace /\
                 Q H res (ee with gas_obs := []) G tn t) ==>
       ?r. exit_result r /\
         !H G tn. valid_horizon cx st0 H ee.storage_trace /\
                  Q H res (ee with gas_obs := []) G tn t ==>
           ?G' tn'.
             gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
               (t, G, tn) [] (r, G', tn') /\
             !cr am' rqs obs. CT gx = (cr, am', rqs, obs) ==>
               REL H (cr, am', rqs) r) /\
    (!gx res ee H gt r cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       valid_horizon cx st0 H ee.storage_trace /\
       exit_result r /\ R H res (ee with gas_obs := []) gt r /\
       CT gx = (cr, am', rqs, obs) ==>
       REL H (cr, am', rqs) r) /\
    (!gx res ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       CT gx = (cr, am', rqs, obs) ==> P cr) ==>
    ?marks.
      ((!tail. ~storage_trace_domain cx st0
                 (SND (SND (SND
                   (CT (gas_explicit marks s0.vs_gas_readings ++ tail)))))) /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
           (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
           (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      ?res am' rqs obs.
        (!tail. CT (gas_explicit marks s0.vs_gas_readings ++ tail) =
                (res, am', rqs, obs)) /\
        P res /\
        ((EX (res, am', rqs) /\
          ?H leaf leaf_pg leaf_g leaf_tn finish.
            gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
              (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
              (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
         (?r. exit_result r /\ storage_trace_domain cx st0 obs /\
            gas_origin_path T E ctx func vs0 (marks0 ++ marks) r /\
            !H. valid_horizon cx st0 H obs ==>
              REL H (res, am', rqs) r /\
              !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY
                       entry_taint vs0))
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.SPECL [`P`, `DF`, `E`, `ctx`, `func`, `cx`, `st0`, `mods`, `source`, `es0`, `s0`, `G0`, `tn0`, `Q`, `R`, `vs0`, `CT`, `REL`, `EX`, `marks0`] unit_execution_compose_result_horizon_mods) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
Theorem unit_execution_compose_result_horizon:
  !(P : 'call_res -> bool) DF E ctx func cx st0 tops
    (source : evaluation_state -> ('body_res + exception) # evaluation_state)
    es0 s0 G0 tn0 Q R vs0 CT REL
    (EX : ('call_res # 'call_accounts # 'call_requests) -> bool) marks0.
    storage_trace_frame source /\
    storage_trace_domain cx st0 es0.storage_trace /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
       gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
         (vs0, FEMPTY, entry_taint) marks0 (OK s0, G0, tn0) /\
       ((!fuel. ptr_safe_run (DF H) 0 fuel ctx func [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY entry_taint
                 vs0)) /\
    gas_outcome_full (DF, 0, E, ctx, func, []) tops cx st0 source
      (es0, s0, G0, tn0) Q R /\
    (!gobs res ee. source (es0 with gas_obs := gobs) = (res, ee) ==>
       (storage_trace_domain cx st0 (SND (SND (SND (CT gobs)))) <=>
        storage_trace_domain cx st0 ee.storage_trace) /\
       (!H. valid_horizon cx st0 H (SND (SND (SND (CT gobs)))) <=>
            valid_horizon cx st0 H ee.storage_trace)) /\
    (!gx res ee.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) ==>
       !tail. CT (gx ++ tail) = CT gx) /\
    (!gx err ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (INR (Error err), ee with gas_obs := tail)) /\
       unspecified_behaviour_exempt tops err /\
       CT gx = (cr, am', rqs, obs) ==>
       EX (cr, am', rqs)) /\
    (!gx res ee t.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       (?H G tn. valid_horizon cx st0 H ee.storage_trace /\
                 Q H res (ee with gas_obs := []) G tn t) ==>
       ?r. exit_result r /\
         !H G tn. valid_horizon cx st0 H ee.storage_trace /\
                  Q H res (ee with gas_obs := []) G tn t ==>
           ?G' tn'.
             gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
               (t, G, tn) [] (r, G', tn') /\
             !cr am' rqs obs. CT gx = (cr, am', rqs, obs) ==>
               REL H (cr, am', rqs) r) /\
    (!gx res ee H gt r cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       valid_horizon cx st0 H ee.storage_trace /\
       exit_result r /\ R H res (ee with gas_obs := []) gt r /\
       CT gx = (cr, am', rqs, obs) ==>
       REL H (cr, am', rqs) r) /\
    (!gx res ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       CT gx = (cr, am', rqs, obs) ==> P cr) ==>
    ?marks.
      ((!tail. ~storage_trace_domain cx st0
                 (SND (SND (SND
                   (CT (gas_explicit marks s0.vs_gas_readings ++ tail)))))) /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
           (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
           (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      ?res am' rqs obs.
        (!tail. CT (gas_explicit marks s0.vs_gas_readings ++ tail) =
                (res, am', rqs, obs)) /\
        P res /\
        ((EX (res, am', rqs) /\
          ?H leaf leaf_pg leaf_g leaf_tn finish.
            gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
              (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
              (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
         (?r. exit_result r /\ storage_trace_domain cx st0 obs /\
            gas_origin_path T E ctx func vs0 (marks0 ++ marks) r /\
            !H. valid_horizon cx st0 H obs ==>
              REL H (res, am', rqs) r /\
              !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY
                       entry_taint vs0))
Proof
  rewrite_tac[gas_outcome_full_singleton_def,
              GSYM unspecified_behaviour_exempt_mods_singleton] >>
  MATCH_ACCEPT_TAC unit_execution_compose_result_horizon_mods
QED

Theorem unit_execution_compose_result:
  !(P : 'call_res -> bool) DF E ctx func cx st0 tops
    (source : evaluation_state -> ('body_res + exception) # evaluation_state)
    es0 s0 G0 tn0 Q R vs0 CT REL
    (EX : ('call_res # 'call_accounts # 'call_requests) -> bool) marks0.
    storage_trace_frame source /\
    storage_trace_domain cx st0 es0.storage_trace /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
       gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
         (vs0, FEMPTY, entry_taint) marks0 (OK s0, G0, tn0) /\
       ((!fuel. ptr_safe_run (DF H) 0 fuel ctx func [] G0 tn0 s0) ==>
        !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY entry_taint
                 vs0)) /\
    gas_outcome_full (DF, 0, E, ctx, func, []) tops cx st0 source
      (es0, s0, G0, tn0) Q R /\
    (!gobs res ee. source (es0 with gas_obs := gobs) = (res, ee) ==>
       SND (SND (SND (CT gobs))) = ee.storage_trace) /\
    (!gx res ee.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) ==>
       !tail. CT (gx ++ tail) = CT gx) /\
    (!gx err ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (INR (Error err), ee with gas_obs := tail)) /\
       unspecified_behaviour_exempt tops err /\
       CT gx = (cr, am', rqs, obs) ==>
       EX (cr, am', rqs)) /\
    (!gx res ee t.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       storage_trace_domain cx st0 ee.storage_trace /\
       (?H G tn. valid_horizon cx st0 H ee.storage_trace /\
                 Q H res (ee with gas_obs := []) G tn t) ==>
       ?r. exit_result r /\
         !H G tn. valid_horizon cx st0 H ee.storage_trace /\
                  Q H res (ee with gas_obs := []) G tn t ==>
           ?G' tn'.
             gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
               (t, G, tn) [] (r, G', tn') /\
             !cr am' rqs obs. CT gx = (cr, am', rqs, obs) ==>
               REL H (cr, am', rqs) r) /\
    (!gx res ee H gt r cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       valid_horizon cx st0 H ee.storage_trace /\
       exit_result r /\ R H res (ee with gas_obs := []) gt r /\
       CT gx = (cr, am', rqs, obs) ==>
       REL H (cr, am', rqs) r) /\
    (!gx res ee cr am' rqs obs.
       (!tail. source (es0 with gas_obs := gx ++ tail) =
               (res, ee with gas_obs := tail)) /\
       CT gx = (cr, am', rqs, obs) ==> P cr) ==>
    ?marks.
      ((!tail. ~storage_trace_domain cx st0
                 (SND (SND (SND
                   (CT (gas_explicit marks s0.vs_gas_readings ++ tail)))))) /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
           (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
           (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      ?res am' rqs obs.
        (!tail. CT (gas_explicit marks s0.vs_gas_readings ++ tail) =
                (res, am', rqs, obs)) /\
        P res /\
        ((EX (res, am', rqs) /\
          ?H leaf leaf_pg leaf_g leaf_tn finish.
            gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
              (vs0, FEMPTY, entry_taint) (marks0 ++ marks)
              (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
         (?r. exit_result r /\ storage_trace_domain cx st0 obs /\
            gas_origin_path T E ctx func vs0 (marks0 ++ marks) r /\
            !H. valid_horizon cx st0 H obs ==>
              REL H (res, am', rqs) r /\
              !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY
                       entry_taint vs0))
Proof
  rewrite_tac[gas_outcome_full_singleton_def,
              GSYM unspecified_behaviour_exempt_mods_singleton] >>
  MATCH_ACCEPT_TAC unit_execution_compose_result_mods
QED
