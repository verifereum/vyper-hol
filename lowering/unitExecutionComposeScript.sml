(*
 * A unit's execution from its entry, composed from a zero-GAS pointer path
 * from the entry state vs0 to the body's start s0 and the body's
 * gas_outcome_full at s0.  CT is the unit's call as a function of its gas
 * observations; its observations are the source's.  REL and EX say what the
 * call's result means for the unit (the runtime call's
 * external_call_result_rel and source_exempt, or the deployment's
 * counterparts).
 *
 * The conclusion has the source-unit shape: storage outside every horizon
 * with a focused prefix from vs0, an exempt result with a focused prefix, or
 * one exit reached from vs0 that every valid horizon relates and whose run
 * is pointer safe from vs0.
 *
 * TOP-LEVEL:
 *   unit_execution_compose
 *)
Theory unitExecutionCompose
Ancestors
  gasOutcomeFull fragGasOriginPtrExec fragGasOriginPtr fragGasOrigin
  gasExemptCert gasStorage fragExec fragExecPtr vyperStorageTrace
  vyperStorageFootprint ptrSafeRun ptrDiscipline vyperState venomState

(* A framed source extends its start's storage trace. *)
Theorem storage_trace_frame_extends[local]:
  storage_trace_frame f /\ f st = (r,t) ==>
  ?ys. t.storage_trace = st.storage_trace ++ ys
Proof
  rw[storage_trace_frame_def] >>
  first_x_assum (qspecl_then [`st`, `st.storage_trace`] mp_tac) >>
  `st with storage_trace := st.storage_trace = st` by
    simp[evaluation_state_component_equality] >>
  Cases_on `f (st with storage_trace := [])` >> simp[] >> metis_tac[]
QED

(* A horizon valid at a framed source's end is valid at its start. *)
Theorem valid_horizon_frame_start[local]:
  storage_trace_frame f /\ f st = (r,t) /\
  valid_horizon cx st0 H t.storage_trace ==>
  valid_horizon cx st0 H st.storage_trace
Proof
  strip_tac >> drule_all storage_trace_frame_extends >> strip_tac >>
  gvs[] >> metis_tac[valid_horizon_append]
QED

(* The entry prefix joins a focus from the body start. *)
Theorem entry_focus_prefix[local]:
  gas_origin_ptr_path X (s, G, tn) [] (OK s0, G0, tn0) /\
  gas_origin_ptr_focus X (s0, G0, tn0) marks out ==>
  gas_origin_ptr_focus X (s, G, tn) marks out
Proof
  PairCases_on `X` >> PairCases_on `out` >> strip_tac >>
  `marks = [] ++ marks` by simp[] >> pop_assum SUBST1_TAC >>
  irule (cj 2 gas_origin_ptr_focus_rules) >> metis_tac[]
QED

(* A pointer path to an exit makes the run from its start pointer safe at
   every fuel. *)
Theorem gas_origin_ptr_path_exit_safe[local]:
  gas_origin_ptr_path (D, lo, E, ctx, func, PG) (s, G, tn) marks
    (r, G', tn') /\ exit_result r ==>
  !fuel. ptr_safe_run D lo fuel ctx func PG G tn s
Proof
  strip_tac >> drule gas_origin_ptr_path_exec >> strip_tac >>
  gvs[exit_result_def] >>
  irule fragExecPtrTheory.ptr_safe_run_all_fuel >>
  metis_tac[exit_result_not_error]
QED

(* The entry prefix and a body path from s0 make one memory path from the
   entry. *)
Theorem entry_path_join[local]:
  gas_origin_ptr_path (D, lo, E, ctx, func, PG) (s, G, tn) []
    (OK s0, G0, tn0) /\
  gas_origin_ptr_path (D, lo, E, ctx, func, PG) (s0, G0, tn0) marks
    (r, G', tn') ==>
  gas_origin_ptr_path (D, lo, E, ctx, func, PG) (s, G, tn) marks
    (r, G', tn')
Proof
  strip_tac >> `marks = [] ++ marks` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_origin_ptr_path_append >> metis_tac[]
QED

Theorem unit_execution_compose:
  !DF E ctx func cx st0 tops source es0 s0 G0 tn0 Q R vs0 CT REL EX.
    storage_trace_frame source /\
    storage_trace_domain cx st0 es0.storage_trace /\
    (!H. valid_horizon cx st0 H es0.storage_trace ==>
       gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
         (vs0, FEMPTY, entry_taint) [] (OK s0, G0, tn0) /\
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
       REL H (cr, am', rqs) r) ==>
    ?marks.
      ((!tail. ~storage_trace_domain cx st0
                 (SND (SND (SND
                   (CT (gas_explicit marks s0.vs_gas_readings ++ tail)))))) /\
       ?H leaf leaf_pg leaf_g leaf_tn finish.
         gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
           (vs0, FEMPTY, entry_taint) marks
           (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
      ?res am' rqs obs.
        (!tail. CT (gas_explicit marks s0.vs_gas_readings ++ tail) =
                (res, am', rqs, obs)) /\
        ((EX (res, am', rqs) /\
          ?H leaf leaf_pg leaf_g leaf_tn finish.
            gas_origin_ptr_focus (DF H, 0, E, ctx, func, [])
              (vs0, FEMPTY, entry_taint) marks
              (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
         (?r. exit_result r /\ storage_trace_domain cx st0 obs /\
            gas_origin_path T E ctx func vs0 marks r /\
            !H. valid_horizon cx st0 H obs ==>
              REL H (res, am', rqs) r /\
              !fuel. ptr_safe_blocks (DF H) 0 fuel ctx func [] FEMPTY
                       entry_taint vs0))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_full_def]) >>
  qexists_tac `marks`
  >- ((* storage outside every horizon *)
      disj1_tac >> conj_tac
      >- (gen_tac >>
          Cases_on `source (es0 with gas_obs :=
                      gas_explicit marks s0.vs_gas_readings ++ tail)` >>
          rename1 `_ = (res, ee)` >>
          `SND (SND (SND (CT (gas_explicit marks s0.vs_gas_readings ++
                              tail)))) = ee.storage_trace` by metis_tac[] >>
          fs[gas_bad_storage_at_def] >>
          first_x_assum (qspec_then `tail` mp_tac) >> simp[]) >>
      `valid_horizon cx st0 H es0.storage_trace` by metis_tac[] >>
      metis_tac[entry_focus_prefix])
  >- ((* a run that reaches its end *)
      disj2_tac >>
      qabbrev_tac `gx = gas_explicit marks s0.vs_gas_readings` >>
      `source (es0 with gas_obs := gx) = (res, ee with gas_obs := [])` by
        (first_assum (qspec_then `[]`
           (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL]))) >>
      Cases_on `CT gx` >> rename1 `CT gx = (cr, rest)` >>
      PairCases_on `rest` >> rename1 `CT gx = (cr, am', rqs, obs)` >>
      `obs = ee.storage_trace` by
        (qpat_x_assum `!gobs res ee. _ ==> SND _ = _` drule >>
         asm_simp_tac (srw_ss()) []) >>
      `!tail. CT (gx ++ tail) = CT gx` by metis_tac[] >>
      qexistsl_tac [`cr`, `am'`, `rqs`, `obs`] >> simp[] >> disj2_tac >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
           valid_horizon cx st0 H es0.storage_trace` by
        (rpt strip_tac >>
         `valid_horizon cx st0 H (es0 with gas_obs := gx).storage_trace`
           suffices_by simp[] >>
         irule valid_horizon_frame_start >>
         qexistsl_tac [`source`, `res`, `ee with gas_obs := []`] >>
         asm_simp_tac (srw_ss()) []) >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
         ee.storage_trace` by fs[storage_trace_domain_def] >>
      qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
      Cases_on `exit_result r`
      >- ((* the body exits *)
          qexists_tac `r` >> simp[] >> conj_tac
          >- (`gas_origin_ptr_path (DF H0, 0, E, ctx, func, [])
                 (s0, G0, tn0) marks (r, G', tn')` by metis_tac[] >>
              `gas_origin_ptr_path (DF H0, 0, E, ctx, func, [])
                 (vs0, FEMPTY, entry_taint) [] (OK s0, G0, tn0)` by
                metis_tac[] >>
              metis_tac[entry_path_join, gas_origin_ptr_path_projections]) >>
          rpt strip_tac
          >- (first_x_assum irule >> simp[] >>
              qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
                drule >> strip_tac >> gvs[exit_result_def] >>
              metis_tac[]) >>
          `valid_horizon cx st0 H es0.storage_trace` by metis_tac[] >>
          `gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
             (s0, G0, tn0) marks (r, G', tn')` by metis_tac[] >>
          metis_tac[gas_origin_ptr_path_exit_safe]) >>
      (* the body falls through to t *)
      `?t. r = OK t /\
           !H. valid_horizon cx st0 H ee.storage_trace ==>
               gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
                 (s0, G0, tn0) marks (OK t, G', tn') /\
               Q H res (ee with gas_obs := []) G' tn' t` by
        (qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
           (fn th => assume_tac th >> drule th) >>
         strip_tac >> gvs[] >> qexists_tac `t` >> simp[] >>
         rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
      `?r'. exit_result r' /\
            !H G tn. valid_horizon cx st0 H ee.storage_trace /\
                     Q H res (ee with gas_obs := []) G tn t ==>
              ?G'' tn''.
                gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
                  (t, G, tn) [] (r', G'', tn'') /\
                !cr am' rqs obs. CT gx = (cr, am', rqs, obs) ==>
                  REL H (cr, am', rqs) r'` by
        (qpat_x_assum `!gx res ee t. _ ==> ?r. _` irule >>
         simp[] >> metis_tac[]) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
           ?G'' tn''. gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
             (vs0, FEMPTY, entry_taint) marks (r', G'', tn'') /\
             REL H (cr, am', rqs) r'` by
        (rpt strip_tac >>
         `valid_horizon cx st0 H es0.storage_trace` by metis_tac[] >>
         qpat_assum `!H. valid_horizon _ _ H es0.storage_trace ==> _ /\ _`
           drule >> strip_tac >>
         qpat_x_assum `!H G tn. _ /\ _ ==> ?G'' tn''. _`
           (qspecl_then [`H`, `G'`, `tn'`] mp_tac) >>
         simp[] >> strip_tac >>
         qexistsl_tac [`G''`, `tn''`] >> simp[] >>
         `gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
            (s0, G0, tn0) (marks ++ []) (r', G'', tn'')` by
           (irule gas_origin_ptr_path_append >> metis_tac[]) >>
         fs[] >> metis_tac[entry_path_join]) >>
      qexists_tac `r'` >> simp[] >> conj_tac
      >- (first_x_assum (qspec_then `H0` mp_tac) >> simp[] >>
          metis_tac[gas_origin_ptr_path_projections]) >>
      rpt strip_tac >- metis_tac[] >>
      `valid_horizon cx st0 H es0.storage_trace` by metis_tac[] >>
      `?G'' tn''. gas_origin_ptr_path (DF H, 0, E, ctx, func, [])
         (s0, G0, tn0) (marks ++ []) (r', G'', tn'')` by
        (qpat_x_assum `!H G tn. _ /\ _ ==> ?G'' tn''. _`
           (qspecl_then [`H`, `G'`, `tn'`] mp_tac) >>
         impl_tac >- metis_tac[] >> strip_tac >>
         qexistsl_tac [`G''`, `tn''`] >>
         irule gas_origin_ptr_path_append >> metis_tac[]) >>
      fs[] >> metis_tac[gas_origin_ptr_path_exit_safe]) >>
  (* an exempt error *)
  disj2_tac >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qabbrev_tac `gx = gas_explicit marks s0.vs_gas_readings` >>
  `!tail. source (es0 with gas_obs := gx ++ tail) =
          (INR (Error err), ee with gas_obs := tail)` by
    (gen_tac >>
     qpat_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `tail` mp_tac) >>
     Cases_on `source (es0 with gas_obs := gx ++ tail)` >>
     rename1 `source _ = (q, _)` >> Cases_on `q` >>
     gvs[ignore_bind_def, bind_def, return_def]) >>
  Cases_on `CT gx` >> rename1 `CT gx = (cr, rest)` >>
  PairCases_on `rest` >> rename1 `CT gx = (cr, am', rqs, obs)` >>
  `!tail. CT (gx ++ tail) = CT gx` by metis_tac[] >>
  qexistsl_tac [`cr`, `am'`, `rqs`, `obs`] >> simp[] >> disj1_tac >>
  conj_tac >- metis_tac[] >>
  `valid_horizon cx st0 H es0.storage_trace` by metis_tac[] >>
  metis_tac[entry_focus_prefix]
QED
