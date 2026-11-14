(* Reached GAS prefixes through the dispatched CFG normalization stage. *)
Theory o1ContractCfgNormGas
Ancestors
  o1ContractCfgNorm o1ContractCfgNormCursorBlocks o1ContractCfgNormCursorReturns
  o1ContractCfgNormCursorProjection
  gasEventsContext gasEventsFuel gasEvents o1PassLift
  o1PassContract venomExecSemantics venomExecProofs venomInst venomState
  venomWf list option pair cfgNormSupplySim cfgNormDefs o1SafeUpto unitMemInv
  frameFinitePrefix rich_list arithmetic

Theorem cfg_norm_iter_supply_gas_events_prefix:
  !n t fn fn' t'.
    supply_norm_inv t fn /\ EVERY label_positions_ok (fn_insts fn) /\
    cfg_norm_iter_supply n t fn = (fn',t') ==>
    !s fuel. fn_entry_state fn s ==>
      ?fuel' extra.
        gas_events_blocks fuel' D fn' s = gas_events_blocks fuel D fn s ++ extra /\
        (terminates (run_blocks fuel D fn s) ==>
          extra = [] /\ frame_result_rel (run_blocks fuel D fn s) (run_blocks fuel' D fn' s))
Proof
  Induct_on `n` >> rpt gen_tac
  >- (strip_tac >> gvs[cfg_norm_iter_supply_def] >> rpt strip_tac >>
      qexistsl_tac [`fuel`, `[]`] >> simp[] >>
      metis_tac[supply_run_blocks_frame_refl]) >>
  strip_tac >>
  Cases_on `cfg_norm_round_supply t fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply t fn = (mid,changed,t1)` >>
  `supply_norm_inv t1 mid /\ EVERY label_positions_ok (fn_insts mid) /\
   fn_entry_label mid = fn_entry_label fn` by metis_tac[supply_round_semantics] >>
  rpt strip_tac >>
  `fn_entry_state mid s` by gvs[fn_entry_state_def] >>
  drule_all cfg_norm_round_supply_gas_events_prefix >>
  disch_then (qspec_then `fuel` (qspec_then `D` strip_assume_tac)) >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def]
  >- (first_x_assum drule_all >>
      disch_then (qspec_then `m` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`fuel'`, `extra ++ extra'`] >>
      conj_tac >- simp[listTheory.APPEND_ASSOC] >>
      strip_tac >>
      `terminates (run_blocks m D mid s)` by
        metis_tac[frame_result_rel_terminates] >>
      gvs[] >> metis_tac[frame_result_rel_trans]) >>
  metis_tac[]
QED

Theorem cfg_norm_function_supply_gas_events_prefix:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
  cfg_norm_function_supply t fn = (fn',t') /\ fn_entry_state fn s ==>
  !fuel. ?fuel' extra.
    gas_events_blocks fuel' D fn' s = gas_events_blocks fuel D fn s ++ extra /\
    (terminates (run_blocks fuel D fn s) ==>
      extra = [] /\ frame_result_rel (run_blocks fuel D fn s) (run_blocks fuel' D fn' s))
Proof
  simp[cfg_norm_function_supply_def] >> strip_tac >>
  `supply_norm_inv t fn` by simp[supply_norm_inv_def] >>
  drule_all cfg_norm_iter_supply_gas_events_prefix >>
  simp[]
QED

Theorem cfg_norm_stage_supply_lookup[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' ==>
  !nm. OPTREL (\f g. ?t t'. ir_supply_covers_fn t f /\ ir_supply_inst_ok t /\
    cfg_norm_function_supply t f = (g,t'))
    (lookup_function nm C.ctx_functions) (lookup_function nm C'.ctx_functions)
Proof
  strip_tac >> drule cfg_norm_stage_functions >> strip_tac >>
  irule list_rel_lookup_function >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  metis_tac[cfg_norm_function_supply_identity]
QED

Theorem cfg_norm_stage_paired_gas_events_prefix[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions ==>
  !fuel nm f g s.
    lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm C'.ctx_functions = SOME g /\ fn_entry_state f s ==>
    ?m extra.
      gas_events_blocks m C' g s = gas_events_blocks fuel C f s ++ extra /\
      (terminates (run_blocks fuel C f s) ==>
        extra = [] /\ frame_result_rel (run_blocks fuel C f s) (run_blocks m C' g s))
Proof
  strip_tac >> drule cfg_norm_stage_supply_lookup >>
  disch_then (mk_asm "supply_lookup") >>
  `!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm C'.ctx_functions)` by
    (gen_tac >> asm "supply_lookup" (qspec_then `nm` mp_tac) >>
     Cases_on `lookup_function nm C.ctx_functions` >>
     Cases_on `lookup_function nm C'.ctx_functions` >> simp[] >>
     metis_tac[cfg_norm_function_supply_identity]) >>
  completeInduct_on `fuel` >> rpt strip_tac >>
  `MEM f C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  drule_all cfg_norm_stage_fn_ok >> strip_tac >>
  asm "supply_lookup" (qspec_then `nm` mp_tac) >> simp[] >> strip_tac >>
  `?m extra. gas_events_blocks m C' f s = gas_events_blocks fuel C f s ++ extra /\
    (terminates (run_blocks fuel C f s) ==> extra = [] /\
      frame_result_rel (run_blocks fuel C f s) (run_blocks m C' f s))` by
    (irule gas_events_blocks_same_caller >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  drule_all cfg_norm_function_supply_gas_events_prefix >>
  disch_then (qspec_then `C'` (qspec_then `m` strip_assume_tac)) >>
  qexistsl_tac [`fuel'`, `extra ++ extra'`] >> conj_tac
  >- simp[listTheory.APPEND_ASSOC] >>
  strip_tac >>
  `terminates (run_blocks m C' f s)` by metis_tac[frame_result_rel_terminates] >>
  gvs[] >> metis_tac[frame_result_rel_trans]
QED

Theorem cfg_norm_stage_gas_events_prefix:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  lookup_function name C.ctx_functions = SOME fn ==>
  ?fn'.
    lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = fn_entry_label fn /\
    !s fuel. fn_entry_state fn s ==>
      ?fuel' extra.
        gas_events_blocks fuel' C' fn' s =
          gas_events_blocks fuel C fn s ++ extra /\
        (terminates (run_blocks fuel C fn s) ==>
          extra = [] /\
          frame_result_rel (run_blocks fuel C fn s)
            (run_blocks fuel' C' fn' s) /\
          terminates (run_blocks fuel' C' fn' s))
Proof
  strip_tac >> drule cfg_norm_stage_supply_lookup >>
  disch_then (qspec_then `name` mp_tac) >> simp[OPTREL_SOME] >> strip_tac >>
  rename1 `lookup_function name C'.ctx_functions = SOME fn'` >>
  `fn_entry_label fn' = fn_entry_label fn` by
    metis_tac[cfg_norm_function_supply_identity] >>
  qexists_tac `fn'` >> simp[] >> rpt strip_tac >>
  drule_all cfg_norm_stage_paired_gas_events_prefix >>
  disch_then (qspec_then `fuel` mp_tac) >>
  metis_tac[frame_result_rel_terminates]
QED

(* The cut is measured from the context's initial state, including in callees. *)
Theorem cfg_norm_stage_static_mem_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  mem_inv (\ctx fn inst s. gas_cut k vs s ==>
             static_mem_ok eom ctx fn inst s) C vs ==>
  mem_inv (\ctx fn inst s. gas_cut k vs s ==>
             static_mem_ok eom ctx fn inst s) C' vs
Proof
  strip_tac >>
  `ctx_bisim C C'` by (irule cfg_norm_stage_bisim >> metis_tac[]) >>
  `mem_corr_closed_rf (\ctx fn inst s. gas_cut k vs s ==>
     static_mem_ok eom ctx fn inst s)` by
    (`mem_corr_closed_rf (\ctx fn inst s.
        (\r. LENGTH vs.vs_gas_readings < k + LENGTH r) s.vs_gas_readings ==>
        static_mem_ok eom ctx fn inst s)` by
       (irule mem_corr_closed_rf_readings_guard >>
        simp[mem_corr_closed_rf_static_mem_ok]) >>
     fs[gas_cut_def]) >>
  drule cfg_norm_stage_functions >> strip_tac >>
  irule frame_sim_rf_mem_inv >> simp[] >>
  qexists_tac `C` >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule cfg_norm_function_supply_identity >> strip_tac >> simp[] >>
  `MEM (EL n C.ctx_functions) C.ctx_functions` by simp[EL_MEM] >>
  drule_all cfg_norm_stage_fn_ok >> strip_tac >>
  metis_tac[cfg_norm_function_supply_frame_sim,
            cfg_norm_function_supply_frame_sim_rf]
QED

Theorem cfg_norm_stage_safe_gas_events_prefix:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  max_live_eom C = SOME eom /\
  mem_inv (\ctx fn inst s. gas_cut k vs s ==>
             static_mem_ok eom ctx fn inst s) C vs ==>
  C'.ctx_entry = SOME name /\ max_live_eom C' = SOME eom /\
  mem_inv (\ctx fn inst s. gas_cut k vs s ==>
             static_mem_ok eom ctx fn inst s) C' vs /\
  ?fn'. lookup_function name C'.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    !fuel. ?fuel' extra.
      gas_events_blocks fuel' C' fn'
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) =
      gas_events_blocks fuel C fn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) ++ extra /\
      (0 < k /\ k <= LENGTH (gas_events_blocks fuel C fn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
       finite_run_prefix C' fn'
         (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
         (TAKE k (gas_events_blocks fuel C fn
           (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)))) /\
      (terminates (run_blocks fuel C fn
        (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) ==>
       extra = [] /\
       frame_result_rel
         (run_blocks fuel C fn
           (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
         (run_blocks fuel' C' fn'
           (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
       terminates (run_blocks fuel' C' fn'
         (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)))
Proof
  strip_tac >>
  `C'.ctx_entry = SOME name` by gvs[ctx_pass_stage_def] >>
  `max_live_eom C' = SOME eom` by metis_tac[cfg_norm_stage_max_live_eom] >>
  drule_all cfg_norm_stage_static_mem_upto >> strip_tac >> simp[] >>
  drule_all cfg_norm_stage_gas_events_prefix >> strip_tac >>
  qexists_tac `fn'` >> simp[] >> gen_tac >>
  qabbrev_tac `entry = vs with
    <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `fn_entry_state fn entry` by simp[Abbr `entry`, fn_entry_state_def] >>
  first_x_assum (qspecl_then [`entry`, `fuel`] mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`fuel'`, `extra`] >> simp[] >> strip_tac >>
  `finite_run_prefix C' fn' entry
     (TAKE k (gas_events_blocks fuel' C' fn' entry))` by
    (irule gas_events_blocks_prefix >> simp[]) >>
  gvs[TAKE_APPEND1]
QED

(* A terminating normalized run has a terminating original run. *)
Theorem cfg_norm_stage_terminates_back:
  ctx_pass_stage rpolicy (CFP_Simple VP_CFGNormalization) view C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  lookup_function name C'.ctx_functions = SOME fn' ==>
  ?fn. lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = fn_entry_label fn' /\
    !s fuel'. fn_entry_state fn s /\ terminates (run_blocks fuel' C' fn' s) ==>
      ?fuel. terminates (run_blocks fuel C fn s)
Proof
  strip_tac >> drule cfg_norm_stage_supply_lookup >>
  disch_then (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name C.ctx_functions` >> simp[] >> strip_tac >>
  rename1 `lookup_function name C.ctx_functions = SOME fn` >>
  drule_all cfg_norm_stage_bisim >> simp[ctx_bisim_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[frame_result_rel_terminates]
QED
