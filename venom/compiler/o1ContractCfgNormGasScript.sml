(* Reached GAS prefixes through the dispatched CFG normalization stage. *)
Theory o1ContractCfgNormGas
Ancestors
  o1ContractCfgNorm gasEventsContext gasEventsFuel gasEvents o1PassLift
  o1PassContract venomExecSemantics venomExecProofs venomInst venomState
  venomWf list option pair cfgNormSupplySim cfgNormDefs

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
