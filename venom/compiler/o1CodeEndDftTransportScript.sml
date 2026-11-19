Theory o1CodeEndDftTransport
Ancestors
  o1CodeEndCfgNormTransport unitTransformDefs
  dftGasInvResidualTrace gasOracleReplay dftGasInvMemoryObservation
  o1LabelFlowLateDft o1ContractDft codegenSymRel
  dftGasOracleDefs dftRunRel venomExecSemantics venomInstProofs1
  o1PassContract unitShapeDefs venomState contextCodegenRel venomExecProps
  dftGasInvCrossingProbe list dftContractGas dftGasOracleFromList
  dftGasOracleToList dftGasOracleSim dftGasOracleInv o1DftStageSim
  o1DftStageSsa venomPassSchedule venomRetProps stackPlanGen
  contextRawReachable unitMemInv venomInst dftCorrectnessFinal
  dftStaticAbortCompletion dftStaticAbortInterval dftStaticAbortExtension
  dftWaveStaticGasContract staticShadowEventReachable staticAbortDefs

Theorem dft_ev_code_end_offset_ok[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  code_end_offset_ok (\ctx fn inst t. ?p d. ev_reachable orc initial ctx p d fn inst t) C ==>
  code_end_offset_ok (\ctx fn inst t. ?p d. ev_reachable orc initial ctx p d fn inst t) C'
Proof
  strip_tac >> rw[code_end_offset_ok_def] >>
  `inv_memory_observation inst.inst_opcode` by simp[inv_memory_observation_def] >>
  drule_all inv_reachable_memory_observation >>
  disch_then (qx_choosel_then
    [`source`,`source_state`,`source_block`,`target_block`] strip_assume_tac) >>
  `o1_fn_shape C source` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
  `EVERY label_positions_ok (fn_insts source)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
  `code_end_var source x` by metis_tac[dft_code_end_var_reflect] >>
  `source_state.vs_labels = t.vs_labels` by metis_tac[ev_reachable_labels] >>
  fs[code_end_offset_ok_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[MEM]
QED

(* Use the two reachability directions for the same supplied filling and oracle. *)
Theorem dft_fixed_filling_code_end_offset_ok:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 vs0.vs_labels /\ o1_run_state_ok vs0 /\
  code_end_offset_ok (raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])) C7 /\
  (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s ==>
     ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w]) C7 fn inst
            (s with vs_gas_readings := ws)) /\
  (!fn inst s. raw_reachable vs0 C8 fn inst s ==>
     ?p d. ev_reachable orc vs0 C8 p d fn inst
             (s with vs_gas_readings := vs0.vs_gas_readings)) ==>
  code_end_offset_ok (raw_reachable vs0) C8
Proof
  strip_tac >>
  `code_end_offset_ok
    (\ctx fn inst s. ?p d. ev_reachable orc vs0 ctx p d fn inst s) C7` by
    (rw[code_end_offset_ok_def] >>
     first_x_assum drule >> strip_tac >>
     rename1 `eval_operand (Var _) s = SOME _` >>
     qpat_x_assum `code_end_offset_ok (raw_reachable _) C7`
       (mp_tac o REWRITE_RULE [code_end_offset_ok_def]) >>
     disch_then (qspecl_then [`fn`, `inst`, `s with vs_gas_readings := ws`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  drule_all dft_ev_code_end_offset_ok >>
  simp[code_end_offset_ok_def] >> strip_tac >> rpt strip_tac >>
  rename1 `raw_reachable vs0 C8 fn inst s` >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspecl_then
    [`fn`, `inst`, `s with vs_gas_readings := vs0.vs_gas_readings`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem dft_ctx_code_end_sim_gas[local]:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim_fuel I D C C' vs vs' /\
    (o1_lowered_inv C vs /\ code_end_offset_ok (raw_reachable vs) C ==>
     o1_lowered_inv C' vs' /\ code_end_offset_ok (raw_reachable vs') C')
Proof
  strip_tac >> drule_all dft_ctx_sim_gas_oracle >>
  disch_then (qspec_then `D`
    (qx_choosel_then [`source_state`,`orc`] strip_assume_tac)) >>
  qexists_tac `source_state` >> simp[] >> strip_tac >>
  `code_end_offset_ok
    (\ctx fn inst t. ?p d. ev_reachable orc vs' ctx p d fn inst t) C` by
    (rw[code_end_offset_ok_def] >>
     first_x_assum drule >> strip_tac >>
     fs[code_end_offset_ok_def] >>
     first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all dft_ev_code_end_offset_ok >>
  simp[code_end_offset_ok_def] >> strip_tac >> rpt strip_tac >>
  rename1 `raw_reachable vs' C' fn inst target_state` >>
  first_x_assum drule >> strip_tac >>
  first_x_assum (qspecl_then
    [`fn`, `inst`, `target_state with vs_gas_readings := vs'.vs_gas_readings`] mp_tac) >>
  simp[] >> metis_tac[]
QED


Theorem dft_code_end_stage_contract_gas:
  !C C' vs'.
    ctx_pass_stage rpolicy (EL 7 o1_fn_passes)
      (o1_walk_view rpolicy 7) C C' /\
    o1_pre 7 C C' /\ dead_wf D /\ o1_ctx_shape C /\
    o1_run_state_ok vs' ==>
    ?vs. gas_variant vs vs' /\
      (o1_inv D 7 C vs /\ code_end_offset_ok (raw_reachable vs) C ==>
       ctx_sim_fuel (pass_fuel (EL 7 o1_fn_passes) C') D C C' vs vs' /\
       o1_inv D 8 C' vs' /\ code_end_offset_ok (raw_reachable vs') C')
Proof
  simp[o1_stage_contract_gas_def, o1_inv_def, o1_ssa_inv_def, pass_fuel_def] >>
  rpt strip_tac >> rename1 `o1_run_state_ok vs'` >>
  Cases_on `EVERY wf_ssa C.ctx_functions`
  >- (`ctx_pass_stage rpolicy (CFP_Simple VP_DFT) (o1_walk_view rpolicy 7) C C'` by
        gvs[o1_fn_passes_def] >>
      drule_all dft_stage_fn_rel >> strip_tac >>
      drule ctx_pass_stage_dft >> strip_tac >>
      `ctx_labels_bound C vs'.vs_labels` by
        (irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]) >>
      drule_all dft_ctx_code_end_sim_gas >>
      disch_then (qspec_then `D` (qx_choose_then `source_state` strip_assume_tac)) >>
      qexists_tac `source_state` >> simp[o1_fn_passes_def] >> rpt strip_tac >>
      `o1_lowered_inv C' vs' /\ code_end_offset_ok (raw_reachable vs') C'` by
        metis_tac[] >>
      simp[] >> irule dft_stage_wf_ssa >> metis_tac[]) >>
  qexists_tac `vs'` >> simp[gas_variant_refl]
QED

(* A scheduled CODECOPY either has a real source observation or was
   advanced into the straight prefix of a faulting static write. *)
Theorem dft_ev_codecopy_source_static_oracle:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  ev_reachable orc initial C' p d fn' inst t /\
  inst.inst_opcode = CODECOPY /\ MEM (Var x) inst.inst_operands /\
  code_end_var fn' x ==>
  (?fn s. ev_reachable orc initial C p d fn inst s /\ code_end_var fn x /\
          eval_operand (Var x) s = eval_operand (Var x) t /\
          s.vs_labels = t.vs_labels /\ s.vs_requests = t.vs_requests) \/
  (in_static_abort_prefix fn' t /\
   !fuel. terminates (ev_context orc fuel C initial) ==>
          ?u. ev_context orc fuel C initial = Abort ExHalt_abort u)
Proof
  strip_tac >>
  `inv_memory_observation inst.inst_opcode` by simp[inv_memory_observation_def] >>
  `!fn. MEM fn C.ctx_functions /\ fn' = dft_fn fn ==> code_end_var fn x` by
    (rpt strip_tac >>
     `o1_fn_shape C fn` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
     `EVERY label_positions_ok (fn_insts fn)` by
       fs[o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >>
     metis_tac[dft_code_end_var_reflect]) >>
  Cases_on `initial.vs_call_ctx.cc_static`
  >- (mp_tac inv_static_observation_source_completion_oracle >>
      impl_tac
      >- (conj_tac >- metis_tac[inv_remaining_trace_prefix_no_static_writes] >>
          conj_tac >- metis_tac[inv_static_ftrace_no_writes] >>
          simp[]) >>
      strip_tac
      >- suspend "observation" >>
      suspend "write") >>
  `o1_run_state_ok initial` by simp[o1_run_state_ok_def] >>
  drule_all inv_reachable_memory_observation_oracle >> strip_tac >>
  disj1_tac >> metis_tac[ev_reachable_labels]
QED

Resume dft_ev_codecopy_source_static_oracle[observation]:
  disj1_tac >> metis_tac[ev_reachable_labels]
QED

Resume dft_ev_codecopy_source_static_oracle[write]:
  `active_inst fn' inst t` by
    (qpat_assum `ev_reachable orc initial C' p d fn' inst t` mp_tac >>
     rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
  `in_static_abort_prefix fn' t` by
    (drule_all_then ACCEPT_TAC inv_missing_write_static_abort_prefix) >>
  disj2_tac >> conj_tac
  >- first_assum ACCEPT_TAC >>
  `EVERY wf_function C.ctx_functions` by metis_tac[o1_ctx_shape_wf_functions] >>
  metis_tac[ev_reachable_static_write_exhalt]
QED

Finalise dft_ev_codecopy_source_static_oracle

Theorem dft_ev_codecopy_source_static:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  ev_reachable orc initial C' p d fn' inst t /\
  inst.inst_opcode = CODECOPY /\ MEM (Var x) inst.inst_operands /\
  code_end_var fn' x ==>
  (?fn s. ev_reachable orc initial C p d fn inst s /\ code_end_var fn x /\
          eval_operand (Var x) s = eval_operand (Var x) t /\
          s.vs_labels = t.vs_labels) \/
  (in_static_abort_prefix fn' t /\
   !fuel. terminates (ev_context orc fuel C initial) ==>
          ?u. ev_context orc fuel C initial = Abort ExHalt_abort u)
Proof
  strip_tac >> drule_all dft_ev_codecopy_source_static_oracle >> metis_tac[]
QED

Theorem dft_code_end_offset_ok_fixed:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C vs.vs_labels /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  (!fuel. gas_res_rel (run_context fuel C source) (ev_context orc fuel C vs)) /\
  (!p d fn inst t. ev_reachable orc vs C p d fn inst t ==>
     ?ws. raw_reachable source C fn inst (t with vs_gas_readings := ws)) /\
  (!fn inst t. raw_reachable vs C' fn inst t ==>
     ?p d. ev_reachable orc vs C' p d fn inst
       (t with vs_gas_readings := vs.vs_gas_readings)) /\
  code_end_offset_ok (raw_reachable source) C ==>
  code_end_offset_ok
    (\ctx fn inst s. raw_reachable vs ctx fn inst s /\ ~in_static_abort_prefix fn s)
    C' /\
  (code_end_offset_ok (raw_reachable vs) C' \/
   !fuel. terminates (run_context fuel C source) ==>
          ?u. run_context fuel C source = Abort ExHalt_abort u)
Proof
  strip_tac >>
  `!fn inst t dst x sz w base.
    raw_reachable vs C' fn inst t /\ inst.inst_opcode = CODECOPY /\
    inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
    eval_operand (Var x) t = SOME w /\ FLOOKUP t.vs_labels "code_end" = SOME base /\
    ~(w2n (w - base) < dimword (:256) DIV 2) ==>
    in_static_abort_prefix fn t /\
    !fuel. terminates (run_context fuel C source) ==>
           ?u. run_context fuel C source = Abort ExHalt_abort u` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!fn inst t. raw_reachable vs C' fn inst t ==> _` drule >>
     strip_tac >>
     `MEM (Var x) inst.inst_operands` by simp[] >>
     drule_all dft_ev_codecopy_source_static >> strip_tac
     >- (qpat_x_assum `!p d fn inst t. ev_reachable _ _ C p d fn inst t ==> _`
           drule >> strip_tac >>
         rename1 `FLOOKUP t.vs_labels "code_end" = SOME bword` >>
         qpat_x_assum `code_end_offset_ok (raw_reachable source) C`
           (mp_tac o REWRITE_RULE [code_end_offset_ok_def]) >>
         disch_then (qspecl_then [`fn'`, `inst`, `s with vs_gas_readings := ws`,
                                  `dst`, `x`, `sz`, `w`, `bword`] mp_tac) >>
         gvs[eval_operand_def, lookup_var_def]) >>
     fs[in_static_abort_prefix_def] >> rpt strip_tac >>
     `terminates (ev_context orc fuel C vs)` by
       metis_tac[gas_res_rel_terminates] >>
     qpat_x_assum `!f. terminates (ev_context orc f C vs) ==> _` drule >>
     strip_tac >>
     qpat_x_assum `!f. gas_res_rel (run_context f C source) _`
       (qspec_then `fuel` mp_tac) >>
     Cases_on `run_context fuel C source` >> simp[gas_res_rel_def]) >>
  conj_tac
  >- (rw[code_end_offset_ok_def] >> metis_tac[]) >>
  Cases_on `code_end_offset_ok (raw_reachable vs) C'` >> simp[] >>
  qpat_x_assum `~code_end_offset_ok (raw_reachable vs) C'` mp_tac >>
  simp[code_end_offset_ok_def] >> metis_tac[]
QED

(* Request histories are unchanged by the gas-reading state updates. *)
Theorem dft_code_end_offset_ok_under_requests:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C vs.vs_labels /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  (!p d fn inst t. ev_reachable orc vs C p d fn inst t /\ P t.vs_requests ==>
     ?ws. raw_reachable source C fn inst (t with vs_gas_readings := ws)) /\
  (!fn inst t. raw_reachable vs C' fn inst t /\ P t.vs_requests /\
     ~in_static_abort_prefix fn t ==>
     ?p d. ev_reachable orc vs C' p d fn inst
       (t with vs_gas_readings := vs.vs_gas_readings)) /\
  code_end_offset_ok
    (\ctx fn inst s. raw_reachable source ctx fn inst s /\ P s.vs_requests) C ==>
  code_end_offset_ok
    (\ctx fn inst s. raw_reachable vs ctx fn inst s /\ P s.vs_requests /\
                     ~in_static_abort_prefix fn s) C'
Proof
  strip_tac >> simp[code_end_offset_ok_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `raw_reachable vs C' fn inst target` >>
  qpat_x_assum `!fn inst t. raw_reachable vs C' fn inst t /\ P t.vs_requests /\
     ~in_static_abort_prefix fn t ==> _`
    drule_all >> strip_tac >>
  `MEM (Var x) inst.inst_operands` by simp[] >>
  drule_all dft_ev_codecopy_source_static_oracle >> strip_tac
  >- (rename1 `ev_reachable orc vs C p d source_fn inst source_state` >>
      `P source_state.vs_requests` by fs[] >>
      qpat_x_assum `!p d fn inst t. ev_reachable _ _ C p d fn inst t /\ P t.vs_requests ==> _`
        drule_all >> strip_tac >>
      rename1 `FLOOKUP target.vs_labels "code_end" = SOME bword` >>
      qpat_x_assum `code_end_offset_ok _ C`
        (mp_tac o REWRITE_RULE [code_end_offset_ok_def]) >>
      disch_then (qspecl_then [`source_fn`, `inst`, `source_state with vs_gas_readings := ws`,
                               `dst`, `x`, `sz`, `w`, `bword`] mp_tac) >>
      gvs[eval_operand_def, lookup_var_def]) >>
  fs[in_static_abort_prefix_def]
QED

Theorem o1_code_end_dft_exit_fixed:
  ctx_pass_stage rp (CFP_Simple VP_DFT) dft_view C7 C8 /\ o1_pre 7 C7 C8 /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) cfg_view C8 C9 /\
  o1_ctx_shape C7 /\ EVERY wf_ssa C7.ctx_functions /\ o1_ctx_shape C8 /\
  o1_initial_state_ok vs_out /\ vs_out.vs_fmp = vs_out.vs_initial_fmp /\
  code_layout_valid vs_out /\
  (!fuel. gas_res_rel
    (run_context fuel C7 (vs_out with vs_gas_readings := rds))
    (ev_context orc fuel C7 vs_out)) /\
  (!p d fn inst t. ev_reachable orc vs_out C7 p d fn inst t ==>
     ?ws. raw_reachable (vs_out with vs_gas_readings := rds) C7 fn inst
              (t with vs_gas_readings := ws)) /\
  (!fn inst t. raw_reachable vs_out C8 fn inst t ==>
     ?p d. ev_reachable orc vs_out C8 p d fn inst
              (t with vs_gas_readings := vs_out.vs_gas_readings)) /\
  code_end_offset_ok (raw_reachable (vs_out with vs_gas_readings := rds)) C7 ==>
  code_end_offset_ok
    (\ctx fn inst s. raw_reachable vs_out ctx fn inst s /\ ~in_static_abort_prefix fn s)
    C9 /\
  (code_end_offset_ok (raw_reachable vs_out) C9 \/
   !fuel. terminates (run_context fuel C7 (vs_out with vs_gas_readings := rds)) ==>
      ?u. run_context fuel C7 (vs_out with vs_gas_readings := rds) = Abort ExHalt_abort u)
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  `EVERY wf_ssa C8.ctx_functions` by
    (irule dft_stage_wf_ssa >> metis_tac[]) >>
  `ctx_labels_bound C7 vs_out.vs_labels` by
    (irule dft_ctx_labels_bound >> simp[]) >>
  drule_all dft_code_end_offset_ok_fixed >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  `vs_out.vs_vars = FEMPTY /\ ~vs_out.vs_halted` by fs[o1_initial_state_ok_def] >>
  conj_tac
  >- (mp_tac (Q.INST [`guarded` |-> `T`, `C` |-> `C8`, `C'` |-> `C9`,
      `vs` |-> `vs_out`, `rpolicy` |-> `rp`, `view` |-> `cfg_view`] cfg_norm_code_end_offset_ok) >>
      simp[]) >>
  qpat_x_assum `code_end_offset_ok (raw_reachable vs_out) C8 \/ _`
    (DISJ_CASES_THEN assume_tac) >> simp[] >>
  disj1_tac >>
  mp_tac (Q.INST [`guarded` |-> `F`, `C` |-> `C8`, `C'` |-> `C9`,
    `vs` |-> `vs_out`, `rpolicy` |-> `rp`, `view` |-> `cfg_view`] cfg_norm_code_end_offset_ok) >>
  fs[code_end_offset_ok_def] >> metis_tac[]
QED
