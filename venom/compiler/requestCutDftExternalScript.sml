Theory requestCutDftExternal
Ancestors
  dftGasInvObservationOracle
  requestCutDftStaticRequest dftStaticAbortCompletion dftGasInvExtraction
  dftGasInvPrefixReach dftGasInvRequestFields dftGasInvFlexibleTrace
  dftGasInvCrossingProbe dftGasInvOracleFrame
  dftGasFromListRestore dftGasToListReachBoundary dftRunRel dftGasOracleDefs o1PassContract unitShapeDefs
  contextCodegenRel jointRequestCut venomExecSemantics venomExecProofs venomWf venomInst venomState list

(* A reached scheduled call uses the same request fields in the original
   order. The static branch excludes a preceding write in this block. *)
Theorem request_cut_dft_external_fields:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C.ctx_functions /\
  ev_reachable orc initial C' p d fn' inst t /\ is_ext_call_op inst.inst_opcode ==>
  ?fn s.
    ev_reachable orc initial C p d fn inst s /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
    s.vs_memory = t.vs_memory /\ s.vs_accounts = t.vs_accounts /\
    s.vs_transient = t.vs_transient /\ s.vs_call_ctx = t.vs_call_ctx /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `initial.vs_call_ctx.cc_static`
  >- (drule_all request_cut_dft_static_external_fields >> simp[]) >>
  `inv_memory_observation inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def, inv_memory_observation_def]) >>
  drule_all inv_observation_normalized_setup >>
  disch_then (qx_choosel_then [`fn`,`s0`,`start`,`bb`,`bb'`,`pseudos`,
    `srcpre`,`srcpost`,`consumed`,`later`] strip_assume_tac) >>
  `o1_run_state_ok initial` by simp[o1_run_state_ok_def] >>
  `~s0.vs_call_ctx.cc_static` by metis_tac[inv_ev_reachable_nonstatic] >>
  drule_all inv_lookup_normalized_observation_oracle >>
  disch_then (qx_choose_then `sS` strip_assume_tac) >>
  `get_instruction bb sS.vs_inst_idx = SOME inst` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `active_inst fn start s0` by
    (qpat_assum `ev_reachable orc initial C p d fn start s0`
      (mp_tac o ONCE_REWRITE_RULE [ev_reachable_cases]) >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn)` by fs[dft_fn_rel_def, wf_function_def] >>
  drule_all active_inst_lookup_distinct >> strip_tac >>
  `get_instruction bb s0.vs_inst_idx = SOME start` by metis_tac[optionTheory.SOME_11] >>
  `bb.bb_label = s0.vs_current_bb` by metis_tac[lookup_block_label] >>
  `ev_reachable orc initial C p d fn inst sS` by
    (irule inv_ev_prefix_reachable >> qexistsl_tac [`bb`,`start`,`LENGTH srcpre`,`s0`] >>
     simp[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions` by
    (simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
     `MEM i (fn_insts fn)` by (simp[fn_insts_def, fn_insts_blocks_MEM] >> qexists_tac `bb` >> simp[]) >>
     qpat_x_assum `EVERY _ C.ctx_functions`
       (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
     disch_then (qspec_then `fn` mp_tac) >> simp[] >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  drule_all inv_lookup_normalized_external_request_fields >>
  strip_tac >> qexistsl_tac [`fn`,`sS`] >> simp[]
QED

Theorem request_cut_dft_recording:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C.ctx_functions /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  ev_reachable orc initial C' p d fn' inst t /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C' inst t = OK post /\
  LENGTH t.vs_requests < LENGTH post.vs_requests ==>
  ?fn s u.
    ev_reachable orc initial C p d fn inst s /\
    step_inst 0 C inst s = OK u /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >>
  `is_ext_call_op inst.inst_opcode` by
    (drule_all step_inst_request_outcomes >> Cases_on `inst.inst_opcode` >>
     simp[is_ext_call_op_def]) >>
  drule_all request_cut_dft_external_fields >> strip_tac >>
  drule_all request_step_same_fields >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  metis_tac[]
QED

Theorem request_cut_recording_restore:
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  step_inst fuel C inst s = OK u ==>
  step_inst fuel' C' inst (s with vs_gas_readings := gs) =
    OK (u with vs_gas_readings := gs)
Proof
  strip_tac >>
  `step_inst_base inst s = OK u` by metis_tac[step_inst_non_invoke] >>
  simp[step_inst_non_invoke] >>
  mp_tac (Q.INST [`inst` |-> `inst`, `gs` |-> `gs`, `s` |-> `s`] step_base_restore) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := gs)` >>
  simp[restore_rel_def]
QED

(* At the recording site only the remaining GAS tail changes when the
   event state is projected back to the selected native filling. *)
Theorem request_cut_dft_native_recording:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)) C.ctx_functions /\
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  (!fn s. ev_reachable orc initial C p d fn inst s /\ LENGTH s.vs_requests = k ==>
    ?ws. raw_reachable (initial with vs_gas_readings := filling) C fn inst
                      (s with vs_gas_readings := ws)) /\
  ev_reachable orc initial C' p d fn' inst (t with vs_gas_readings := initial.vs_gas_readings) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C' inst t = OK post /\
  LENGTH t.vs_requests = k /\ k < LENGTH post.vs_requests ==>
  ?fn s u.
    raw_reachable (initial with vs_gas_readings := filling) C fn inst s /\
    step_inst 0 C inst s = OK u /\
    s.vs_requests = t.vs_requests /\ s.vs_outcomes = t.vs_outcomes /\
    u.vs_requests = post.vs_requests /\ u.vs_outcomes = post.vs_outcomes
Proof
  strip_tac >>
  `LENGTH t.vs_requests < LENGTH post.vs_requests` by simp[] >>
  `inst.inst_opcode <> GAS` by (drule_all step_inst_request_outcomes >> Cases_on `inst.inst_opcode` >> simp[]) >>
  `step_inst fuel C' inst (t with vs_gas_readings := initial.vs_gas_readings) =
   OK (post with vs_gas_readings := initial.vs_gas_readings)` by
    metis_tac[request_cut_recording_restore] >>
  `LENGTH (t with vs_gas_readings := initial.vs_gas_readings).vs_requests <
   LENGTH (post with vs_gas_readings := initial.vs_gas_readings).vs_requests` by simp[] >>
  drule_all request_cut_dft_recording >> simp[] >> strip_tac >>
  `LENGTH s.vs_requests = k` by simp[] >>
  qpat_x_assum `!f state. _ ==> ?ws. raw_reachable _ _ f _ _`
    (qspecl_then [`fn`, `s`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  qexistsl_tac [`fn`,`s with vs_gas_readings := ws`,`u with vs_gas_readings := ws`] >>
  simp[] >> metis_tac[request_cut_recording_restore]
QED
