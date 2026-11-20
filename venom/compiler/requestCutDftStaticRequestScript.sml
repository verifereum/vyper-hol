Theory requestCutDftStaticRequest
Ancestors
  dftStaticAbortCompletion dftStaticAbortExtension dftGasInvExtraction
  dftGasInvRequestFields dftGasInvCrossingProbe dftScheduleOrder dftRunRel
  dftGasOracleDefs o1PassContract unitShapeDefs contextCodegenRel
  venomEffects venomInst venomState venomWf passSharedDefs pred_set list

(* The static-write alternative at a scheduled observation cannot precede
   an external request that has already reached its scheduled cursor. *)
Theorem external_static_write_must_order[local]:
  is_ext_call_op obs.inst_opcode /\ MEM x.inst_opcode [SSTORE; TSTORE; LOG] ==>
  dft_must_order x obs
Proof
  strip_tac >>
  `read_effects obs.inst_opcode = all_effects` by
    (Cases_on `obs.inst_opcode` >> gvs[is_ext_call_op_def, read_effects_def]) >>
  fs[MEM] >> gvs[dft_must_order_def, write_effects_def, all_effects_def, DISJOINT_INSERT]
QED

Theorem request_cut_dft_static_external_fields:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  initial.vs_call_ctx.cc_static /\
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
  `inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET` by
    (Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def, inv_memory_observation_def]) >>
  mp_tac (Q.INST [`C` |-> `C`, `C'` |-> `C'`,
    `p` |-> `p`, `d` |-> `d`, `orc` |-> `orc`, `inst` |-> `inst`, `t` |-> `t`,
    `initial` |-> `initial`, `fn'` |-> `fn'`]
    inv_static_observation_source_completion_oracle) >>
  impl_tac
  >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE all_tac) >>
      metis_tac[inv_remaining_trace_prefix_no_static_writes, inv_static_ftrace_no_writes]) >>
  strip_tac
  >- (`EVERY (\i. i.inst_opcode <> ALLOCA) bb.bb_instructions` by
        (simp[EVERY_MEM] >> qx_gen_tac `i` >> strip_tac >>
         `MEM i (fn_insts fn)` by (simp[fn_insts_def, fn_insts_blocks_MEM] >> qexists_tac `bb` >> simp[]) >>
         qpat_x_assum `EVERY _ C.ctx_functions`
           (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
         disch_then (qspec_then `fn` mp_tac) >> simp[] >>
         disch_then (qspec_then `i` mp_tac) >> simp[]) >>
      drule_all inv_lookup_normalized_external_request_fields >> strip_tac >>
      qexistsl_tac [`fn`, `sS`] >> simp[]) >>
  drule_all inv_lookup_missing_predecessors >>
  simp[EVERY_MEM, MEM_FILTER] >> strip_tac >>
  `MEM x0 srcpre` by simp[MEM_APPEND] >>
  metis_tac[external_static_write_must_order]
QED
