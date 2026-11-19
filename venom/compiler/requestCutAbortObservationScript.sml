Theory requestCutAbortObservation
Ancestors
  requestCutEventAbort requestCutNativeEventCover dftStaticAbortCompletion dftStaticAbortExtension
  dftGasInvMemoryObservation dftGasToListReachBoundary dftGasOracleDefs
  dftContractGas dftRunRel dftWf dftCorrectness o1PassContract unitShapeDefs
  venomExecSemantics venomExecProofs venomInst venomWf venomState list arithmetic

(* On an OK rooted cut the retained source observation exists. This rules
   out the prior-static-write arm of the DFT pointwise correspondence. *)
Theorem request_cut_retained_abort_observation:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  ev_reachable orc initial C7 p d src inst u /\
  ev_reachable orc initial C8 p d dst inst t /\
  dst = dft_fn src /\ u.vs_current_bb = t.vs_current_bb /\
  inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET ==>
  (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op t) /\
  u.vs_initial_fmp = t.vs_initial_fmp /\ u.vs_requests = t.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY wf_function C7.ctx_functions /\
   EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
     fn.fn_blocks) C7.ctx_functions` by
    (drule o1_ctx_shape_wf_functions >> simp[] >>
     rewrite_tac[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  Cases_on `initial.vs_call_ctx.cc_static`
  >- (mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C8`, `fn'` |-> `dst`]
        inv_static_observation_source_completion_oracle) >>
      (impl_tac
       >- (conj_tac >- metis_tac[inv_remaining_trace_prefix_no_static_writes] >>
           conj_tac >- metis_tac[inv_static_ftrace_no_writes] >>
           rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac
      >- metis_tac[request_cut_event_visit_unique] >>
      suspend "static_write") >>
  `o1_run_state_ok initial` by simp[o1_run_state_ok_def] >>
  drule_all_then strip_assume_tac inv_reachable_memory_observation_oracle >>
  metis_tac[request_cut_event_visit_unique]
QED

Resume request_cut_retained_abort_observation[static_write]:
  `MEM src C7.ctx_functions /\ wf_function src` by
    metis_tac[ev_reachable_function_member, EVERY_MEM] >>
  `src.fn_name = fn.fn_name` by
    (qpat_assum `dst = dft_fn src` mp_tac >>
     qpat_assum `dst = dft_fn fn` mp_tac >> strip_tac >>
     disch_then (mp_tac o Q.AP_TERM `\f. f.fn_name`) >> simp[]) >>
  `src = fn` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
     metis_tac[all_distinct_map_mem_inj]) >>
  qpat_x_assum `src = fn` SUBST_ALL_TAC >>
  `bb.bb_label = sX.vs_current_bb` by fs[dft_remaining_inv_def] >>
  `u.vs_current_bb = sX.vs_current_bb` by
    metis_tac[lookup_block_label] >>
  `active_inst fn inst u` by
    (qpat_assum `ev_reachable orc initial C7 p d fn inst u` mp_tac >>
     rewrite_tac[Once ev_reachable_cases] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `get_instruction bb u.vs_inst_idx = SOME inst` by
    (drule_all_then strip_assume_tac active_inst_lookup_distinct >> gvs[]) >>
  `u.vs_inst_idx = LENGTH pseudos + LENGTH (a ++ x0::b)` by
    (`u.vs_inst_idx < LENGTH bb.bb_instructions /\
       EL u.vs_inst_idx bb.bb_instructions = inst` by gvs[get_instruction_def] >>
     `LENGTH pseudos + LENGTH (a ++ x0::b) < LENGTH bb.bb_instructions /\
      EL (LENGTH pseudos + LENGTH (a ++ x0::b)) bb.bb_instructions = inst` by
       simp[EL_APPEND_EQN] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
       metis_tac[wf_fn_block_inst_ids_distinct] >>
     `ALL_DISTINCT bb.bb_instructions` by
       metis_tac[ALL_DISTINCT_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  `sX.vs_inst_idx < u.vs_inst_idx` by simp[] >>
  metis_tac[event_visit_after_abort_impossible]
QED

Finalise request_cut_retained_abort_observation
