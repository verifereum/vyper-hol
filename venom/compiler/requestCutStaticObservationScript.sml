Theory requestCutStaticObservation
Ancestors
  dftStaticAbortCompletion dftStaticAbortExtension dftGasInvMemoryObservation
  dftGasInvPairedHistory dftGasInvFlexibleTrace dftGasInvTerminalReach dftGasOracleDefs dftRunRel dftDefs
  o1PassContract staticAbortDefs venomInst venomState list

(* A static observation has a C7 counterpart or a C7 write that faults
   before the observation. The second case supplies the C8 static suffix. *)
Theorem request_cut_observation_or_static_write:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  ev_reachable orc initial C8 p d fn8 inst t /\
  inv_memory_observation inst.inst_opcode /\ inst.inst_opcode <> DRET ==>
  (?fn7 u. ev_reachable orc initial C7 p d fn7 inst u /\ fn8 = dft_fn fn7 /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_initial_fmp = t.vs_initial_fmp /\
    u.vs_requests = t.vs_requests /\
    (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op t)) \/
  (in_static_abort_prefix fn8 t /\ ?fn7 op s.
    ev_reachable orc initial C7 p d fn7 op s /\
    MEM op.inst_opcode [SSTORE; TSTORE; LOG] /\ s.vs_call_ctx.cc_static /\
    IS_SOME (eval_operands op.inst_operands s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `initial.vs_call_ctx.cc_static`
  >- (mp_tac (Q.INST [`C` |-> `C7`, `C'` |-> `C8`, `fn'` |-> `fn8`]
        inv_static_observation_source_completion_oracle) >>
      (impl_tac
       >- (conj_tac >- metis_tac[inv_remaining_trace_prefix_no_static_writes] >>
           conj_tac >- metis_tac[inv_static_ftrace_no_writes] >>
           rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac
      >- (`inv_ev_ftrace orc p d C7 srcpre s0 sS` by
            (irule (iffRL inv_ev_ftrace_slice) >>
             qexistsl_tac [`pseudos`, `inst::srcpost`, `bb`] >>
             simp[APPEND_ASSOC]) >>
          disj1_tac >> qexistsl_tac [`fn`, `sS`] >> simp[] >>
          metis_tac[inv_ev_ftrace_current_bb]) >>
      disj2_tac >> conj_tac
      >- (drule_all_then ACCEPT_TAC inv_missing_write_static_abort_prefix) >>
      qexistsl_tac [`fn`, `x0`, `sX`] >> simp[]) >>
  `o1_run_state_ok initial` by simp[o1_run_state_ok_def] >>
  drule_all_then strip_assume_tac inv_reachable_memory_observation_oracle >>
  disj1_tac >> qexistsl_tac [`fn`, `sS`] >> simp[]
QED
