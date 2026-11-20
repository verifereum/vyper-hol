Theory requestCutRetainedGuard
Ancestors
  requestCutCfgFrontierGuard requestCutAbortGuard requestCutAbortObservation
  requestCutReplaySuffix unitMemInv stateFrame contextCodegenRel
  dftGasOracleDefs dftGasInvMemoryObservation dftRunRel dftDefs
  o1PassContract frameJointTransition venomInst venomState words list

(* A successful C7 cut supplies the observation even when the C9 walk
   stops at a failed spill guard before attempting the next instruction. *)
Theorem request_cut_retained_memory_guard:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  inst_shape_ok inst8 /\ inst8.inst_opcode <> DRET /\ ~in_revert_forward fn9 s9 /\
  LENGTH s9.vs_requests <= k /\
  (!r. MEM r cpl.cp_regions ==> eom <= r.sr_spill_base /\
    r.sr_spill_end <= w2n s9.vs_initial_fmp) /\
  mem_inv (\ctx fn i s. LENGTH s.vs_requests <= k ==> lowered_mem_fact eom ctx fn i s) C7 v7 /\
  (inv_memory_observation inst8.inst_opcode ==>
    ?fn7 u ws. raw_reachable v7 C7 fn7 inst8 (u with vs_gas_readings := ws) /\
      ~in_revert_forward fn7 u /\
      fn8 = dft_fn fn7 /\ u.vs_current_bb = s8.vs_current_bb /\
      ev_reachable orc initial C7 p d fn7 inst8 u /\
      ev_reachable orc initial C8 p d fn8 inst8 (s8 with vs_gas_readings := initial.vs_gas_readings)) ==>
  source_memory_reads_disjoint cpl inst9 s9 /\ context_source_memory_writes_disjoint cpl inst9 s9
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac request_cut_cfg_disjoint_guard >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> suspend "observation")) >>
  disch_then ACCEPT_TAC
QED

Resume request_cut_retained_memory_guard[observation]:
  strip_tac >> drule_all request_cut_cfg_guard_projection >> strip_tac >>
  `s8.vs_requests = s9.vs_requests` by
    (drule cfg_norm_joint_cursor_execution_frame >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_requests`) >> simp[execution_frame_def]) >>
  `!r. MEM r cpl.cp_regions ==> eom <= r.sr_spill_base /\
      r.sr_spill_end <= w2n s8.vs_initial_fmp` by metis_tac[] >>
  `inv_memory_observation inst8.inst_opcode ==>
   ?fn7 u. raw_reachable v7 C7 fn7 inst8 u /\ LENGTH u.vs_requests <= k /\
     ~in_revert_forward fn7 u /\ u.vs_initial_fmp = s8.vs_initial_fmp /\
     (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8)` by
    (strip_tac >>
     qpat_x_assum `inv_memory_observation _ ==> _` drule >> strip_tac >>
     rename1 `ev_reachable orc initial C7 p d fn7 inst8 x` >>
     mp_tac (Q.INST [`src` |-> `fn7`, `dst` |-> `fn8`,
       `u` |-> `x`,
       `t` |-> `s8 with vs_gas_readings := initial.vs_gas_readings`,
       `inst` |-> `inst8`] request_cut_retained_abort_observation) >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[eval_operand_def] >> strip_tac >>
     qexistsl_tac [`fn7`, `x with vs_gas_readings := ws`] >> gvs[in_revert_forward_def, eval_operand_def]) >>
  drule_all_then ACCEPT_TAC request_cut_paired_memory_guard
QED

Finalise request_cut_retained_memory_guard
