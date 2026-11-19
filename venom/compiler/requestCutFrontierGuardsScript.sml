Theory requestCutFrontierGuards
Ancestors
  requestCutStoppedObservation requestCutRetainedGuard requestCutRetainedCodeEnd
  requestCutCfgFrontierGuard requestCutCfgCodeEnd frameJointTransition
  codegenEntrySim unitMemInv codegenSymRel o1PassContract contextCodegenRel
  dftGasOracleDefs dftRunRel dftDefs staticAbortDefs venomInst venomState
  venomExecSemantics venomWf asmIR finite_map words list

(* At or before the request cut, a stopped check either leads into the
   certified static suffix or leaves an executable primitive terminal. *)
Theorem request_cut_frontier_guards:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  LIST_REL (\fn fn'. fn' = dft_fn fn) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  C8.ctx_entry = C7.ctx_entry /\ o1_ctx_shape C7 /\
  ctx_labels_bound C7 initial.vs_labels /\ o1_initial_state_ok initial /\
  initial.vs_fmp = initial.vs_initial_fmp /\ code_layout_valid initial /\
  EVERY wf_function C8.ctx_functions /\ raw_reachable initial C8 fn8 inst8 s8 /\
  inst_shape_ok inst8 /\ inst8.inst_opcode <> DRET /\ ~in_revert_forward fn9 s9 /\
  LENGTH s9.vs_requests <= k /\
  (!r. MEM r cpl.cp_regions ==> eom <= r.sr_spill_base /\
    r.sr_spill_end <= w2n s9.vs_initial_fmp) /\
  mem_inv (\ctx fn i s. LENGTH s.vs_requests <= k ==> lowered_mem_fact eom ctx fn i s) C7 v7 /\
  (guarded ==> code_end_offset_ok
    (\ctx fn i s. raw_reachable v7 ctx fn i s /\ LENGTH s.vs_requests <= k) C7) /\
  codegen_asm_entry_rel cpl prog initial a0 /\
  (inv_memory_observation inst8.inst_opcode /\ ~in_revert_forward fn8 s8 ==>
    ((?fn7 u ws. raw_reachable v7 C7 fn7 inst8 (u with vs_gas_readings := ws) /\
      ~in_revert_forward fn7 u /\ fn8 = dft_fn fn7 /\
      u.vs_current_bb = s8.vs_current_bb /\ ev_reachable orc initial C7 p d fn7 inst8 u) \/
     (in_static_abort_prefix fn8 s8 /\ !p d fn i t. ev_reachable orc initial C7 p d fn i t ==>
       ?ws. raw_reachable v7 C7 fn i (t with vs_gas_readings := ws))) /\
    ev_reachable orc initial C8 p d fn8 inst8 (s8 with vs_gas_readings := initial.vs_gas_readings)) /\
  ((inst9.inst_opcode <> INVOKE /\
     ?post. step_inst 0 C9 inst9 s9 = Halt post \/
            ?a. step_inst 0 C9 inst9 s9 = Abort a post) \/
   (~source_memory_reads_disjoint cpl inst9 s9 \/
    ~context_source_memory_writes_disjoint cpl inst9 s9) \/
   (guarded /\ ?dst x sz src off.
     inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
     code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
     FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off /\
     ~(w2n (src - n2w off) < dimword (:256) DIV 2))) ==>
  (inv_memory_observation inst9.inst_opcode /\ in_static_abort_prefix fn8 s8 /\
   !p d fn i t. ev_reachable orc initial C7 p d fn i t ==>
     ?ws. raw_reachable v7 C7 fn i (t with vs_gas_readings := ws)) \/
  (source_memory_reads_disjoint cpl inst9 s9 /\
   context_source_memory_writes_disjoint cpl inst9 s9 /\ inst9.inst_opcode <> INVOKE /\
   ?post. step_inst 0 C9 inst9 s9 = Halt post \/
          ?a. step_inst 0 C9 inst9 s9 = Abort a post)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `inst_mem_ranges inst9 s9 <> [] \/
    ?x. inst9.inst_opcode = CODECOPY /\ MEM (Var x) inst9.inst_operands /\ code_end_var fn9 x`
  >- (drule_all request_cut_stopped_observation >> strip_tac >>
      qpat_x_assum `inv_memory_observation _ /\ ~in_revert_forward _ _ ==> _`
        (drule_all_then strip_assume_tac)
      >- suspend "paired" >>
      disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `source_memory_reads_disjoint cpl inst9 s9 /\
   context_source_memory_writes_disjoint cpl inst9 s9` by
    (irule request_cut_cfg_disjoint_guard >> metis_tac[]) >>
  disj2_tac >> simp[] >> metis_tac[MEM]
QED

Resume request_cut_frontier_guards[paired]:
  `source_memory_reads_disjoint cpl inst9 s9 /\
   context_source_memory_writes_disjoint cpl inst9 s9` by
    (mp_tac request_cut_retained_memory_guard >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
     disch_then ACCEPT_TAC) >>
  disj2_tac >> simp[] >>
  qpat_x_assum `(inst9.inst_opcode <> INVOKE /\ _) \/ _` mp_tac >> simp[] >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC strip_assume_tac) >>
  mp_tac request_cut_retained_code_end >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  simp[]
QED

Finalise request_cut_frontier_guards
