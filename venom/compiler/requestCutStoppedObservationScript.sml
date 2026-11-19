Theory requestCutStoppedObservation
Ancestors
  requestCutCfgFrontierGuard requestCutCfgCodeEnd dftGasInvMemoryObservation
  dftGasInvCrossingProbe dftGasFromListLookup stepWriteFootprintBase
  concretizeLayoutLocalReturn o1ContractCfgNormJointCursors contextRawReachable contextCodegenRel
  codegenSymRel unitMemInv frameJointTransition venomInst venomWf
  venomExecSemantics venomState words list

(* Memory checks at the stopped C9 cursor resolve to the selected C8
   instruction, including a CODECOPY whose evaluated range is empty. *)
Theorem request_cut_stopped_observation:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  EVERY wf_function C8.ctx_functions /\ raw_reachable initial C8 fn8 inst8 s8 /\
  inst_shape_ok inst8 /\ ~in_revert_forward fn9 s9 /\
  (inst_mem_ranges inst9 s9 <> [] \/
    (?x. inst9.inst_opcode = CODECOPY /\ MEM (Var x) inst9.inst_operands /\
      code_end_var fn9 x)) ==>
  inv_memory_observation inst8.inst_opcode /\
  inv_memory_observation inst9.inst_opcode /\ ~in_revert_forward fn8 s8
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `inst_mem_ranges inst9 s9 <> [] \/ _`
    (DISJ_CASES_THEN strip_assume_tac)
  >- (drule_all request_cut_cfg_guard_projection >> strip_tac >>
      `inv_memory_observation inst8.inst_opcode` by
        metis_tac[inv_memory_observation_covers_ranges] >>
      metis_tac[]) >>
  drule_all request_cut_cfg_codecopy >> strip_tac >>
  `wf_function fn8 /\ active_inst fn8 inst8 s8` by
    metis_tac[raw_reachable_wf, raw_reachable_active] >>
  `ALL_DISTINCT (fn_labels fn8)` by fs[wf_function_def] >>
  `~in_revert_forward fn8 s8` by
    (irule active_inst_not_revert_forward >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `inst8` >> fs[]) >>
  fs[inv_memory_observation_def]
QED
