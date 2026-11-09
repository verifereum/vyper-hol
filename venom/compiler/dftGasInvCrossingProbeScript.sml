Theory dftGasInvCrossingProbe
Ancestors
  dftRunRel dftScheduleOrder venomEffects venomInst dftGasInvCallBoundary
  unitShapeDefs unitMemInv venomWf dftGasOracleDefs venomExecSemantics
  contextCodegenRel codegenRel list

(* Syntactic cases, not the state-dependent nonempty-range predicate. *)
Definition inv_memory_observation_def:
  inv_memory_observation opc <=>
    MEM opc [MLOAD; ILOAD; MSTORE; MSTORE8; ISTORE; MCOPY;
      CALLDATACOPY; RETURNDATACOPY; DLOADBYTES; CODECOPY; EXTCODECOPY;
      DRET; RETURN; REVERT; SHA3; LOG; CALL; STATICCALL; INVOKE]
End

(* Exact state-free obstruction, leaving SSA uses and output arity explicit. *)
Definition inv_crossing_candidate_def:
  inv_crossing_candidate opc obs outputs_empty <=>
    DISJOINT (write_effects opc) (read_effects obs UNION write_effects obs) /\
    DISJOINT (read_effects opc) (write_effects obs) /\
    ~(outputs_empty /\ read_effects opc = empty_effects /\
      write_effects opc = empty_effects) /\ ~is_terminator obs
End

Theorem inv_crossing_candidate_necessary:
  ~dft_must_order x y ==>
  inv_crossing_candidate x.inst_opcode y.inst_opcode (x.inst_outputs = [])
Proof
  simp[dft_must_order_def, inv_crossing_candidate_def] >> metis_tac[]
QED

(* Exhaustive relevant-observation table for the potentially nonreturning
   predecessor; no callee-termination assumption is hidden here. *)
Theorem inv_invoke_cannot_cross_memory:
  inv_memory_observation obs ==>
  ~inv_crossing_candidate INVOKE obs outputs_empty
Proof
  simp[inv_memory_observation_def] >> rpt strip_tac >>
  gvs[inv_crossing_candidate_def, read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def, is_terminator_def]
QED

Theorem inv_output_free_barriers:
  MEM opc [ASSERT; ASSERT_UNREACHABLE; INVALID] ==>
  ~inv_crossing_candidate opc obs T
Proof
  simp[] >> rpt strip_tac >>
  gvs[inv_crossing_candidate_def, read_effects_def, write_effects_def]
QED

Theorem inv_shape_excludes_runtime_errors:
  inst_shape_ok inst ==> ~dft_swap_runtime_error_opcode inst.inst_opcode
Proof
  simp[inst_shape_ok_def, dft_swap_runtime_error_opcode_def] >> metis_tac[]
QED

(* These survivors show why NoFail alone is not the whole table. *)
Theorem inv_exceptional_crossing_survivors:
  inv_crossing_candidate SSTORE MLOAD T /\
  inv_crossing_candidate TSTORE MLOAD T /\
  inv_crossing_candidate ALLOCA MLOAD F /\
  ~inv_crossing_candidate RETURNDATACOPY MLOAD T /\
  ~inv_crossing_candidate RETURNDATACOPY MSTORE T /\
  inv_crossing_candidate LOG MLOAD T
Proof
  EVAL_TAC
QED

Theorem inv_fallible_crossing_classification:
  inst_wf x /\ inst_shape_ok x /\
  inv_memory_observation obs /\
  inv_crossing_candidate x.inst_opcode obs (x.inst_outputs = []) ==>
  opcode_fail_class x.inst_opcode = NoFail \/
  MEM x.inst_opcode [SSTORE; TSTORE; LOG]
Proof
  strip_tac >>
  `x.inst_opcode <> INVOKE` by metis_tac[inv_invoke_cannot_cross_memory] >>
  Cases_on `x.inst_opcode` >> gvs[opcode_fail_class_def] >>
  gvs[inst_shape_ok_def] >>
  gvs[inst_wf_def] >>
  gvs[inv_crossing_candidate_def, read_effects_def, write_effects_def,
      empty_effects_def] >>
  gvs[inv_memory_observation_def, read_effects_def, write_effects_def,
      all_effects_def, is_terminator_def]
QED

Theorem inv_oracle_nofail_total:
  inst_wf inst /\ ~is_pseudo inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> ALLOCA /\
  opcode_fail_class inst.inst_opcode = NoFail /\
  ~dft_swap_runtime_error_opcode inst.inst_opcode /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. ev_step orc p d fuel ctx inst s = OK t
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      simp[ev_step_def, ev_gas_def]) >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[opcode_fail_class_def]) >>
  drule_all dft_swap_guarded_nofail_total >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  simp[ev_step_def, step_inst_non_invoke]
QED

Theorem inv_oracle_alloca_total:
  inst_wf inst /\ inst.inst_opcode = ALLOCA ==>
  ?t. ev_step orc p d fuel ctx inst s = OK t
Proof
  strip_tac >> gvs[inst_wf_def] >>
  simp[ev_step_def, Once step_inst_base_def, exec_alloca_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> simp[] >>
  rename1 `FLOOKUP _ _ = SOME allocation` >>
  PairCases_on `allocation` >> simp[]
QED

Theorem inv_static_class_no_abort:
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\
  ~s.vs_call_ctx.cc_static ==>
  step_inst fuel ctx inst s <> Abort a t
Proof
  simp[] >> rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  gvs[Once step_inst_base_def, AllCaseEqs(), exec_write2_def]
QED

Theorem inv_oracle_static_class_total:
  inst_wf inst /\ MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\
  ~s.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. ev_step orc p d fuel ctx inst s = OK t
Proof
  strip_tac >>
  `opcode_fail_class inst.inst_opcode = CanExHalt /\
   ~is_terminator inst.inst_opcode /\
   ~dft_swap_runtime_error_opcode inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (gvs[opcode_fail_class_def, is_terminator_def,
         dft_swap_runtime_error_opcode_def]) >>
  drule_all dft_swap_canexhalt_operand_defined >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  strip_tac
  >- gvs[ev_step_def, step_inst_non_invoke] >>
  metis_tac[inv_static_class_no_abort]
QED

Theorem inv_memory_observation_covers_ranges:
  inst_shape_ok inst /\ ~inv_memory_observation inst.inst_opcode ==>
  inst_mem_ranges inst s = []
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[inst_shape_ok_def, inv_memory_observation_def] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem inv_crossed_predecessor_total:
  inst_wf x /\ inst_shape_ok x /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  inv_memory_observation y.inst_opcode /\ ~dft_must_order x y /\
  ~s.vs_call_ctx.cc_static /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. ev_step orc p d fuel ctx x s = OK t
Proof
  strip_tac >>
  drule inv_crossing_candidate_necessary >> strip_tac >>
  drule_all inv_fallible_crossing_classification >> strip_tac
  >- (Cases_on `x.inst_opcode = ALLOCA`
      >- metis_tac[inv_oracle_alloca_total] >>
      drule inv_shape_excludes_runtime_errors >> strip_tac >>
      irule inv_oracle_nofail_total >> simp[]) >>
  irule inv_oracle_static_class_total >> simp[]
QED
