(* Permanent focused checks of the unit-transform boundary.
 * No S4-S6 admission is used to prove a regression check.
 *)
Theory unitTransformChecks
Ancestors
  unitTransformDefs contextCodegenRel contextCodegenRelProps codegenRel
  venomInst venomState venomExecSemantics passSimulationDefs stateEquiv
  observableOracle finite_map words list
Libs
  wordsLib

(* ===== Result cases and intentional asymmetry ===== *)

Theorem unit_result_success_requests_check:
  ~unit_result_rel (Halt (s with vs_requests := []))
                   (Halt (s with vs_requests := [request])) /\
  unit_result_rel (Halt (s with vs_outcomes := []))
                  (Halt (s with vs_outcomes := [outcome]))
Proof
  simp[unit_result_rel_def, observable_request_counterexample,
       observable_outcome_counterexample]
QED

(* Successful results retain all eight observable fields, including deletions. *)
Theorem unit_result_success_observables_check:
  unit_result_rel (Halt s) (Halt s') <=>
  s.vs_accounts = s'.vs_accounts /\ s.vs_returndata = s'.vs_returndata /\
  s.vs_halted = s'.vs_halted /\ s.vs_logs = s'.vs_logs /\
  s.vs_transient = s'.vs_transient /\ s.vs_immutables = s'.vs_immutables /\
  s.vs_requests = s'.vs_requests /\
  s.vs_pending_deletions = s'.vs_pending_deletions
Proof
  simp[unit_result_rel_def, observable_equiv_def]
QED

(* Includes unrelated states, different returndata and different requests. *)
Theorem unit_result_abort_weakening_check:
  unit_result_rel (Abort Revert_abort s) (Abort Revert_abort s') /\
  ~unit_result_rel (Abort Revert_abort s) (Abort ExHalt_abort s') /\
  unit_result_rel (Abort ExHalt_abort s) (Abort Revert_abort s') /\
  unit_result_rel (Abort ExHalt_abort s) (Abort ExHalt_abort s') /\
  ~unit_result_rel (Halt s) (Abort Revert_abort s') /\
  ~unit_result_rel (Abort ExHalt_abort s) (Halt s')
Proof
  simp[unit_result_rel_def]
QED

Theorem unit_result_rejects_nonterminal_check:
  ~unit_result_rel (OK s) res /\ ~unit_result_rel res (OK s) /\
  ~unit_result_rel (IntRet vals s) res /\ ~unit_result_rel res (IntRet vals s) /\
  ~unit_result_rel (Error err) res /\ ~unit_result_rel res (Error err)
Proof
  simp[unit_result_rel_nonterminal]
QED

(* Missing entry: the raw run is always Error, so forward correctness imposes
 * NO requirement on the output. This is not a bidirectional pass contract. *)
Theorem ctx_transform_forward_vacuity_check:
  ctx.ctx_entry = NONE ==> ctx_transform_correct ctx ctx' s
Proof
  simp[ctx_transform_correct_def, run_context_def, terminates_def]
QED

Theorem checked_unit_pipeline_failure_check:
  pipeline rpolicy unit = NONE ==>
  ~checked_unit_transform_correct pipeline rpolicy unit s
Proof
  simp[checked_unit_transform_correct_def]
QED

(* ===== Initial-state boundary ===== *)

(* Outcomes, requests and initial FMP are unrestricted by this allocation
 * predicate; the two executions still share the same whole initial state. *)
Theorem o1_initial_state_oracle_fmp_check:
  o1_initial_state_ok
    (s with <| vs_outcomes := outcomes; vs_requests := requests;
               vs_initial_fmp := fmp |>) <=> o1_initial_state_ok s
Proof
  simp[o1_initial_state_ok_def]
QED

Theorem o1_initial_state_reset_check:
  o1_initial_state_ok
    (s with <| vs_vars := FEMPTY; vs_halted := F; vs_memory := [];
               vs_allocas := FEMPTY; vs_alloca_next := 0 |>) /\
  ~o1_initial_state_ok (s with vs_alloca_next := 1) /\
  ~o1_initial_state_ok (s with vs_halted := T) /\
  ~o1_initial_state_ok (s with vs_memory := [0w])
Proof
  simp[o1_initial_state_ok_def]
QED

(* ===== Exact numeric footprint boundaries ===== *)

Theorem memory_fixed_frontier_checks:
  inst_mem_below_frontier (mk_inst 0 MLOAD [Lit 0w] ["x"])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier (mk_inst 0 MLOAD [Lit 1w] ["x"])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier (mk_inst 0 ILOAD [Lit 0w] ["x"])
    (s with vs_alloca_next := 31) /\
  inst_mem_below_frontier (mk_inst 0 MSTORE [Lit 0w; Lit 1w] [])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier (mk_inst 0 MSTORE8 [Lit 32w; Lit 1w] [])
    (s with vs_alloca_next := 32)
Proof
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       mk_inst_def, eval_operand_def] >> EVAL_TAC
QED

(* A zero-length access is safe even at max word; nonzero endpoints use
 * natural-number addition, not wrapping word addition. LOG uses REVERSE. *)
Theorem memory_sized_frontier_checks:
  inst_mem_below_frontier (mk_inst 0 RETURN [Lit (-1w); Lit 0w] [])
    (s with vs_alloca_next := 0) /\
  ~inst_mem_below_frontier (mk_inst 0 RETURN [Lit (-1w); Lit 1w] [])
    (s with vs_alloca_next := dimword (:256) - 1) /\
  inst_mem_below_frontier (mk_inst 0 LOG [Lit 1w; Lit 9w; Lit 1w; Lit 31w] [])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier (mk_inst 0 LOG [Lit 1w; Lit 9w; Lit 2w; Lit 31w] [])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier (mk_inst 0 MCOPY [Lit 0w; Lit 32w; Lit 1w] [])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier (mk_inst 0 MCOPY [Lit 32w; Lit 0w; Lit 1w] [])
    (s with vs_alloca_next := 32)
Proof
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       memory_range_of_operands_def, mk_inst_def, eval_operand_def,
       eval_operands_def] >> EVAL_TAC
QED

(* Both input reads and output writes count, even if a short outcome will
 * write fewer bytes. These are the existing conservative footprint tables. *)
Theorem memory_call_frontier_checks:
  inst_mem_below_frontier
    (mk_inst 0 CALL [Lit 0w; Lit 1w; Lit 0w; Lit 0w; Lit 32w; Lit 0w; Lit 32w] ["r"])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier
    (mk_inst 0 CALL [Lit 0w; Lit 1w; Lit 0w; Lit 32w; Lit 1w; Lit 0w; Lit 0w] ["r"])
    (s with vs_alloca_next := 32) /\
  ~inst_mem_below_frontier
    (mk_inst 0 STATICCALL [Lit 0w; Lit 1w; Lit 0w; Lit 0w; Lit 32w; Lit 1w] ["r"])
    (s with vs_alloca_next := 32)
Proof
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       mk_inst_def, eval_operand_def] >> EVAL_TAC
QED

(* INVOKE's direct footprint is empty; callee accesses are NOT omitted from
 * raw_unit_memory_ok, whose package includes reachability_closed_callee. *)
Theorem memory_invoke_direct_check:
  inst_mem_below_frontier (mk_inst 0 INVOKE [Label "callee"] []) s
Proof
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def]
QED

Theorem raw_memory_requires_entry_check:
  ctx.ctx_entry = NONE ==> ~raw_unit_memory_ok ctx s
Proof
  simp[raw_unit_memory_ok_def, codegen_reachability_package_def]
QED

(* Regression for the first corrected closure clause: safety applies at the
 * incremented instruction index, not at the unincremented step result. *)
Theorem raw_memory_next_site_check:
  codegen_reachability_package Inv ctx vs /\
  (!fn inst s. Inv ctx fn inst s ==>
    s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s) /\
  Inv ctx fn inst s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
  active_inst fn next (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  inst_mem_below_frontier next (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `reachability_closed Inv ctx` by fs[codegen_reachability_package_def] >>
  drule_all reachability_closed_next >> metis_tac[]
QED

(* Terminator continuation uses the destination's evaluated PHI prefix. *)
Theorem raw_memory_block_site_check:
  codegen_reachability_package Inv ctx vs /\
  (!fn inst s. Inv ctx fn inst s ==>
    s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s) /\
  Inv ctx fn inst s /\ active_inst fn inst s /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
  ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn next s1 ==>
  inst_mem_below_frontier next s1
Proof
  strip_tac >>
  `reachability_closed Inv ctx` by fs[codegen_reachability_package_def] >>
  drule_all reachability_closed_block >> metis_tac[]
QED

(* Callee memory is constrained at its post-PHI entry instruction even though
 * INVOKE itself has no direct read/write footprint. *)
Theorem raw_memory_callee_site_check:
  codegen_reachability_package Inv ctx vs /\
  (!fn inst s. Inv ctx fn inst s ==>
    s.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier inst s) /\
  Inv ctx caller invoke s /\ active_inst caller invoke s /\
  invoke.inst_opcode = INVOKE /\ decode_invoke invoke = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee next s1 ==>
  s1.vs_alloca_next < dimword (:256) /\ inst_mem_below_frontier next s1
Proof
  strip_tac >>
  `reachability_closed Inv ctx` by fs[codegen_reachability_package_def] >>
  drule_all reachability_closed_callee >> strip_tac >>
  drule_all fn_entry_inv_active >> metis_tac[]
QED
