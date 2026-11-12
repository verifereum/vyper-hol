(* Concrete compatible caller for the context-generalized simulation. *)
Theory targetPureWalkCallerProbe
Ancestors
  targetPureWalkSimulationProbe exprLoweringProps compileEnv exprLowering
  venomInst venomWf venomExecSemantics fragExec loweringShapeDefs fcgDefs
  list finite_map relation pred_set

Definition simulation_probe_start_def:
  simulation_probe_start =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "caller"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Definition simulation_probe_finish_def:
  simulation_probe_finish = SND (compile_get_target_ptr compile_expr
    simulation_probe_cenv module_probe_target simulation_probe_start)
End

Definition simulation_probe_op_def:
  simulation_probe_op = FST (compile_get_target_ptr compile_expr
    simulation_probe_cenv module_probe_target simulation_probe_start)
End

Definition simulation_probe_caller_def:
  simulation_probe_caller = mk_raw_function "caller"
    (all_blocks simulation_probe_finish)
End

Theorem simulation_probe_compilation:
  compile_get_target_ptr compile_expr simulation_probe_cenv
    module_probe_target simulation_probe_start =
    (simulation_probe_op, simulation_probe_finish)
Proof
  simp[simulation_probe_op_def, simulation_probe_finish_def]
QED

Theorem simulation_probe_finish_code:
  simulation_probe_finish.cs_current_bb = "caller"
Proof
  rewrite_tac[simulation_probe_finish_def, simulation_probe_compile_target] >>
  EVAL_TAC
QED

Theorem simulation_probe_caller_has_code:
  fn_has_code simulation_probe_start simulation_probe_finish simulation_probe_caller
Proof
  rewrite_tac[fn_has_code_def, simulation_probe_caller_def,
    simulation_probe_finish_def, simulation_probe_compile_target,
    simulation_probe_start_def] >>
  EVAL_TAC >> simp[]
QED

Theorem simulation_probe_caller_name:
  simulation_probe_caller.fn_name = "caller" /\
  simulation_probe_caller.fn_name <> simulation_probe_label
Proof
  EVAL_TAC
QED

Theorem simulation_probe_caller_distinct:
  fn_inst_ids_distinct simulation_probe_caller
Proof
  rewrite_tac[fn_inst_ids_distinct_def, simulation_probe_caller_def,
    simulation_probe_finish_def, simulation_probe_compile_target] >> EVAL_TAC
QED

Theorem simulation_probe_caller_lookup:
  lookup_function "caller"
    (simulation_probe_context_with_caller simulation_probe_caller).ctx_functions =
    SOME simulation_probe_caller
Proof
  mp_tac (Q.SPEC `simulation_probe_caller`
    simulation_probe_context_with_caller_lookup) >>
  simp[simulation_probe_caller_name]
QED

Theorem simulation_probe_caller_direct_calls:
  !a b. fn_directly_calls
    (simulation_probe_context_with_caller simulation_probe_caller) a b <=>
    a = "caller" /\ b = simulation_probe_label
Proof
  rewrite_tac[fn_directly_calls_def, simulation_probe_context_with_caller_def,
    simulation_probe_caller_def, simulation_probe_finish_def,
    simulation_probe_compile_target] >>
  simp[mk_venom_context_def, lookup_function_def, FIND_thm,
       mk_raw_function_def, all_blocks_def, simulation_probe_callee_def,
       simulation_probe_label_def] >>
  rpt gen_tac >> Cases_on `a = "caller"` >>
  simp[] >> EVAL_TAC >>
  dsimp[] >> rpt strip_tac >> gvs[]
QED

Theorem simulation_probe_caller_reachable:
  !a b. TC (fn_directly_calls
    (simulation_probe_context_with_caller simulation_probe_caller)) a b <=>
    a = "caller" /\ b = simulation_probe_label
Proof
  `transitive (fn_directly_calls
     (simulation_probe_context_with_caller simulation_probe_caller))` by
    simp[transitive_def, simulation_probe_caller_direct_calls,
         simulation_probe_label_def, internal_fn_label_def] >>
  drule transitive_TC_identity >>
  simp[simulation_probe_caller_direct_calls]
QED

Theorem simulation_probe_caller_zero_allocations:
  (!s. pending_alloca_size simulation_probe_caller s = 0) /\
  unit_alloca_frame
    (simulation_probe_context_with_caller simulation_probe_caller) = 0
Proof
  rewrite_tac[pending_alloca_size_def, unit_alloca_frame_def,
    simulation_probe_context_with_caller_def, simulation_probe_caller_def,
    simulation_probe_finish_def, simulation_probe_compile_target] >>
  EVAL_TAC >> simp[]
QED

Theorem simulation_probe_caller_alloca_room:
  !s. s.vs_alloca_next < dimword (:256) ==>
    alloca_room (simulation_probe_context_with_caller simulation_probe_caller)
      simulation_probe_caller s
Proof
  simp[alloca_room_def, simulation_probe_caller_name,
       simulation_probe_caller_lookup, simulation_probe_caller_reachable,
       simulation_probe_caller_zero_allocations, simulation_probe_label_def,
       internal_fn_label_def]
QED

Theorem simulation_probe_caller_no_dynamic_allocations:
  ~EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts simulation_probe_caller) /\
  ~EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts simulation_probe_callee)
Proof
  rewrite_tac[simulation_probe_caller_def, simulation_probe_finish_def,
    simulation_probe_compile_target] >> EVAL_TAC
QED

Theorem simulation_probe_caller_fmp_room:
  !s. fmp_room (simulation_probe_context_with_caller simulation_probe_caller)
    simulation_probe_caller s
Proof
  simp[fmp_room_def, simulation_probe_caller_no_dynamic_allocations,
       simulation_probe_caller_reachable,
       simulation_probe_context_with_caller_def, mk_venom_context_def,
       simulation_probe_caller_name] >>
  rpt strip_tac >> gvs[simulation_probe_caller_name,
    simulation_probe_caller_no_dynamic_allocations]
QED

Theorem simulation_probe_concrete_op:
  simulation_probe_op =
    (Var "%5", SOME LocMemory, SOME (ValPT (BaseT (UintT 256))))
Proof
  rewrite_tac[simulation_probe_op_def, simulation_probe_compile_target] >> EVAL_TAC
QED

Theorem simulation_probe_concrete_endpoint:
  simulation_probe_finish.cs_current_bb = simulation_probe_start.cs_current_bb /\
  LENGTH simulation_probe_finish.cs_current_insts = 8 /\
  simulation_probe_finish.cs_next_var = 6 /\
  simulation_probe_finish.cs_next_id = 8 /\
  simulation_probe_finish.cs_blocks = []
Proof
  rewrite_tac[simulation_probe_finish_def, simulation_probe_compile_target] >> EVAL_TAC
QED
