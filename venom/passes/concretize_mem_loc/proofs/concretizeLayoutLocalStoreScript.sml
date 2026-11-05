Theory concretizeLayoutLocalStore
Ancestors concretizeLayoutStoreProduction frameRelocationStoreTaint frameRelocationCopySteps frameRelocationObservations
  frameRelocationGuardedValues frameRelocationGhostCopy frameRelocationLocal
  frameRelocationValues ptrDiscipline venomState frameJointTrace frameJointTransition frameOriginHistory
  frameOriginReachable frameRelocationTaintOrder

Theorem concretize_mstore_local_core:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) Obs s t /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  inst.inst_outputs = [] ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. T) post tpost
Proof
  strip_tac >> drule_all concretize_mstore_demand_execution >>
  strip_tac >> qexists_tac `tpost` >> simp[] >>
  qpat_x_assum `local_rel _ _ _ _ _ s t` mp_tac >>
  qpat_x_assum `demand_agree _ _ _` mp_tac >>
  simp[local_rel_def, variable_domains_def, variables_agree_on_def,
       local_values_def, lookup_var_def, mstore_def, write_memory_with_expansion_def,
       guarded_bytes_def, copy_bytes_def, op_taint_def, step_taint_def,
       set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV]
QED

val _ = if null (hyp concretize_mstore_local_core) then ()
        else raise Fail "store local core export has hypotheses";

(* The restored-memory equalities preserve every non-memory field on each
   side individually, hence preserve all incoming control/GAS equalities. *)
Theorem concretize_mstore_local_observed:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  inst.inst_outputs = [] ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    (post with vs_memory := s.vs_memory) = s /\
    (tpost with vs_memory := t.vs_memory) = t
Proof
  strip_tac >>
  drule_all concretize_mstore_local_core >> strip_tac >>
  drule_all concretize_mstore_demand_execution >> strip_tac >>
  qexists_tac `tpost` >>
  gvs[] >> simp[mstore_memory_frame] >>
  qpat_x_assum `local_rel _ _ _ _ (\s t. T) _ _` mp_tac >>
  drule local_rel_observation >>
  simp[local_rel_def, dead_result_rel_mstore]
QED

val _ = if null (hyp concretize_mstore_local_observed) then ()
        else raise Fail "observed store export has hypotheses";

Theorem concretize_mstore_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  inst.inst_outputs = [] /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    (post with vs_memory := s.vs_memory) = s /\
    (tpost with vs_memory := t.vs_memory) = t /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un)
Proof
  strip_tac >>
  drule_all concretize_mstore_local_observed >> strip_tac >>
  drule_all concretize_mstore_execution_geometry >> strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >>
     gvs[] >> fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `op_taint un opv SUBSET {k:num | k < 32}` by
    (irule relocation_reachable_operand_taint_bounded >> metis_tac[]) >>
  qexists_tac `tpost` >> gvs[] >>
  irule relocation_taint_le_mstore >> simp[] >>
  goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  metis_tac[]
QED

val _ = if null (hyp concretize_mstore_local_complete) then ()
        else raise Fail "complete store export has hypotheses";
