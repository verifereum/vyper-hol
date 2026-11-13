Theory concretizeLayoutLocalValues
Ancestors concretizeLayoutOperandCleanliness
  frameRelocationCleanValueSteps frameRelocationEnvironment
  frameRelocationCleanOperands frameRelocationReachableSupport
  frameRelocationOpaque frameOriginUpdates
  concretizeLayoutLoadProduction pointerConfinedDefs memLocDefs
  frameRelocationBinding frameJointDemand frameJointTrace frameJointTransition
  frameResolvedTrace frameJointTaint frameOriginReachable frameOriginHistory
  ptrDiscipline codegenRel finite_map pred_set list

Theorem nonpointer_clean_classification[local]:
  clean_value_shape inst /\ ~MEM inst.inst_opcode [ADD; SUB; EQ; LT; GT; MUL] ==>
  ~is_pointer_preserving_op inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  ~MEM inst.inst_opcode [LT; GT; EQ] /\
  mem_write_ops inst = NONE /\ mem_read_ops inst = NONE /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]
Proof
  simp[clean_value_shape_def, frameRelocationScalarStepsTheory.scalar_binary_opcode_def, MEM] >> strip_tac >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def]
QED

Theorem nonpointer_clean_no_writes[local]:
  clean_value_shape inst /\ ~MEM inst.inst_opcode [ADD; SUB; EQ; LT; GT] ==>
  step_writes inst s post = []
Proof
  simp[clean_value_shape_def, frameRelocationScalarStepsTheory.scalar_binary_opcode_def, MEM] >> strip_tac >>
  simp[step_writes_def, source_memory_write_ranges_def]
QED

Theorem concretize_clean_value_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  clean_value_shape inst /\ ~MEM inst.inst_opcode [ADD; SUB; EQ; LT; GT] /\
  inst.inst_outputs = [v] /\ step_inst_base inst s = OK post /\
  relocation_env s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
     fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = MUL` >- suspend "mul" >>
  `!w. MEM (Var w) inst.inst_operands ==>
       clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >>
     `~MEM inst.inst_opcode [ADD; SUB; EQ; LT; GT; MUL]` by fs[] >>
     drule_all nonpointer_clean_classification >> strip_tac >>
     `~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]` by fs[] >>
     drule_all nonpointer_operand_clean >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, nonpointer_clean_no_writes, range_bytes_def] >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_all guarded_clean_value_step >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexists_tac `update_var v z t` >> simp[] >>
  gvs[] >> irule relocation_env_update_var >> simp[]
QED

Resume concretize_clean_value_local_complete[mul]:
  `?a b. inst.inst_operands = [a;b]` by
    gvs[clean_value_shape_def, frameRelocationScalarStepsTheory.scalar_binary_opcode_def,
        LENGTH_EQ_NUM_compute] >>
  `!w. MEM (Var w) inst.inst_operands ==>
    FLOOKUP rv w = NONE /\ ~retpc_var fn w` by
    (gen_tac >> strip_tac >> conj_tac
     >- (spose_not_then assume_tac >>
         `w IN fn_pv P fn` by metis_tac[] >>
         `ptr_use_ok P (fn_pv P fn) inst` by
           (fs[fn_ptr_ok_def] >> metis_tac[]) >>
         fs[ptr_use_ok_def] >>
         qpat_x_assum `!v. MEM (Var v) _ /\ _ ==> _`
           (qspec_then `w` mp_tac) >>
         simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
     strip_tac >> drule_all disciplined_retpc_operand_use >> gvs[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
    joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, nonpointer_clean_no_writes, range_bytes_def] >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_all guarded_selector_mul_execution >> strip_tac >>
  `step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,out_taint tn inst s)` by
    (irule frameRelocationScalarStepsTheory.scalar_binary_update_taint >>
     simp[frameRelocationScalarStepsTheory.scalar_binary_opcode_def]) >>
  `step_taint inst t (update_var v y t) un =
    un with t_var := un.t_var |+ (v,out_taint un inst t)` by
    (irule frameRelocationScalarStepsTheory.scalar_binary_update_taint >>
     simp[frameRelocationScalarStepsTheory.scalar_binary_opcode_def]) >>
  qexists_tac `update_var v y t` >> simp[] >> gvs[] >> conj_tac
  >- (irule guarded_masked_write_restrict >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
            fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
      gen_tac >> IF_CASES_TAC >> simp[]) >>
  conj_tac
  >- (irule relocation_masked_write_taint >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[relocation_env_update_var]
QED

Finalise concretize_clean_value_local_complete
