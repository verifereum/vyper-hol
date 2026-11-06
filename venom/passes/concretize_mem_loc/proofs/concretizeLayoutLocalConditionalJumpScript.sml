Theory concretizeLayoutLocalConditionalJump
Ancestors concretizeLayoutLocalJump concretizeLayoutLocalOffset
  frameRelocationValues frameRelocationLocal frameRelocationDemand
  frameRelocationTaintOrder frameRelocationCopyTaint frameRelocationMemory concretizeLayoutReaderContext
  frameRelocationEnvironment frameRelocationBinding frameJointDemand frameJointTrace
  frameJointTransition frameResolvedTrace frameJointTaint frameOriginUpdates
  frameRelocationCleanOperands frameRelocationReachableSupport frameRelocationGuardedValues
  concretizeLayoutOperandCleanliness concretizeLayoutLoadProduction
  pointerConfinedDefs memLocDefs frameOriginReachable frameOriginHistory
  ptrDiscipline venomExecSemantics venomState venomWf codegenRel finite_map pred_set list

Theorem conditional_jump_execution:
  MEM inst.inst_opcode [JNZ; DJMP] /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst_base inst s = OK post ==>
  ?lbl. post = jump_to lbl s /\ step_inst_base inst t = OK (jump_to lbl t)
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[AllCaseEqs()] >> metis_tac[MEM]
QED

Theorem conditional_jump_ghosts[local]:
  MEM inst.inst_opcode [JNZ; DJMP] /\ inst.inst_outputs = [] ==>
  step_prov PG G inst (jump_to lbl s) = G /\
  step_taint inst s (jump_to lbl s) tn = tn /\
  step_writes inst s (jump_to lbl s) = []
Proof
  simp[MEM] >> strip_tac >>
  `new_site_bytes s (jump_to lbl s) = {}` by
    (irule new_site_bytes_unchanged >> simp[jump_to_def]) >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, store_taint_def, adopt_reset_def,
       imm_taint_def, out_taint_def, set_var_taint_def, taint_component_equality] >>
  rpt CASE_TAC >> simp[fmap_eq_flookup, FLOOKUP_DRESTRICT]
QED

Theorem conditional_jump_operands:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM inst.inst_opcode [JNZ; DJMP] /\
  relocation_env s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  !op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!w. MEM (Var w) inst.inst_operands ==> clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >>
     `~is_pointer_preserving_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
      ~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
      mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
       (gvs[MEM] >> simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]) >>
     drule_all nonpointer_operand_clean >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_operand >>
  disch_then (qspec_then `op` mp_tac) >>
  gvs[relocation_env_def] >> metis_tac[]
QED

Theorem concretize_conditional_jump_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\
  MEM inst (fn_insts fn) /\ MEM inst.inst_opcode [JNZ; DJMP] /\
  step_inst_base inst s = OK post /\ s.vs_current_bb = t.vs_current_bb /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?t'. step_inst_base inst t = OK t' /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post t' /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t t' un) /\
    relocation_env post t' /\ relocation_reader_context post t' /\
    post.vs_current_bb = t'.vs_current_bb /\
    post.vs_prev_bb = t'.vs_prev_bb /\ post.vs_inst_idx = t'.vs_inst_idx /\
    step_taint inst s post tn = tn /\ step_taint inst t t' un = un
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
     fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t` by
    (metis_tac[conditional_jump_operands]) >>
  `inst_wf inst` by
    (fs[o1PassContractTheory.o1_fn_shape_def, fn_inst_wf_def,
        venomInstTheory.fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >> gvs[MEM] >>
     simp[inst_wf_def, venomInstTheory.opcode_case_def] >> metis_tac[]) >>
  drule_all conditional_jump_execution >> strip_tac >> gvs[] >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, conditional_jump_ghosts, range_bytes_def] >> metis_tac[]) >>
  simp[conditional_jump_ghosts] >> (conj_tac
  >- (irule local_rel_jump_to >> fs[local_rel_def, demand_agree_def] >> metis_tac[])) >>
  (conj_tac
  >- (fs[relocation_taint_le_def, demand_taint_def] >> metis_tac[])) >>
  fs[relocation_env_def, relocation_reader_context_def, jump_to_def]
QED

val _ = if null (hyp concretize_conditional_jump_local_complete) then ()
        else raise Fail "conditional jump export has hypotheses";
val _ = export_theory();
