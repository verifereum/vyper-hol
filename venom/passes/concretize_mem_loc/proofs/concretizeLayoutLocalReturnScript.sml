Theory concretizeLayoutLocalReturn
Ancestors concretizeLayoutHaltExit concretizeLayoutSupplement frameRelocationLocal codegenRel
  ptrDiscipline venomExecSemantics venomState list rich_list pred_set
  concretizeLayoutLocalSha3 concretizeLayoutAccessGeometry
  frameRelocationCleanOperands frameRelocationReachableSupport frameResolvedTrace
  frameOriginReachable frameOriginHistory frameActivationLookup frameActivationLifetime
  frameJointTrace frameJointTransition frameRelocationGuardedValues
  frameRelocationBinding frameJointDemand o1PassContract unitMemInv memLocDefs finite_map
  pointerConfinedDefs contextCodegenRel frameRelocationDemand memSafeRun venomExecProofs
  venomInst venomWf

Theorem return_execution_envelope:
  inst.inst_opcode = RETURN /\ step_inst_base inst s = Halt post ==>
  ?opd opn off sz.
    inst.inst_operands = [opd;opn] /\
    eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
    post = halt_state (set_returndata
      (TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w)) s)
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = Halt post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

(* Return payloads need agreement only outside their source memory taint. *)
Theorem concretize_return_payload:
  inst.inst_opcode = RETURN /\ inst.inst_operands = [opd;opn] /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
  (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
    codegenRel$read_byte (w2n off+i) s.vs_memory =
    codegenRel$read_byte (w2n offT+i) t.vs_memory) ==>
  ?post post'. step_inst_base inst s = Halt post /\
    step_inst_base inst t = Halt post' /\
    LENGTH post.vs_returndata = LENGTH post'.vs_returndata /\
    (!i. i < LENGTH post.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
      EL i post.vs_returndata = EL i post'.vs_returndata)
Proof
  strip_tac >>
  qexistsl_tac [
    `halt_state (set_returndata (TAKE (w2n sz)
       (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w)) s)`,
    `halt_state (set_returndata (TAKE (w2n sz)
       (DROP (w2n offT) t.vs_memory ++ REPLICATE (w2n sz) 0w)) t)`] >>
  simp[step_inst_base_def, halt_state_def, set_returndata_def,
       LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP, ret_taint_def] >>
  qx_gen_tac `j` >> strip_tac >>
  `codegenRel$read_byte (w2n off+j) s.vs_memory =
   codegenRel$read_byte (w2n offT+j) t.vs_memory` by metis_tac[arithmeticTheory.ADD_COMM] >>
  fs[codegenRelTheory.read_byte_def] >> simp[EL_TAKE] >>
  Cases_on `w2n off+j < LENGTH s.vs_memory` >>
  Cases_on `w2n offT+j < LENGTH t.vs_memory` >>
  gvs[EL_APPEND1, EL_APPEND2, LENGTH_DROP, EL_DROP, EL_REPLICATE] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[]
QED

Theorem concretize_return_observation:
  inst.inst_opcode = RETURN /\ step_inst_base inst s = Halt post /\
  inst.inst_operands = [opd;opn] /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
  (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
    codegenRel$read_byte (w2n off+i) s.vs_memory =
    codegenRel$read_byte (w2n offT+i) t.vs_memory) /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  taint_within D C vs0 /\
  frame_reachable vs0 C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  ?post'. step_inst_base inst t = Halt post' /\
    dead_result_rel D (Halt post) (Halt post')
Proof
  strip_tac >>
  `final_taint vs0 C post (step_taint inst s post tn) (ret_taint tn inst s)` by
    (simp[final_taint_def] >>
     goal_assum (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
     simp[step_inst_def] >> qexists_tac `0` >> simp[]) >>
  drule_all return_execution_envelope >> strip_tac >> gvs[] >>
  drule_all (SRULE[arithmeticTheory.ADD_COMM] concretize_return_payload) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst t = Halt _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[] >> strip_tac >> gvs[] >>
  irule concretize_supplement_halt_exit >>
  gvs[halt_state_def, set_returndata_def] >>
  `s.vs_logs = t.vs_logs /\
   s.vs_pending_deletions = t.vs_pending_deletions` by
    gvs[concretize_local_obs_def, dead_result_rel_def] >>
  simp[] >>
  goal_assum (drule_at (Pat `final_taint _ _ _ _ _`)) >> simp[] >>
  gvs[concretize_supplement_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def, halt_state_def, set_returndata_def]
QED

Theorem active_inst_not_revert_forward:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
  ~MEM inst.inst_opcode [RETURNDATACOPY; REVERT] ==>
  ~in_revert_forward fn s
Proof
  rw[in_revert_forward_def] >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (fs[active_inst_def, fn_labels_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> simp[]) >>
     gvs[get_instruction_def]) >>
  strip_tac >> drule_all revert_forward_at_opcode >> simp[]
QED

Theorem concretize_return_read_agreement:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) Obs s t /\
  inst.inst_opcode = RETURN /\ inst.inst_operands = [opd;opn] /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz ==>
  ?offT. eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
    (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
      codegenRel$read_byte (w2n off+i) s.vs_memory =
      codegenRel$read_byte (w2n offT+i) t.vs_memory)
Proof
  strip_tac >>
  `~joint_read_exempt (EL c (q0::qs))` by
    (simp[joint_read_exempt_def] >> irule active_inst_not_revert_forward >>
     conj_tac >- fs[o1_fn_shape_def, wf_function_def] >>
     qexists_tac `inst` >> simp[]) >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_trace_def, joint_chain_length] >>
  `joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h)` by
    (drule joint_trace_prefix_reachable >> rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `c` mp_tac) >> simp[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `eval_operand opn s = eval_operand opn t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
     disch_then irule >> simp[] >>
     conj_tac >- (rpt strip_tac >> spose_not_then assume_tac >>
       `v IN fn_pv P fn` by metis_tac[] >>
       `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
       gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
           mem_write_ops_def, mem_read_ops_def] >>
       first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
       Cases_on `opd = Var v` >> gvs[]) >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `inst` >> simp[]) >>
  `eval_operand opn t = SOME sz` by metis_tac[] >>
  `?offT. eval_operand opd t = SOME offT /\
    (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c
        (w2n off+i) (w2n offT+i))` by
    (irule concretize_read_demand_geometry >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def] >> metis_tac[]) >>
  qexists_tac `offT` >> simp[] >> rpt strip_tac >>
  drule local_rel_demand >> simp[demand_agree_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

val _ = export_theory();
