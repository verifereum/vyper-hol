Theory concretizeLayoutLoadProduction
Ancestors concretizeLayoutAccessGeometry frameRelocationWriteCoverage
  concretizeLayoutPointerRanges frameRelocationBinding
  frameRelocationLoadSteps frameRelocationLocal frameJointDemand frameJointTaint
  frameRelocationMemoryAccess frameRelocationMemoryOpaque
  frameRelocationCleanOperands frameJointTrace frameJointTransition frameOriginReachable
  frameOriginHistory memLocDefs finiteByteDemand venomExecSemantics
  frameResolvedTrace frameActivationLookup frameActivationLifetime
  o1PassContract ptrDiscipline unitMemInv contextCodegenRel finite_map list pred_set words


Theorem concretize_word_load_execution_clean_lanes:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
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
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst ==>
  ?dstT tpost. eval_operand opd t = SOME dstT /\
    step_inst_base inst t = OK tpost /\
    tpost = update_var v (mload (w2n dstT) t) t /\
    post = update_var v (mload (w2n dst) s) s /\
    (!i. i < 32 /\ w2n dst+i NOTIN tn.t_mem ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c
        (w2n dst+i) (w2n dstT+i))
Proof
  strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >>
     metis_tac[resolved_frame_erasure]) >>
  `~in_revert_forward fn s` by fs[joint_read_exempt_def] >>
  `post = update_var v (mload (w2n dst) s) s` by
    (fs[MEM] >> qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def, step_inst_base_def, exec_read1_def] >>
     metis_tac[]) >>
  `?dstT. eval_operand opd t = SOME dstT /\
    ((w2n dst+32 <= lo /\ w2n dstT = w2n dst) \/
     (?d owner aid b sz.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,sz) /\ lo <= b /\ b <= w2n dst /\
       w2n dst+32 <= b+sz /\
       w2n dstT = concretize_positions C' owner aid + (w2n dst-b)))` by
    (irule concretize_memory_access_geometry >> simp[] >>
     conj_tac
     >- (qexists_tac `<| iao_ofst := opd; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>` >>
     fs[MEM] >> simp[source_memory_read_ranges_def, mem_read_ops_def]) >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  (all_tac >>
  `!i. i < 32 ==> relocation_pair lo (concretize_positions C')
      (EL c (q0::qs)) (w2n dst+i) (w2n dstT+i)` by
    (rpt strip_tac >> irule relocation_pair_range >> metis_tac[]) >>
  qexists_tac `dstT` >> simp[step_inst_base_def, exec_read1_def] >>
  rpt strip_tac >> irule joint_relocation_demand_current >> simp[] >>
  conj_tac
  >- (fs[MEM] >> simp[joint_observed_read_def, joint_reads_def, joint_mem_taint_def,
           source_memory_read_ranges_def, range_bytes_def] >> gvs[]) >>
  qpat_x_assum `!i. i < 32 ==> relocation_pair _ _ _ _ _`
    (qspec_then `i` mp_tac) >> simp[arithmeticTheory.ADD_COMM])
QED

val _ = List.app (fn th => if null (hyp th) then ()
                          else raise Fail "load production export has hypotheses")
  [frame_reachable_saved_allocas_from, joint_activation_cache_lower_bound,
   concretize_word_load_execution_clean_lanes];

Theorem concretize_word_load_demand_execution:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
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
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst ==>
  ?dstT tpost. eval_operand opd t = SOME dstT /\
    step_inst_base inst t = OK tpost /\
    tpost = update_var v (mload (w2n dstT) t) t /\
    post = update_var v (mload (w2n dst) s) s /\
    word_agree_except {i | i < 32 /\ w2n dst+i IN tn.t_mem}
      (mload (w2n dst) s) (mload (w2n dstT) t)
Proof
  strip_tac >> drule_all concretize_word_load_execution_clean_lanes >> strip_tac >>
  qexistsl_tac [`dstT`, `tpost`] >> asm_rewrite_tac[] >>
  drule_then assume_tac local_rel_demand >>
  irule demand_agree_mload >>
  goal_assum (drule_at (Pat `demand_agree _ _ _`)) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

val _ = if null (hyp concretize_word_load_demand_execution) then ()
        else raise Fail "load execution export has hypotheses";

(* Compatibility interfaces: the memory-word proof above is shared with ILOAD. *)
Theorem concretize_mload_execution_clean_lanes:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
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
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst ==>
  ?dstT tpost. eval_operand opd t = SOME dstT /\
    step_inst_base inst t = OK tpost /\
    tpost = update_var v (mload (w2n dstT) t) t /\
    post = update_var v (mload (w2n dst) s) s /\
    (!i. i < 32 /\ w2n dst+i NOTIN tn.t_mem ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c
        (w2n dst+i) (w2n dstT+i))
Proof
  strip_tac >> irule concretize_word_load_execution_clean_lanes >> simp[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >> metis_tac[]
QED

Theorem concretize_mload_demand_execution:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
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
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst ==>
  ?dstT tpost. eval_operand opd t = SOME dstT /\
    step_inst_base inst t = OK tpost /\
    tpost = update_var v (mload (w2n dstT) t) t /\
    post = update_var v (mload (w2n dst) s) s /\
    word_agree_except {i | i < 32 /\ w2n dst+i IN tn.t_mem}
      (mload (w2n dst) s) (mload (w2n dstT) t)
Proof
  strip_tac >> irule concretize_word_load_demand_execution >> simp[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >> metis_tac[]
QED
