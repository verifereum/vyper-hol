Theory concretizeLayoutLocalLoad
Ancestors concretizeLayoutLoadProduction frameRelocationLoadSteps list
  frameRelocationEnvironment concretizeLayoutReaderContext frameResolvedTrace
  venomExecSemantics
  frameRelocationTaintOrder frameRelocationGuardedValues frameRelocationGhostCopy
  frameRelocationBinding frameJointDemand frameOriginUpdates
  ptrDiscipline venomState frameRelocationMemory codegenRel
  frameRelocationLocal frameRelocationDemand finite_map pred_set frameRelocationCopyTaint

Theorem word_load_taint_update[local]:
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst ==>
  step_taint inst s (update_var v value s) tn =
    tn with t_var := tn.t_var |+ (v,mem_word_taint tn.t_mem (w2n dst))
Proof
  strip_tac >>
  `new_site_bytes s (update_var v value s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, out_taint_def, set_var_taint_def,
       taint_component_equality]
QED

Theorem concretize_word_load_local_complete:
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
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  MEM inst.inst_opcode [MLOAD;ILOAD] /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un)
Proof
  strip_tac >>
  drule_all concretize_word_load_execution_clean_lanes >> strip_tac >>
  drule_all concretize_word_load_demand_execution >> strip_tac >> gvs[] >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
     metis_tac[]) >>
  `step_taint inst s (update_var v (mload (w2n dst) s) s) tn =
     tn with t_var := tn.t_var |+ (v,mem_word_taint tn.t_mem (w2n dst))` by
    (irule word_load_taint_update >> simp[]) >>
  `step_taint inst t (update_var v (mload (w2n dstT) t) t) un =
     un with t_var := un.t_var |+ (v,mem_word_taint un.t_mem (w2n dstT))` by
    (irule word_load_taint_update >> simp[]) >>
  (conj_tac >- suspend "values") >>
  suspend "taint"
QED

Resume concretize_word_load_local_complete[values]:
  markerLib.RESUME_TAC >> (simp[word_load_taint_update] >>
  `local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
    (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,mem_word_taint tn.t_mem (w2n dst))))
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v (mload (w2n dst) s) s)
    (update_var v (mload (w2n dstT) t) t)` by
    (irule local_rel_update >> simp[] >>
     conj_tac
     >- (drule local_rel_observation >> simp[update_var_def, dead_result_rel_def]) >>
     conj_tac
     >- gvs[guarded_bytes_def, copy_bytes_def, origin_set_lookup,
            op_taint_def, FLOOKUP_UPDATE, mem_word_taint_def] >>
     conj_tac
     >- simp[guarded_ptr_def, copy_ptr_def, origin_set_lookup] >>
     goal_assum (drule_at Any) >>
     simp[guarded_ptr_other, guarded_bytes_other]) >>
  qpat_x_assum `local_rel _ _ _ _ _ (update_var _ _ _) _` mp_tac >>
  simp[local_rel_def, demand_agree_def] >> metis_tac[])
QED

Resume concretize_word_load_local_complete[taint]:
  markerLib.RESUME_TAC >> (`mem_word_taint un.t_mem (w2n dstT) SUBSET
   mem_word_taint tn.t_mem (w2n dst)` by
    (qpat_x_assum `relocation_taint_le _ _ _` mp_tac >>
     simp[relocation_taint_le_def, demand_taint_def, mem_word_taint_def, SUBSET_DEF] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[relocation_taint_le_def] >>
  simp[relocation_taint_le_def, op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac >- (gvs[demand_taint_def] >> metis_tac[]) >>
  gen_tac >> IF_CASES_TAC >> simp[] >> gvs[op_taint_def])
QED

Finalise concretize_word_load_local_complete

val _ = if null (hyp concretize_word_load_local_complete) then ()
        else raise Fail "complete load export has hypotheses";

Theorem mload_taint_update[local]:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst ==>
  step_taint inst s (update_var v value s) tn =
    tn with t_var := tn.t_var |+ (v,mem_word_taint tn.t_mem (w2n dst))
Proof
  strip_tac >> irule word_load_taint_update >> simp[]
QED

Theorem concretize_mload_local_complete:
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
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un)
Proof
  strip_tac >> irule concretize_word_load_local_complete >> simp[] >> metis_tac[]
QED

Theorem concretize_iload_local_complete:
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
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  inst.inst_opcode = ILOAD /\ inst.inst_operands = [opd] /\
  inst.inst_outputs = [v] /\ eval_operand opd s = SOME dst /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    step_prov PG G inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `MEM inst.inst_opcode [MLOAD;ILOAD]` by simp[] >>
  drule_all concretize_word_load_local_complete >> strip_tac >>
  drule_all concretize_word_load_execution_clean_lanes >> strip_tac >> gvs[] >>
  (conj_tac >- suspend "ghost") >>
  fs[relocation_env_def, relocation_reader_context_def, update_var_def]
QED
Resume concretize_iload_local_complete[ghost]:
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >> metis_tac[resolved_frame_erasure]) >>
  gvs[] >> simp[step_prov_def, out_prov_def, set_prov_def,
    origin_set_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  gen_tac >> IF_CASES_TAC >> simp[]
QED
Finalise concretize_iload_local_complete
