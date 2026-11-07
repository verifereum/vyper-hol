Theory concretizeLayoutLocalStore8
Ancestors concretizeLayoutStoreProduction concretizeLayoutRelocation frameRelocationStoreTaint
  frameRelocationStoreSteps frameRelocationObservations frameRelocationEnvironment
  frameRelocationCleanOperands frameRelocationReachableSupport frameRelocationGuardedValues
  pointerConfinedDefs memLocDefs frameRelocationLocal frameRelocationValues
  frameRelocationGhostCopy ptrDiscipline venomState venomExecSemantics
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameResolvedTrace frameActivationLookup frameActivationCache frameRelocationBinding
  concretizeLayoutAccessGeometry frameRelocationWriteCoverage frameJointDemand
  frameRelocationOpaque concretizePtrParamSupport codegenRel o1PassContract
  venomWf venomInst finite_map list pred_set words

Theorem mstore8_value_origin_free[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [opd;opv] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) ==>
  !v. opv = Var v ==> FLOOKUP rv v = NONE
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `v IN fn_pv P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `opd = Var v` >> gvs[]
QED

Theorem concretize_mstore8_execution_geometry:
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
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  ?dstT. eval_operand opd t = SOME dstT /\ eval_operand opv t = SOME value /\
    step_inst_base inst t = OK (mstore8 (w2n dstT) value t) /\
    post = mstore8 (w2n dst) value s /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+1 ==>
      w2n dstT <= z /\ z < w2n dstT+1 /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+1) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+1))
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `post = mstore8 (w2n dst) value s` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def, step_inst_base_def, exec_write2_def] >> metis_tac[]) >>
  `eval_operand opv t = SOME value` by suspend "value" >>
  `?dstT. eval_operand opd t = SOME dstT /\
    ((w2n dst+1 <= lo /\ w2n dstT = w2n dst) \/
     (?d owner aid b sz.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,sz) /\ lo <= b /\ b <= w2n dst /\
       w2n dst+1 <= b+sz /\
       w2n dstT = concretize_positions C' owner aid + (w2n dst-b)))` by
    suspend "address" >>
  `(!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+1 ==>
      w2n dstT <= z /\ z < w2n dstT+1 /\ a-w2n dst = z-w2n dstT) /\
   (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+1) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+1))` by suspend "memory" >>
  qexists_tac `dstT` >> asm_rewrite_tac[] >>
  (conj_tac >- simp[step_inst_base_def, exec_write2_def]) >>
  qpat_x_assum `!a z. _ /\ ~_ ==> _` mp_tac >> simp[]
QED

Resume concretize_mstore8_execution_geometry[value]:
  `?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def, fn_insts_def,
        fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok Q fn` by metis_tac[EVERY_MEM] >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv Q fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     drule resolved_frame_erasure >> strip_tac >>
     metis_tac[resolved_static_support]) >>
  `!v. opv = Var v ==> FLOOKUP rv v = NONE` by
    metis_tac[mstore8_value_origin_free] >>
  `eval_operand opv s = eval_operand opv t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
     disch_then irule >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `inst` >> simp[]) >> metis_tac[]
QED
Resume concretize_mstore8_execution_geometry[address]:
  irule concretize_memory_access_geometry >> simp[] >>
  conj_tac
  >- (qexists_tac `<| iao_ofst := opd; iao_size := SOME (Lit 1w);
                    iao_max_size := SOME (Lit 1w) |>` >>
      simp[source_memory_write_ranges_def, fixed_source_write_range_def,
           mem_write_ops_def]) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
Resume concretize_mstore8_execution_geometry[memory]:
  markerLib.RESUME_TAC >> (all_tac >>
  `(!i. i < 1 ==>
      w2n dst+i IN joint_writes (EL c (q0::qs)) (EL c es) /\
      w2n dstT+i IN range_bytes (step_writes inst t t) /\
      relocation_pair lo (concretize_positions C') (EL c (q0::qs))
        (w2n dst+i) (w2n dstT+i)) /\
   (!z. z IN range_bytes (step_writes inst t t) ==> ?a.
      a IN joint_writes (EL c (q0::qs)) (EL c es) /\
      relocation_pair lo (concretize_positions C') (EL c (q0::qs)) a z /\
      a-w2n dst = z-w2n dstT)` by
    (irule joint_store_write_correspondence >> asm_rewrite_tac[] >> metis_tac[]) >>
  `joint_writes (EL c (q0::qs)) (EL c es) =
    range_bytes [(w2n dst,1)] /\ step_writes inst t t = [(w2n dstT,1)]` by
    (`step_writes inst s post = [(w2n dst,1)] /\
      step_writes inst t t = [(w2n dstT,1)]` by
       (conj_tac >> irule step_writes_store >> metis_tac[]) >>
     fs[joint_writes_ordinary] >> metis_tac[]) >>
  conj_tac
  >- (ho_match_mp_tac (Q.INST
        [`R` |-> `relocation_pair lo (concretize_positions C') (EL c (q0::qs))`]
        coherent_written_interval) >>
      conj_tac
      >- (rpt strip_tac >> irule joint_mstore_demand_address_coherence >>
          `post.vs_allocas = s.vs_allocas` by simp[mstore8_def] >> metis_tac[]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `a NOTIN joint_writes (EL c (q0::qs)) (EL c es)` by
    (asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac) >>
  `joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
   z NOTIN range_bytes (step_writes inst t t)` by
    (irule concretize_positions_demand_write_complement >>
     conj_tac >- metis_tac[] >> asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  gvs[range_bytes_def] >> decide_tac)
QED
Finalise concretize_mstore8_execution_geometry


Theorem concretize_mstore8_local_complete:
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
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [opd;opv] /\
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
    step_prov PG G inst post = G /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un)
Proof
  strip_tac >> drule_all concretize_mstore8_execution_geometry >> strip_tac >>
  `demand_agree (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
     (\a. read_byte a post.vs_memory)
     (\z. read_byte z (mstore8 (w2n dstT) value t).vs_memory)` by suspend "demand" >>
  qexists_tac `mstore8 (w2n dstT) value t` >> asm_rewrite_tac[] >>
  conj_tac >- suspend "local" >>
  conj_tac >- simp[mstore8_def] >>
  conj_tac >- simp[mstore8_def] >>
  conj_tac >- simp[step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  irule relocation_taint_le_mstore8 >> simp[] >>
  goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >> metis_tac[]
QED
Resume concretize_mstore8_local_complete[demand]:
  rewrite_tac[mstore8_as_write_memory] >>
  qpat_x_assum `post = _` (fn th => rewrite_tac[th, mstore8_as_write_memory]) >>
  irule demand_agree_write_memory >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `joint_relocation_demand lo (concretize_positions C') q0 es qs c` >>
  metis_tac[local_rel_demand]
QED
Resume concretize_mstore8_local_complete[local]:
  qpat_x_assum `local_rel _ _ _ _ _ s t` mp_tac >>
  qpat_x_assum `demand_agree _ _ _` mp_tac >>
  simp[local_rel_def, variable_domains_def, variables_agree_on_def,
       local_values_def, lookup_var_def, mstore8_def,
       guarded_bytes_def, copy_bytes_def, op_taint_def, step_taint_def,
       set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV,
       dead_result_rel_memory_frame]
QED
Finalise concretize_mstore8_local_complete

val _ = if List.all (null o hyp)
  [concretize_mstore8_execution_geometry, concretize_mstore8_local_complete]
  then () else raise Fail "Store8 exports have hypotheses";
