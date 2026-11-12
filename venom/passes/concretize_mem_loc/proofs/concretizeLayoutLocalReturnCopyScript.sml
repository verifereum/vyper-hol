Theory concretizeLayoutLocalReturnCopy
Ancestors concretizeLayoutReturnCopySteps concretizeLayoutLocalCalldataCopy
  o1PassContract venomWf venomInst frameJointTrace frameJointTransition
  frameOriginReachable frameOriginHistory frameResolvedTrace
  memLocDefs concretizePtrParamSupport frameRelocationTaintOrder
  frameRelocationMemory frameRelocationGhostCopy frameActivationLifetime
  frameRelocationCopyTaint frameRelocationStoreSteps frameRelocationReachableSupport
  concretizeLayoutSupplement concretizeLayoutStateTransport
  frameRelocationLocal frameRelocationValues frameRelocationGuardedValues
  frameRelocationEnvironment concretizeLayoutReaderContext
  ptrDiscipline venomExecSemantics venomState codegenRel list pred_set finite_map words

Theorem local_obs_returndata:
  concretize_local_obs s t ==> s.vs_returndata = t.vs_returndata
Proof
  simp[concretize_local_obs_def, dead_result_rel_def] >> strip_tac >>
  irule LIST_EQ >> simp[]
QED

Theorem return_copy_observation[local]:
  concretize_local_obs s t ==>
  concretize_local_obs (write_memory_with_expansion d xs s)
    (write_memory_with_expansion dT ys t)
Proof
  simp[concretize_local_obs_def, dead_result_rel_def, write_memory_with_expansion_def]
QED

Theorem concretize_returncopy_execution_geometry:
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
  lifetime_ok depth (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz ==>
  ?dstT. eval_operand opd t = SOME dstT /\
    eval_operand ops t = SOME src /\ eval_operand opn t = SOME sz /\
    w2n src + w2n sz <= LENGTH s.vs_returndata /\
    post = write_memory_with_expansion (w2n dst)
      (TAKE (w2n sz) (DROP (w2n src) s.vs_returndata)) s /\
    step_inst_base inst t = OK (write_memory_with_expansion (w2n dstT)
      (TAKE (w2n sz) (DROP (w2n src) s.vs_returndata)) t) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+w2n sz ==>
      w2n dstT <= z /\ z < w2n dstT+w2n sz /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+w2n sz))
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def, fn_insts_def,
        fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok Q fn` by suspend "fn" >>
  `eval_operand ops s = eval_operand ops t /\ eval_operand opn s = eval_operand opn t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) joint_calldatacopy_scalar_agreement >>
     disch_then irule >> simp[MEM] >> metis_tac[]) >>
  `step_inst_base inst s = OK post` by suspend "step" >>
  `s.vs_returndata = t.vs_returndata` by
    metis_tac[local_rel_observation, local_obs_returndata] >>
  `w2n src + w2n sz <= LENGTH s.vs_returndata /\
   post = write_memory_with_expansion (w2n dst)
      (TAKE (w2n sz) (DROP (w2n src) s.vs_returndata)) s` by
    (qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
     gvs[] >> simp[step_inst_base_def] >> IF_CASES_TAC >> simp[]) >>
  `?dstT. eval_operand opd t = SOME dstT /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+w2n sz ==>
      w2n dstT <= z /\ z < w2n dstT+w2n sz /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+w2n sz))` by suspend "geometry" >>
  pop_assum strip_assume_tac >> qexists_tac `dstT` >>
  gvs[] >>
  `step_inst_base inst t = OK (write_memory_with_expansion (w2n dstT)
      (TAKE (w2n sz) (DROP (w2n src) t.vs_returndata)) t)` by
    (simp[step_inst_base_def]) >>
  simp[] >> metis_tac[]
QED
Resume concretize_returncopy_execution_geometry[fn]:
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  drule_all ptr_frame_current_static >> strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED
Resume concretize_returncopy_execution_geometry[step]:
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  gvs[joint_transition_ordinary, step_inst_def]
QED
Resume concretize_returncopy_execution_geometry[geometry]:
  irule concretize_clean_write_geometry >> simp[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `fn_ptr_ok _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >>
  goal_assum (drule_at (Pat `lifetime_ok _ _ _`)) >>
  goal_assum (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >> simp[] >>
  qexists_tac `<| iao_ofst := opd; iao_size := SOME opn; iao_max_size := SOME opn |>` >>
  gvs[] >>
  simp[mem_write_ops_def, step_writes_def, source_memory_write_ranges_def,
    sized_source_write_range_def, write_memory_with_expansion_def]
QED
Finalise concretize_returncopy_execution_geometry

Theorem concretize_returncopy_local_complete:
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
  lifetime_ok depth (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  concretize_supplement D tn s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    step_prov PG G inst post = G /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, opcode_case_def]) >>
  drule_all concretize_returncopy_execution_geometry >> strip_tac >>
  qmatch_asmsub_abbrev_tac `post = write_memory_with_expansion (w2n dst) xs s` >>
  `LENGTH xs = w2n sz` by (simp[Abbr `xs`, LENGTH_TAKE_EQ, LENGTH_DROP]) >>
  `step_writes inst s post = [(w2n dst,w2n sz)] /\
   step_writes inst t (write_memory_with_expansion (w2n dstT) xs t) = [(w2n dstT,w2n sz)]` by
    (gvs[] >> simp[step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def]) >>
  qexists_tac `write_memory_with_expansion (w2n dstT) xs t` >>
  asm_rewrite_tac[] >> (conj_tac >- suspend "relation") >>
  (conj_tac >- (irule (cj 1 clean_copy_ghosts) >> simp[MEM] >> metis_tac[])) >>
  (conj_tac >- (irule clean_copy_taint_order >> simp[MEM] >>
    goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >> metis_tac[])) >>
  (conj_tac >- suspend "supplement") >>
  gvs[] >> fs[relocation_env_def, relocation_reader_context_def, write_memory_with_expansion_def]
QED
Resume concretize_returncopy_local_complete[relation]:
  `(guarded_bytes (retpc_var fn) rv (step_taint inst s post tn) :
     string -> bytes32 -> bytes32 -> bool) = guarded_bytes (retpc_var fn) rv tn` by
    (irule EQ_EXT >> gen_tac >> irule EQ_EXT >> gen_tac >> irule EQ_EXT >> gen_tac >>
     simp[guarded_bytes_def, frameRelocationGhostCopyTheory.copy_bytes_def,
          op_taint_def, step_taint_def, set_var_taint_def, DRESTRICT_UNIV]) >>
  asm_rewrite_tac[] >> gvs[] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) local_rel_write_memory >>
  disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >> (conj_tac >- metis_tac[]) >>
  fs[local_rel_def] >> metis_tac[return_copy_observation]
QED
Resume concretize_returncopy_local_complete[supplement]:
  `step_taint inst s post tn = tn with t_mem := tn.t_mem DIFF range_bytes [(w2n dst,w2n sz)]` by
    (irule (cj 2 clean_copy_ghosts) >> simp[MEM] >> metis_tac[]) >>
  gvs[concretize_supplement_def, write_memory_with_expansion_def]
QED
Finalise concretize_returncopy_local_complete

Theorem concretize_returncopy_bounds_abort_complete:
  ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  frame_reachable vs0 C stk PG G tn fn inst s /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  relocation_env s t /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R concretize_local_obs s t /\
  step_inst_base inst s = Abort a post ==>
  ?tpost. step_inst_base inst t = Abort a tpost /\
    dead_result_rel D (Abort a post) (Abort a tpost)
Proof
  strip_tac >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `eval_operand ops s = eval_operand ops t /\ eval_operand opn s = eval_operand opn t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) calldatacopy_scalar_agreement >>
     disch_then irule >> simp[MEM] >> metis_tac[]) >>
  `?dstT. eval_operand opd t = SOME dstT` by
    (drule local_rel_domains >> strip_tac >>
     drule_all operand_domain_agreement >> disch_then (qspec_then `opd` mp_tac) >>
     Cases_on `eval_operand opd t` >> simp[]) >>
  `s.vs_returndata = t.vs_returndata` by
    metis_tac[local_rel_observation, local_obs_returndata] >>
  qpat_x_assum `step_inst_base inst s = Abort a post` mp_tac >>
  gvs[] >> simp[step_inst_base_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[] >>
  simp[step_inst_base_def, dead_result_rel_def]
QED

val _ = if null (hyp concretize_returncopy_execution_geometry) andalso
           null (hyp concretize_returncopy_local_complete) andalso
           null (hyp concretize_returncopy_bounds_abort_complete) then ()
        else raise Fail "return copy exports have hypotheses";
