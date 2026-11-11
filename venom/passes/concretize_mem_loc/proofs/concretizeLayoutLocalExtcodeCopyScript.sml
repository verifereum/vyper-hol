Theory concretizeLayoutLocalExtcodeCopy
Ancestors concretizeLayoutLocalCalldataCopy concretizeLayoutLocalExtcodeSize
  frameRelocationValues codegenRel concretizePtrParamSupport frameRelocationStoreSteps
  vfmState ptrDiscipline venomExecSemantics venomState list words finite_map
  pointerConfinedDefs memLocDefs frameRelocationCleanOperands
  frameRelocationGuardedValues frameRelocationLocal frameRelocationEnvironment
  concretizeLayoutReaderContext frameJointTrace frameJointTransition
  frameOriginReachable frameOriginHistory frameRelocationReachableSupport
  frameResolvedTrace frameRelocationBinding frameJointDemand
  concretizeLayoutRelocation frameActivationLifetime o1PassContract venomWf venomInst
  frameRelocationTaintOrder frameRelocationMemory frameRelocationObservations

Theorem extcodecopy_execution:
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [opa;opd;ops;opn] /\
  eval_operand opa s = SOME addr /\ eval_operand opd s = SOME dst /\
  eval_operand ops s = SOME src /\ eval_operand opn s = SOME sz /\
  eval_operand opa t = SOME addr /\ eval_operand opd t = SOME dstT /\
  eval_operand ops t = SOME src /\ eval_operand opn t = SOME sz /\
  dead_result_rel D (Halt s) (Halt t) /\ step_inst_base inst s = OK post ==>
  post = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) (lookup_account (w2w addr) s.vs_accounts).code ++
      REPLICATE (w2n sz) 0w)) s /\
  step_inst_base inst t = OK (write_memory_with_expansion (w2n dstT)
    (TAKE (w2n sz) (DROP (w2n src) (lookup_account (w2w addr) s.vs_accounts).code ++
      REPLICATE (w2n sz) 0w)) t)
Proof
  strip_tac >>
  `!a. (lookup_account a s.vs_accounts).code = (lookup_account a t.vs_accounts).code` by
    (gen_tac >> irule accounts_agree_except_code >> qexists_tac `D` >> fs[dead_result_rel_def]) >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[opcode_case_def] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >> simp[]
QED

Theorem extcodecopy_scalar_origin_free[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [opa;opd;ops;opn] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\ MEM op [opa;ops;opn] ==>
  !v. op = Var v ==> FLOOKUP rv v = NONE
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `v IN fn_pv P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `opa = Var v` >> Cases_on `opd = Var v` >>
  Cases_on `ops = Var v` >> Cases_on `opn = Var v` >> gvs[]
QED

Theorem joint_extcodecopy_scalar_agreement:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [opa;opd;ops;opn] /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  !op. MEM op [opa;ops;opn] ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
     fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[extcodecopy_scalar_origin_free] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `inst` >> simp[] >> gvs[]
QED

Theorem concretize_extcodecopy_local_complete:
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
  relocation_env s t /\ relocation_reader_context s t /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  inst.inst_opcode = EXTCODECOPY /\ inst.inst_operands = [opa;opd;ops;opn] /\
  eval_operand opa s = SOME addr /\ eval_operand opd s = SOME dst /\
  eval_operand ops s = SOME src /\ eval_operand opn s = SOME sz /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
      (guarded_bytes (retpc_var fn) rv (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG G inst post = G /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost /\
    post.vs_code = tpost.vs_code /\ post.vs_data_section = tpost.vs_data_section
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `inst.inst_outputs = []` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, opcode_case_def]) >>
  `?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def, fn_insts_def,
        fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok Q fn` by suspend "fn" >>
  `!op. MEM op [opa;ops;opn] ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     drule_at (Pat `local_rel _ _ _ _ _ _ _`) joint_extcodecopy_scalar_agreement >>
     disch_then irule >> fs[relocation_env_def] >> metis_tac[]) >>
  `eval_operand opa t = SOME addr /\ eval_operand ops t = SOME src /\
   eval_operand opn t = SOME sz` by metis_tac[listTheory.MEM] >>
  `step_inst_base inst s = OK post` by suspend "step" >>
  `dead_result_rel D (Halt s) (Halt t)` by
    (drule local_rel_observation >> simp[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `?dummy. eval_operand opd t = SOME dummy` by
    (Cases_on `eval_operand opd t` >> metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE]) >>
  `post = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) (lookup_account (w2w addr) s.vs_accounts).code ++
      REPLICATE (w2n sz) 0w)) s` by
    (irule (cj 1 extcodecopy_execution) >> simp[] >> qexists_tac `D` >> simp[] >> metis_tac[]) >>
  `?dstT. eval_operand opd t = SOME dstT /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+w2n sz ==>
      w2n dstT <= z /\ z < w2n dstT+w2n sz /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+w2n sz))` by suspend "geometry" >>
  pop_assum strip_assume_tac >>
  `step_inst_base inst t = OK (write_memory_with_expansion (w2n dstT)
    (TAKE (w2n sz) (DROP (w2n src) (lookup_account (w2w addr) s.vs_accounts).code ++
      REPLICATE (w2n sz) 0w)) t)` by
    (irule (cj 2 extcodecopy_execution) >> simp[] >> qexists_tac `D` >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `post = write_memory_with_expansion (w2n dst) xs s` >>
  `LENGTH xs = w2n sz` by (simp[Abbr `xs`, LENGTH_TAKE_EQ, LENGTH_APPEND]) >>
  qexists_tac `write_memory_with_expansion (w2n dstT) xs t` >>
  asm_rewrite_tac[] >> (conj_tac >- suspend "relation") >>
  (conj_tac >- (irule (cj 1 clean_copy_ghosts) >> simp[] >>
    qexistsl_tac [`w2n dst`, `w2n sz`, `s`, `xs`] >>
    simp[step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def])) >>
  (conj_tac >- suspend "taint") >>
  gvs[] >> fs[relocation_env_def, relocation_reader_context_def, write_memory_with_expansion_def]
QED
Resume concretize_extcodecopy_local_complete[fn]:
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  drule_all ptr_frame_current_static >> strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED
Resume concretize_extcodecopy_local_complete[step]:
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  gvs[joint_transition_ordinary, step_inst_def]
QED
Resume concretize_extcodecopy_local_complete[geometry]:
  irule concretize_clean_write_geometry >> simp[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `fn_ptr_ok _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >>
  goal_assum (drule_at (Pat `lifetime_ok _ _ _`)) >>
  goal_assum (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >> simp[] >>
  qexists_tac `<| iao_ofst := opd; iao_size := SOME opn; iao_max_size := SOME opn |>` >>
  simp[mem_write_ops_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, write_memory_with_expansion_def] >> metis_tac[]
QED
Resume concretize_extcodecopy_local_complete[relation]:
  `(guarded_bytes (retpc_var fn) rv (step_taint inst s post tn) :
     string -> bytes32 -> bytes32 -> bool) = guarded_bytes (retpc_var fn) rv tn` by
    (irule EQ_EXT >> gen_tac >> irule EQ_EXT >> gen_tac >> irule EQ_EXT >> gen_tac >>
     simp[guarded_bytes_def, frameRelocationGhostCopyTheory.copy_bytes_def,
          op_taint_def, step_taint_def, set_var_taint_def, DRESTRICT_UNIV]) >>
  asm_rewrite_tac[] >> gvs[] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) local_rel_write_memory >>
  disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >> (conj_tac >- metis_tac[]) >>
  fs[local_rel_def, write_memory_with_expansion_def, dead_result_rel_memory_frame]
QED
Resume concretize_extcodecopy_local_complete[taint]:
  irule clean_copy_taint_order >> simp[] >>
  goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  qexistsl_tac [`w2n dst`, `w2n dstT`, `w2n sz`, `xs`] >>
  simp[step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def] >> metis_tac[]
QED
Finalise concretize_extcodecopy_local_complete
