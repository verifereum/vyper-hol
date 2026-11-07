Theory concretizeLayoutCopyProduction
Ancestors concretizeLayoutStoreProduction frameRelocationBinding
  frameRelocationCopyTaint frameJointTrace frameJointTransition frameJointDemand
  ptrDiscipline venomState frameJointTaint memLocDefs pointerConfinedDefs
  concretizeLayoutAccessGeometry frameRelocationCleanOperands frameRelocationValues
  frameRelocationLocal frameRelocationGuardedValues frameRelocationReachableSupport
  frameResolvedTrace frameOriginReachable frameOriginHistory concretizePtrParamSupport
  frameRelocationCopySteps venomExecSemantics finite_map list words pred_set
  o1PassContract venomWf venomInst concretizeLayoutRelocation frameActivationCache
  frameRelocationWriteCoverage contextCodegenRel codegenRel finiteByteDemand

(* A demanded copy result is clean, so its simultaneous pre-state producer
   is clean. No corresponding fact is needed for tainted producer lanes. *)
Theorem joint_mcopy_demand_producer_clean:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  post = mcopy (w2n dst) (w2n src) (w2n sz) s /\
  joint_relocation_demand lo positions q0 es qs (SUC c) a z /\
  w2n dst <= a /\ a < w2n dst+w2n sz ==>
  w2n src+(a-w2n dst) NOTIN tn.t_mem
Proof
  strip_tac >>
  `a NOTIN joint_mem_taint (EL (SUC c) (q0::qs))` by
    (irule joint_relocation_demand_clean >> metis_tac[]) >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >>
  gvs[joint_mem_taint_def] >>
  `a IN (step_taint inst s (mcopy (w2n dst) (w2n src) (w2n sz) s) tn).t_mem <=>
   if w2n dst <= a /\ a < w2n dst+w2n sz then
     w2n src+(a-w2n dst) IN tn.t_mem else a IN tn.t_mem` by
    (irule step_taint_mcopy_mem >> simp[] >> metis_tac[]) >>
  gvs[]
QED

val _ = if null (hyp joint_mcopy_demand_producer_clean) then ()
        else raise Fail "copy producer cleanliness export has hypotheses";

Theorem mcopy_size_origin_free[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) ==>
  !v. opn = Var v ==> FLOOKUP rv v = NONE
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `v IN fn_pv P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `opd = Var v` >> Cases_on `ops = Var v` >> gvs[] >>
  rpt strip_tac >> gvs[]
QED

Theorem concretize_mcopy_execution_geometry:
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
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz ==>
  ?dstT srcT tpost. eval_operand opd t = SOME dstT /\
    eval_operand ops t = SOME srcT /\ eval_operand opn t = SOME sz /\
    step_inst_base inst t = OK tpost /\
    tpost = mcopy (w2n dstT) (w2n srcT) (w2n sz) t /\
    post = mcopy (w2n dst) (w2n src) (w2n sz) s /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+w2n sz ==>
      w2n dstT <= z /\ z < w2n dstT+w2n sz /\
      a-w2n dst = z-w2n dstT /\
      joint_relocation_demand lo (concretize_positions C') q0 es qs c
        (w2n src+(a-w2n dst)) (w2n srcT+(z-w2n dstT))) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+w2n sz))
Proof
  strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `post = mcopy (w2n dst) (w2n src) (w2n sz) s` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def, step_inst_base_def] >> metis_tac[]) >>
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >> metis_tac[resolved_frame_erasure]) >>
  `eval_operand opn t = SOME sz` by suspend "size" >>
  Cases_on `w2n sz = 0` >- suspend "zero" >>
  `?dstT. eval_operand opd t = SOME dstT /\
    ((w2n dst+w2n sz <= lo /\ w2n dstT = w2n dst) \/
     (?d owner aid b len.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,len) /\ lo <= b /\ b <= w2n dst /\
       w2n dst+w2n sz <= b+len /\
       w2n dstT = concretize_positions C' owner aid + (w2n dst-b)))` by
    suspend "destination" >>
  pop_assum strip_assume_tac >>
  `?srcT. eval_operand ops t = SOME srcT /\
    ((w2n src+w2n sz <= lo /\ w2n srcT = w2n src) \/
     (?d owner aid b len.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,len) /\ lo <= b /\ b <= w2n src /\
       w2n src+w2n sz <= b+len /\
       w2n srcT = concretize_positions C' owner aid + (w2n src-b)))` by
    suspend "source" >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`dstT`, `srcT`] >>
  `step_inst_base inst t = OK (mcopy (w2n dstT) (w2n srcT) (w2n sz) t)` by
    simp[step_inst_base_def] >>
  asm_rewrite_tac[] >>
  `!i. i < w2n sz ==> relocation_pair lo (concretize_positions C')
    (EL c (q0::qs)) (w2n dst+i) (w2n dstT+i)` by
    (rpt strip_tac >> irule relocation_pair_range >>
     qexists_tac `w2n sz` >> asm_rewrite_tac[] >> metis_tac[]) >>
  `!i. i < w2n sz ==> relocation_pair lo (concretize_positions C')
    (EL c (q0::qs)) (w2n src+i) (w2n srcT+i)` by
    (rpt strip_tac >> irule relocation_pair_range >>
     qexists_tac `w2n sz` >> asm_rewrite_tac[] >> metis_tac[]) >>
  `post.vs_allocas = s.vs_allocas` by simp[mcopy_def, write_memory_with_expansion_def] >>
  (conj_tac >- (rpt gen_tac >> strip_tac >>
  `a = w2n dst+(a-w2n dst) /\ a-w2n dst < w2n sz` by decide_tac >>
  `relocation_pair lo (concretize_positions C') (EL c (q0::qs))
    a (w2n dstT+(a-w2n dst))` by metis_tac[] >>
  `z = w2n dstT+(a-w2n dst)` by
    (irule joint_mstore_demand_address_coherence >> metis_tac[]) >>
  `w2n dstT <= z /\ z < w2n dstT+w2n sz /\
   a-w2n dst = z-w2n dstT` by decide_tac >>
  qpat_x_assum `a = w2n dst+(a-w2n dst)` kall_tac >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac >- decide_tac >>
  irule joint_relocation_demand_current >>
  conj_tac >- decide_tac >> conj_tac
  >- (`w2n src+(a-w2n dst) NOTIN tn.t_mem` by
        (irule joint_mcopy_demand_producer_clean >> metis_tac[]) >>
      `a+w2n src-w2n dst = w2n src+(a-w2n dst)` by decide_tac >>
      qpat_x_assum `a+w2n src-w2n dst = w2n src+(a-w2n dst)` SUBST1_TAC >>
      qpat_x_assum `z = w2n dstT+(a-w2n dst)` kall_tac >>
      qpat_x_assum `a-w2n dst = z-w2n dstT` kall_tac >>
      simp[joint_observed_read_def, joint_reads_def, joint_mem_taint_def,
           source_memory_read_ranges_def, range_bytes_def] >>
      `a+w2n src-w2n dst = w2n src+(a-w2n dst)` by decide_tac >> metis_tac[]) >>
  `a+w2n src-w2n dst = w2n src+(a-w2n dst)` by decide_tac >>
  metis_tac[]) >> (
  `joint_writes (EL c (q0::qs)) (EL c es) =
     range_bytes [(w2n dst,w2n sz)] /\
   step_writes inst t t = [(w2n dstT,w2n sz)]` by
    simp[joint_writes_ordinary, step_writes_def,
         source_memory_write_ranges_def, sized_source_write_range_def] >>
  `!w. w IN range_bytes (step_writes inst t t) ==> ?byte.
     byte IN joint_writes (EL c (q0::qs)) (EL c es) /\
     relocation_pair lo (concretize_positions C') (EL c (q0::qs)) byte w` by
    (rpt strip_tac >>
     `w2n dstT <= w /\ w < w2n dstT+w2n sz` by
       (qpat_x_assum `w IN range_bytes _` mp_tac >>
        asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac) >>
     qexists_tac `w2n dst+(w-w2n dstT)` >> conj_tac
     >- (simp[range_bytes_def] >> decide_tac) >>
     `w-w2n dstT < w2n sz /\ w = w2n dstT+(w-w2n dstT)` by decide_tac >>
     metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `a NOTIN joint_writes (EL c (q0::qs)) (EL c es)` by
    (asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac) >>
  `joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
   z NOTIN range_bytes (step_writes inst t t)` by
    (irule concretize_positions_demand_write_complement >>
     conj_tac >- metis_tac[] >> asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `z NOTIN range_bytes _` mp_tac >>
  asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac))
QED

Resume concretize_mcopy_execution_geometry[size]:
  `?Q. fn_ptr_ok Q fn /\ (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv Q fn)` by
    (`?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` by
       (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
     pop_assum strip_assume_tac >>
     `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def, fn_insts_def,
           fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
     drule_all ptr_frame_current_static >> strip_tac >>
     qexists_tac `Q` >> conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
     metis_tac[resolved_static_support]) >>
  `!v. opn = Var v ==> FLOOKUP rv v = NONE` by
    (metis_tac[mcopy_size_origin_free]) >>
  `eval_operand opn s = eval_operand opn t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
     disch_then irule >> simp[] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `inst` >> simp[]) >> metis_tac[]
QED
Resume concretize_mcopy_execution_geometry[zero]:
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `?dstT. eval_operand opd t = SOME dstT` by
    (Cases_on `eval_operand opd t` >> metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE]) >>
  `?srcT. eval_operand ops t = SOME srcT` by
    (Cases_on `eval_operand ops t` >> metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE]) >>
  qexistsl_tac [`dstT`, `srcT`] >> asm_rewrite_tac[step_inst_base_def] >>
  simp[] >> rpt strip_tac >>
  `a NOTIN joint_writes (EL c (q0::qs)) (EL c es)` by
    (simp[joint_writes_ordinary, step_writes_def, range_bytes_def,
          source_memory_write_ranges_def, sized_source_write_range_def] >> decide_tac) >>
  irule joint_relocation_demand_retained >> metis_tac[]
QED
Resume concretize_mcopy_execution_geometry[destination]:
  irule concretize_memory_access_geometry >> simp[] >>
  conj_tac
  >- (qexists_tac `<| iao_ofst := opd; iao_size := SOME opn;
                    iao_max_size := SOME opn |>` >>
      simp[source_memory_write_ranges_def, sized_source_write_range_def,
           mem_write_ops_def]) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
Resume concretize_mcopy_execution_geometry[source]:
  markerLib.RESUME_TAC >> (irule concretize_memory_access_geometry >> simp[] >>
  conj_tac
  >- (qexists_tac `<| iao_ofst := ops; iao_size := SOME opn;
                    iao_max_size := SOME opn |>` >>
      simp[source_memory_read_ranges_def, mem_read_ops_def]) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[])
QED
Finalise concretize_mcopy_execution_geometry

val _ = if null (hyp concretize_mcopy_execution_geometry) then ()
        else raise Fail "copy geometry export has hypotheses";
