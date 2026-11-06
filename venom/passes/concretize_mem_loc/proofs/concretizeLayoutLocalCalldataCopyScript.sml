Theory concretizeLayoutLocalCalldataCopy
Ancestors concretizeLayoutLocalCopy concretizeLayoutLocalCalldataReaders
  frameRelocationEnvironment concretizeLayoutReaderContext venomExecSemantics
  venomState list words ptrDiscipline memLocDefs pointerConfinedDefs
  frameRelocationCleanOperands finite_map frameJointTrace frameJointTransition
  frameOriginReachable frameOriginHistory frameRelocationReachableSupport
  frameResolvedTrace concretizePtrParamSupport frameRelocationLocal
  frameRelocationGuardedValues concretizeLayoutAccessGeometry concretizeLayoutStoreProduction
  frameRelocationBinding frameActivationCache frameJointDemand
  frameRelocationValues o1PassContract venomWf venomInst
  concretizeLayoutRelocation frameActivationLifetime
  frameRelocationWriteCoverage contextCodegenRel codegenRel finiteByteDemand pred_set
  frameRelocationMemory frameRelocationTaintOrder frameRelocationStoreSteps
  frameRelocationObservations

(* Immutable byte sources share one padded-slice write boundary. *)
Definition clean_copy_source_def:
  clean_copy_source inst s =
    if inst.inst_opcode = CODECOPY then s.vs_code
    else if inst.inst_opcode = DLOADBYTES then s.vs_data_section
    else s.vs_call_ctx.cc_calldata
End
Theorem calldatacopy_execution:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES] /\
  inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME dstT /\ eval_operand ops t = SOME src /\
  eval_operand opn t = SOME sz /\ relocation_env s t /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  step_inst_base inst s = OK post ==>
  post = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) (clean_copy_source inst s) ++
      REPLICATE (w2n sz) 0w)) s /\
  step_inst_base inst t = OK (write_memory_with_expansion (w2n dstT)
    (TAKE (w2n sz) (DROP (w2n src) (clean_copy_source inst s) ++
      REPLICATE (w2n sz) 0w)) t)
Proof
  strip_tac >> fs[MEM, clean_copy_source_def] >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  fs[relocation_env_def]
QED

val _ = if null (hyp calldatacopy_execution) then ()
        else raise Fail "calldata copy export has hypotheses";

Theorem calldatacopy_scalar_origin_free[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES;RETURNDATACOPY] /\ inst.inst_operands = [opd;ops;opn] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  MEM op [ops;opn] ==>
  !v. op = Var v ==> FLOOKUP rv v = NONE
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `v IN fn_pv P fn` by metis_tac[] >>
  `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `opd = Var v` >> Cases_on `ops = Var v` >>
  Cases_on `opn = Var v` >> gvs[]
QED

Theorem calldatacopy_scalar_agreement:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES;RETURNDATACOPY] /\ inst.inst_operands = [opd;ops;opn] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  eval_operand ops s = eval_operand ops t /\
  eval_operand opn s = eval_operand opn t
Proof
  strip_tac >>
  `!op. MEM op [ops;opn] ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
     disch_then irule >> simp[] >>
     conj_tac >- metis_tac[calldatacopy_scalar_origin_free] >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     qexists_tac `inst` >> simp[] >> gvs[]) >>
  metis_tac[listTheory.MEM]
QED

Theorem joint_calldatacopy_scalar_agreement:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES;RETURNDATACOPY] /\ inst.inst_operands = [opd;ops;opn] /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  eval_operand ops s = eval_operand ops t /\
  eval_operand opn s = eval_operand opn t
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
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) calldatacopy_scalar_agreement >>
  disch_then irule >> fs[MEM] >> metis_tac[]
QED

(* Payload- and arity-independent destination/write-complement geometry. *)
Theorem concretize_clean_write_geometry:
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
  eval_operand opd s = SOME dst /\ post.vs_allocas = s.vs_allocas /\
  mem_write_ops inst = SOME access /\ access.iao_ofst = opd /\
  source_memory_write_ranges inst s = [(w2n dst,cap)] /\ len <= cap /\
  step_writes inst s post = [(w2n dst,len)] ==>
  ?dstT. eval_operand opd t = SOME dstT /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+len ==>
      w2n dstT <= z /\ z < w2n dstT+len /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+len) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+len))
Proof
  strip_tac >>
  `joint_writes (EL c (q0::qs)) (EL c es) = range_bytes [(w2n dst,len)]` by
    simp[joint_writes_ordinary] >>
  Cases_on `len = 0`
  >- (`variable_domains s t` by metis_tac[local_rel_domains] >>
      `?dstT. eval_operand opd t = SOME dstT` by
        (Cases_on `eval_operand opd t` >>
         metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE]) >>
      qexists_tac `dstT` >> simp[] >> rpt strip_tac >>
      irule joint_relocation_demand_retained >> simp[range_bytes_def] >> metis_tac[]) >>
  `?dstT. eval_operand opd t = SOME dstT /\
    ((w2n dst+cap <= lo /\ w2n dstT = w2n dst) \/
     (?d owner aid b sz.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,sz) /\ lo <= b /\ b <= w2n dst /\ w2n dst+cap <= b+sz /\
       w2n dstT = concretize_positions C' owner aid + (w2n dst-b)))` by
    (irule concretize_memory_access_geometry >> simp[] >>
     conj_tac >- (qexists_tac `access` >> simp[]) >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> qexists_tac `dstT` >> asm_rewrite_tac[] >>
  `!i. i < len ==> relocation_pair lo (concretize_positions C')
    (EL c (q0::qs)) (w2n dst+i) (w2n dstT+i)` by
    (rpt strip_tac >> `i < cap` by decide_tac >>
     irule relocation_pair_range >>
     qexists_tac `cap` >> asm_rewrite_tac[] >> metis_tac[]) >>
  (conj_tac >- suspend "written") >> suspend "retained"
QED
Resume concretize_clean_write_geometry[written]:
  markerLib.RESUME_TAC >> (rpt gen_tac >> strip_tac >>
  `a = w2n dst+(a-w2n dst) /\ a-w2n dst < len` by decide_tac >>
  `relocation_pair lo (concretize_positions C') (EL c (q0::qs))
    a (w2n dstT+(a-w2n dst))` by metis_tac[] >>
  `z = w2n dstT+(a-w2n dst)` by
    (irule joint_mstore_demand_address_coherence >> metis_tac[]) >> decide_tac)
QED
Resume concretize_clean_write_geometry[retained]:
  markerLib.RESUME_TAC >> (
  `!w. w IN range_bytes [(w2n dstT,len)] ==> ?byte.
     byte IN joint_writes (EL c (q0::qs)) (EL c es) /\
     relocation_pair lo (concretize_positions C') (EL c (q0::qs)) byte w` by
    (rpt strip_tac >>
     `w2n dstT <= w /\ w < w2n dstT+len` by
       (qpat_x_assum `w IN range_bytes _` mp_tac >>
        asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac) >>
     qexists_tac `w2n dst+(w-w2n dstT)` >> conj_tac
     >- (simp[range_bytes_def] >> decide_tac) >>
     `w-w2n dstT < len /\ w = w2n dstT+(w-w2n dstT)` by decide_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `a NOTIN joint_writes (EL c (q0::qs)) (EL c es)` by
    (asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac) >>
  `joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
   z NOTIN range_bytes [(w2n dstT,len)]` by
    (irule concretize_positions_demand_write_complement >>
     conj_tac >- metis_tac[] >> asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >> asm_rewrite_tac[] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> qpat_x_assum `z NOTIN range_bytes _` mp_tac >>
  asm_rewrite_tac[] >> simp[range_bytes_def] >> decide_tac)
QED
Finalise concretize_clean_write_geometry

Theorem concretize_calldatacopy_execution_geometry:
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
  relocation_env s t /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) Obs s t /\
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES] /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz ==>
  ?dstT. eval_operand opd t = SOME dstT /\
    eval_operand ops t = SOME src /\ eval_operand opn t = SOME sz /\
    post = write_memory_with_expansion (w2n dst)
      (TAKE (w2n sz) (DROP (w2n src) (clean_copy_source inst s) ++ REPLICATE (w2n sz) 0w)) s /\
    step_inst_base inst t = OK (write_memory_with_expansion (w2n dstT)
      (TAKE (w2n sz) (DROP (w2n src) (clean_copy_source inst s) ++ REPLICATE (w2n sz) 0w)) t) /\
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
     disch_then irule >> fs[MEM] >> metis_tac[]) >>
  `eval_operand ops t = SOME src /\ eval_operand opn t = SOME sz` by metis_tac[] >>
  `step_inst_base inst s = OK post` by suspend "step" >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `?dummy. eval_operand opd t = SOME dummy` by
    (Cases_on `eval_operand opd t` >> metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE]) >>
  `post = write_memory_with_expansion (w2n dst)
    (TAKE (w2n sz) (DROP (w2n src) (clean_copy_source inst s) ++ REPLICATE (w2n sz) 0w)) s` by
    (irule (cj 1 calldatacopy_execution) >> simp[] >> metis_tac[]) >>
  `?dstT. eval_operand opd t = SOME dstT /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+w2n sz ==>
      w2n dstT <= z /\ z < w2n dstT+w2n sz /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+w2n sz))` by suspend "geometry" >>
  pop_assum strip_assume_tac >> qexists_tac `dstT` >> asm_rewrite_tac[] >>
  irule (cj 2 calldatacopy_execution) >> simp[] >> metis_tac[]
QED

Resume concretize_calldatacopy_execution_geometry[fn]:
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  drule_all ptr_frame_current_static >> strip_tac >> fs[EVERY_MEM] >> metis_tac[]
QED
Resume concretize_calldatacopy_execution_geometry[step]:
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  gvs[joint_transition_ordinary, step_inst_def]
QED
Resume concretize_calldatacopy_execution_geometry[geometry]:
  irule concretize_clean_write_geometry >> simp[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `fn_ptr_ok _ _`)) >>
  goal_assum (drule_at (Pat `callee_first _ _`)) >>
  goal_assum (drule_at (Pat `lifetime_ok _ _ _`)) >>
  goal_assum (drule_at (Pat `resolved_config_ok _ _ _`)) >>
  goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >> simp[] >>
  qexists_tac `<| iao_ofst := opd; iao_size := SOME opn; iao_max_size := SOME opn |>` >>
  fs[MEM] >> simp[mem_write_ops_def, step_writes_def,
    source_memory_write_ranges_def, sized_source_write_range_def,
    write_memory_with_expansion_def] >> metis_tac[]
QED
Finalise concretize_calldatacopy_execution_geometry

Theorem clean_copy_ghosts:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES;EXTCODECOPY;RETURNDATACOPY] /\
  inst.inst_outputs = [] /\ step_writes inst s post = [(dst,len)] /\
  post = write_memory_with_expansion dst xs s ==>
  step_prov PG G inst post = G /\
  step_taint inst s post tn = tn with t_mem := tn.t_mem DIFF range_bytes [(dst,len)]
Proof
  strip_tac >> fs[MEM] >> (conj_tac
  >- simp[step_prov_def, set_prov_def, DRESTRICT_UNIV]) >>
  `new_site_bytes s post = {}` by
    (irule new_site_bytes_unchanged >> simp[write_memory_with_expansion_def]) >>
  gvs[] >> simp[step_taint_def, mem_taint_def, written_taint_def,
    set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    taint_component_equality, DRESTRICT_UNIV] >> rpt CASE_TAC >> simp[]
QED

Theorem clean_copy_taint_order:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES;EXTCODECOPY;RETURNDATACOPY] /\
  inst.inst_outputs = [] /\ step_writes inst s post = [(dst,len)] /\
  step_writes inst t tpost = [(dstT,len)] /\
  post = write_memory_with_expansion dst xs s /\
  tpost = write_memory_with_expansion dstT xs t /\ relocation_taint_le R tn un /\
  (!a z. next a z /\ dst <= a /\ a < dst+len ==> dstT <= z /\ z < dstT+len) /\
  (!a z. next a z /\ ~(dst <= a /\ a < dst+len) ==>
    R a z /\ ~(dstT <= z /\ z < dstT+len)) ==>
  relocation_taint_le next (step_taint inst s post tn) (step_taint inst t tpost un)
Proof
  strip_tac >>
  `step_taint inst s post tn = tn with t_mem := tn.t_mem DIFF range_bytes [(dst,len)]` by
    (irule (cj 2 clean_copy_ghosts) >> simp[] >> metis_tac[]) >>
  `step_taint inst t tpost un = un with t_mem := un.t_mem DIFF range_bytes [(dstT,len)]` by
    (irule (cj 2 clean_copy_ghosts) >> simp[] >> metis_tac[]) >>
  gvs[relocation_taint_le_def, frameRelocationCopyTaintTheory.demand_taint_def,
      range_bytes_def, op_taint_def] >> metis_tac[]
QED


Theorem calldatacopy_ghosts:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES] /\ inst.inst_operands = [opd;ops;opn] /\
  inst.inst_outputs = [] /\ eval_operand opd s = SOME dst /\
  eval_operand ops s = SOME src /\ eval_operand opn s = SOME sz /\
  post = write_memory_with_expansion (w2n dst) xs s ==>
  step_prov PG G inst post = G /\
  step_taint inst s post tn = tn with t_mem :=
    tn.t_mem DIFF range_bytes [(w2n dst,w2n sz)]
Proof
  strip_tac >> irule clean_copy_ghosts >>
  fs[MEM] >> simp[step_writes_def, source_memory_write_ranges_def,
    sized_source_write_range_def] >> metis_tac[]
QED

Theorem calldatacopy_taint_order:
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES] /\ inst.inst_operands = [opd;ops;opn] /\
  inst.inst_outputs = [] /\ eval_operand opd s = SOME dst /\
  eval_operand ops s = SOME src /\ eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME dstT /\ eval_operand ops t = SOME src /\
  eval_operand opn t = SOME sz /\
  post = write_memory_with_expansion (w2n dst) xs s /\
  tpost = write_memory_with_expansion (w2n dstT) xs t /\
  relocation_taint_le R tn un /\
  (!a z. next a z /\ w2n dst <= a /\ a < w2n dst+w2n sz ==>
    w2n dstT <= z /\ z < w2n dstT+w2n sz) /\
  (!a z. next a z /\ ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
    R a z /\ ~(w2n dstT <= z /\ z < w2n dstT+w2n sz)) ==>
  relocation_taint_le next (step_taint inst s post tn) (step_taint inst t tpost un)
Proof
  strip_tac >> irule clean_copy_taint_order >> simp[] >>
  (conj_tac >- fs[MEM]) >>
  goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  qexistsl_tac [`w2n dst`, `w2n dstT`, `w2n sz`, `xs`] >>
  fs[MEM] >> simp[step_writes_def, source_memory_write_ranges_def,
    sized_source_write_range_def] >> metis_tac[]
QED

Theorem concretize_calldatacopy_local_complete:
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
  MEM inst.inst_opcode [CALLDATACOPY;CODECOPY;DLOADBYTES] /\ inst.inst_operands = [opd;ops;opn] /\
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
    (qpat_x_assum `inst_wf inst` mp_tac >> fs[MEM] >> simp[inst_wf_def, opcode_case_def]) >>
  drule_all concretize_calldatacopy_execution_geometry >> strip_tac >>
  qmatch_asmsub_abbrev_tac `post = write_memory_with_expansion (w2n dst) xs s` >>
  `LENGTH xs = w2n sz` by
    (simp[Abbr `xs`, LENGTH_TAKE_EQ, LENGTH_APPEND]) >>
  qexists_tac `write_memory_with_expansion (w2n dstT) xs t` >>
  asm_rewrite_tac[] >> (conj_tac >- suspend "relation") >>
  (conj_tac >- (irule (cj 1 calldatacopy_ghosts) >> simp[] >> metis_tac[])) >>
  (conj_tac >- (irule calldatacopy_taint_order >> simp[] >>
    goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >> metis_tac[])) >>
  gvs[] >> fs[relocation_env_def, relocation_reader_context_def,
              write_memory_with_expansion_def]
QED
Resume concretize_calldatacopy_local_complete[relation]:
  `(guarded_bytes (retpc_var fn) rv (step_taint inst s post tn) :
     string -> bytes32 -> bytes32 -> bool) =
   guarded_bytes (retpc_var fn) rv tn` by
    (irule EQ_EXT >> gen_tac >> irule EQ_EXT >> gen_tac >> irule EQ_EXT >> gen_tac >>
     simp[guarded_bytes_def, frameRelocationGhostCopyTheory.copy_bytes_def,
          op_taint_def, step_taint_def, set_var_taint_def, DRESTRICT_UNIV]) >>
  asm_rewrite_tac[] >> gvs[] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) local_rel_write_memory >>
  disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >> (conj_tac >- metis_tac[]) >>
  fs[local_rel_def, write_memory_with_expansion_def, dead_result_rel_memory_frame]
QED
Finalise concretize_calldatacopy_local_complete

val _ = if null (hyp concretize_calldatacopy_local_complete) then ()
        else raise Fail "complete calldata copy export has hypotheses";
