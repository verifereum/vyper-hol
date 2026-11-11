Theory concretizeLayoutIstoreProduction
Ancestors concretizeLayoutStoreProduction frameRelocationStoreTaint frameRelocationStoreSteps
  frameRelocationBinding frameJointTrace frameJointTransition frameJointTaint
  frameRelocationMemory frameRelocationCopyTaint frameRelocationTaintOrder ptrDiscipline
  frameRelocationStoreValues frameRelocationReachableSupport frameResolvedTrace
  frameRelocationOpaque frameRelocationGuardedValues frameOriginReachable frameOriginHistory
  concretizePtrParamSupport o1PassContract venomWf venomInst
  venomExecSemantics venomState codegenRel finiteByteDemand byte finite_map pred_set list words

Theorem step_taint_istore_mem:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  post = istore (w2n dst) value s ==>
  (a IN (step_taint inst s post tn).t_mem <=>
   (a IN tn.t_mem /\ ~(w2n dst <= a /\ a < w2n dst+32)) \/
   ?k. k IN op_taint tn opv /\ a = w2n dst+k)
Proof
  strip_tac >>
  `new_site_bytes s post = {}` by
    (irule new_site_bytes_unchanged >>
     simp[istore_def, mstore_def, write_memory_with_expansion_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       fixed_source_write_range_def] >> metis_tac[]
QED

Theorem joint_relocation_demand_istore_lane_clean:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  k < 32 /\
  joint_relocation_demand lo positions q0 es qs (SUC c) (w2n dst+k) z ==>
  k NOTIN op_taint tn opv
Proof
  strip_tac >>
  `w2n dst+k NOTIN joint_mem_taint (EL (SUC c) (q0::qs))` by
    (irule joint_relocation_demand_clean >> metis_tac[]) >>
  drule_all joint_trace_edge_at >> strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >>
  `post = istore (w2n dst) value s` by
    gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  `w2n dst+k NOTIN (step_taint inst s post tn).t_mem` by
    gvs[joint_mem_taint_def] >>
  drule_all step_taint_istore_mem >>
  disch_then (qspecl_then [`tn`, `w2n dst+k`] mp_tac) >> metis_tac[]
QED

Theorem istore_access_fixed[local]:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  op_prov G opd = NONE /\ 
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  w2n dst + 32 <= lo
Proof
  strip_tac >>
  fs[access_ok_def, source_memory_write_ranges_def,
     fixed_source_write_range_def, memLocDefsTheory.mem_write_ops_def] >>
  spose_not_then assume_tac >>
  qpat_x_assum `!off len. _ ==> ?v b sz. _` (qspecl_then [`w2n dst`, `32`] mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[op_prov_def]
QED

Theorem concretize_istore_demand_geometry:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  fixed_region_reserved lo C /\ vs0.vs_allocas = FEMPTY /\
  joint_trace vs0 C q0 es qs q /\ activation_depth q0 = 0 /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  post = istore (w2n dst) value s /\ w2n dst + 32 <= lo ==>
  (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
     w2n dst <= a /\ a < w2n dst+32 ==> z = a) /\
  (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
     ~(w2n dst <= a /\ a < w2n dst+32) ==>
     joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
     ~(w2n dst <= z /\ z < w2n dst+32))
Proof
  strip_tac >>
  `joint_writes (EL c (q0::qs)) (EL c es) = range_bytes [(w2n dst,32)]` by
    simp[frameJointDemandTheory.joint_writes_ordinary, step_writes_def,
         source_memory_write_ranges_def, fixed_source_write_range_def] >>
  conj_tac
  >- (rpt strip_tac >> irule joint_mstore_demand_address_coherence >>
      `post.vs_allocas = s.vs_allocas` by
        simp[istore_def, mstore_def, write_memory_with_expansion_def] >>
      `relocation_pair lo (concretize_positions C') (EL c (q0::qs)) a a` by
        (simp[relocation_pair_def] >> decide_tac) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `a NOTIN joint_writes (EL c (q0::qs)) (EL c es)` by
    (simp[range_bytes_def] >> decide_tac) >>
  `joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
   z NOTIN range_bytes [(w2n dst,32)]` by
    (irule concretizeLayoutRelocationTheory.concretize_positions_demand_write_complement >>
     conj_tac
     >- (rpt strip_tac >> qexists_tac `w` >> simp[] >>
         simp[relocation_pair_def] >> fs[range_bytes_def] >> decide_tac) >>
     simp[] >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >> simp[] >> metis_tac[]) >>
  fs[range_bytes_def] >> decide_tac
QED

Theorem istore_demand_write:
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  post = istore (w2n dst) value s /\
  word_agree_except (op_taint tn opv) value valueT /\
  demand_agree R (\a. read_byte a s.vs_memory) (\z. read_byte z t.vs_memory) /\
  (!a z. joint_relocation_demand lo positions q0 es qs (SUC c) a z /\
     w2n dst <= a /\ a < w2n dst+32 ==> z = a) /\
  (!a z. joint_relocation_demand lo positions q0 es qs (SUC c) a z /\
     ~(w2n dst <= a /\ a < w2n dst+32) ==>
     R a z /\ ~(w2n dst <= z /\ z < w2n dst+32)) ==>
  demand_agree (joint_relocation_demand lo positions q0 es qs (SUC c))
    (\a. read_byte a post.vs_memory)
    (\z. read_byte z (istore (w2n dst) valueT t).vs_memory)
Proof
  strip_tac >>
  `demand_agree (joint_relocation_demand lo positions q0 es qs (SUC c))
    (\a. read_byte a (write_memory_with_expansion (w2n dst) (word_to_bytes value T) s).vs_memory)
    (\z. read_byte z (write_memory_with_expansion (w2n dst) (word_to_bytes valueT T) t).vs_memory)`
    suffices_by simp[istore_def, mstore_def, write_memory_with_expansion_def] >>
  irule demand_agree_write_memory >> simp[LENGTH_word_to_bytes] >> conj_tac
  >- (rpt strip_tac >>
      `b = a` by metis_tac[] >> gvs[] >>
      `a = w2n dst + (a-w2n dst) /\ a-w2n dst < 32` by decide_tac >>
      `a-w2n dst NOTIN op_taint tn opv` by
        (irule joint_relocation_demand_istore_lane_clean >>
         conj_tac >- decide_tac >>
         goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
         goal_assum (drule_at (Pat `EL _ (_::_) = _`)) >>
         goal_assum (drule_at (Pat `EL _ es = _`)) >>
         simp[] >> metis_tac[]) >>
      fs[word_agree_except_def]) >>
  qexists_tac `R` >> simp[] >> metis_tac[]
QED

Theorem concretize_istore_demand_execution:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) Obs s t /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  ?valueT. eval_operand opd t = SOME dst /\
    eval_operand opv t = SOME valueT /\
    step_inst_base inst t = OK (istore (w2n dst) valueT t) /\
    post = istore (w2n dst) value s /\ SND o_f rv = G /\
    op_prov G opd = NONE /\ w2n dst+32 <= lo /\
    word_agree_except (op_taint tn opv) value valueT /\
    demand_agree (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\a. read_byte a post.vs_memory)
      (\z. read_byte z (istore (w2n dst) valueT t).vs_memory)
Proof
  strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >> metis_tac[resolved_frame_erasure]) >>
  `?Q. fn_ptr_ok Q fn /\ (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv Q fn)` by
    suspend "support" >> pop_assum strip_assume_tac >>
  `!op v. MEM op inst.inst_operands /\ op = Var v ==>
      ~retpc_var fn v /\ FLOOKUP rv v = NONE` by suspend "origins" >>
  `op_prov G opd = NONE` by suspend "erasure" >>
  `eval_operand opd t = SOME dst` by suspend "address" >>
  `?valueT. eval_operand opv t = SOME valueT /\
    word_agree_except (op_taint tn opv) value valueT` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`)
       frameRelocationStoreValuesTheory.guarded_masked_operand >>
     disch_then (qspecl_then [`value`, `opv`] mp_tac) >>
     simp[] >> metis_tac[listTheory.MEM]) >>
  pop_assum strip_assume_tac >>
  `post = istore (w2n dst) value s` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_non_invoke,
          step_inst_base_def, exec_write2_def] >> metis_tac[]) >>
  `w2n dst+32 <= lo` by
    (irule istore_access_fixed >> fs[joint_read_exempt_def] >> metis_tac[]) >>
  `demand_agree (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\a. read_byte a s.vs_memory) (\z. read_byte z t.vs_memory)` by
    metis_tac[frameRelocationLocalTheory.local_rel_demand] >>
  drule_all concretize_istore_demand_geometry >> strip_tac >>
  drule_all istore_demand_write >> strip_tac >>
  qexists_tac `valueT` >> asm_rewrite_tac[] >>
  gvs[step_inst_base_def, exec_write2_def]
QED

Resume concretize_istore_demand_execution[support]:
  `?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  qexists_tac `Q` >> conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[resolved_static_support]
QED
Resume concretize_istore_demand_execution[origins]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      `MEM (Var v) inst.inst_operands` by metis_tac[] >>
      drule_all disciplined_retpc_operand_use >> simp[]) >>
  `v NOTIN fn_pv Q fn` by (fs[fn_ptr_ok_def] >> metis_tac[]) >> metis_tac[]
QED
Resume concretize_istore_demand_execution[erasure]:
  Cases_on `opd` >> gvs[op_prov_def] >>
  `FLOOKUP rv s' = NONE` by metis_tac[listTheory.MEM] >>
  simp[finite_mapTheory.FLOOKUP_o_f]
QED
Resume concretize_istore_demand_execution[address]:
  `op_taint tn opd = {}` by
    (fs[taint_ok_def] >> spose_not_then assume_tac >>
     first_x_assum (qspec_then `opd` mp_tac) >> simp[] >> metis_tac[]) >>
  `eval_operand opd s = eval_operand opd t` suffices_by simp[] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`)
    frameRelocationGuardedValuesTheory.guarded_scalar_operand >>
  disch_then (qspec_then `opd` mp_tac) >> simp[] >>
  disch_then irule >> rpt strip_tac >>
  simp[frameRelocationGuardedValuesTheory.clean_scalar_def] >>
  metis_tac[listTheory.MEM, op_taint_def]
QED
Finalise concretize_istore_demand_execution

Theorem demand_taint_istore:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value /\
  eval_operand opd t = SOME dst /\ eval_operand opv t = SOME valueT /\
  post = istore (w2n dst) value s /\
  relocation_taint_le R tn un /\ op_taint un opv SUBSET {k | k < 32} /\
  (!a z. next a z /\ w2n dst <= a /\ a < w2n dst+32 ==> z = a) /\
  (!a z. next a z /\ ~(w2n dst <= a /\ a < w2n dst+32) ==>
     R a z /\ ~(w2n dst <= z /\ z < w2n dst+32)) ==>
  demand_taint next (step_taint inst s post tn).t_mem
    (step_taint inst t (istore (w2n dst) valueT t) un).t_mem
Proof
  strip_tac >>
  `op_taint un opv SUBSET op_taint tn opv` by
    (Cases_on `opv` >> gvs[relocation_taint_le_def, op_taint_def]) >>
  `!i. i IN (step_taint inst s post tn).t_mem <=>
    (i IN tn.t_mem /\ ~(w2n dst <= i /\ i < w2n dst+32)) \/
    ?k. k IN op_taint tn opv /\ i = w2n dst+k` by
    (gen_tac >> irule step_taint_istore_mem >> metis_tac[]) >>
  `!i. i IN (step_taint inst t (istore (w2n dst) valueT t) un).t_mem <=>
    (i IN un.t_mem /\ ~(w2n dst <= i /\ i < w2n dst+32)) \/
    ?k. k IN op_taint un opv /\ i = w2n dst+k` by
    (gen_tac >> irule step_taint_istore_mem >> metis_tac[]) >>
  pure_rewrite_tac[demand_taint_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `w2n dst <= a /\ a < w2n dst+32`
  >- (`b = a` by metis_tac[] >> gvs[] >> fs[SUBSET_DEF] >> metis_tac[]) >>
  `R a b /\ ~(w2n dst <= b /\ b < w2n dst+32)` by metis_tac[] >>
  `!k. k IN op_taint un opv ==> k < 32` by fs[SUBSET_DEF] >>
  `!k. k IN op_taint un opv ==> b <> w2n dst+k` by
    (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[] >> decide_tac) >>
  fs[relocation_taint_le_def, demand_taint_def] >> metis_tac[]
QED
