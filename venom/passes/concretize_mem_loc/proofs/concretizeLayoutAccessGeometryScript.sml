Theory concretizeLayoutAccessGeometry
Ancestors concretizeLayoutPointerRanges frameRelocationBinding frameRelocationStoreValues
  frameRelocationMemoryAccess frameRelocationMemoryOpaque frameRelocationCleanOperands
  frameJointTrace frameJointTransition frameOriginReachable frameOriginHistory
  frameResolvedTrace frameActivationLookup frameActivationLifetime
  o1PassContract ptrDiscipline unitMemInv contextCodegenRel memLocDefs finite_map list pred_set words

Theorem frame_reachable_saved_allocas_from:
  !vs0 C stk PG G tn fn inst s.
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  ptr_discipline lo C vs0 ==>
  EVERY (\f. allocas_from lo f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt strip_tac >> gvs[] >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem joint_activation_cache_lower_bound:
  ptr_discipline lo C vs0 /\
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
    d owner aid (b,sz) ==> lo <= b
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `allocas_from lo s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  drule_all frame_reachable_saved_allocas_from >> strip_tac >>
  gvs[frameActivationCacheTheory.activation_cache_def]
  >- metis_tac[allocas_from_def] >>
  `LENGTH stk - SUC d < LENGTH stk` by decide_tac >>
  qpat_x_assum `EVERY _ stk` mp_tac >>
  rewrite_tac[EVERY_EL] >>
  disch_then (qspec_then `LENGTH stk - SUC d` mp_tac) >>
  simp[allocas_from_def] >> metis_tac[]
QED

Theorem memory_offset_taint_empty:
  taint_ok fn tn inst s /\
  (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) ==>
  op_taint tn ops.iao_ofst = {}
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[mem_write_ops_def, mem_read_ops_def, AllCaseEqs()] >>
  fs[taint_ok_def] >>
  spose_not_then assume_tac >>
  qmatch_asmsub_rename_tac `op_taint tn addr <> {}` >>
  qpat_x_assum `!op. _` (qspec_then `addr` mp_tac) >> simp[] >>
  metis_tac[MEM_REVERSE, MEM]
QED

Theorem concretize_memory_access_geometry:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  joint_trace vs0 C q0 es qs q /\ c <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
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
  len <> 0 /\ ops.iao_ofst = opd /\ eval_operand opd s = SOME off /\
  ((MEM (w2n off,len) (source_memory_write_ranges inst s) /\
    mem_write_ops inst = SOME ops) \/
   (MEM (w2n off,len) (source_memory_read_ranges inst s) /\
    mem_read_ops inst = SOME ops)) ==>
  ?offT. eval_operand opd t = SOME offT /\
    ((w2n off+len <= lo /\ w2n offT = w2n off) \/
     (?d owner aid b sz.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,sz) /\ lo <= b /\ b <= w2n off /\
       w2n off+len <= b+sz /\
       w2n offT = concretize_positions C' owner aid + (w2n off-b)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LENGTH es = LENGTH qs` by
    metis_tac[joint_trace_def, joint_chain_length] >>
  `joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h)` by
    (drule joint_trace_prefix_reachable >> rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `c` mp_tac) >> simp[]) >> gnvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >> metis_tac[resolved_frame_erasure]) >>
  `~in_revert_forward fn s` by fs[joint_read_exempt_def] >>
  `((w2n off+len <= lo /\ (!u. ops.iao_ofst = Var u ==> FLOOKUP rv u = NONE)) \/
    (?u tok b sz. ops.iao_ofst = Var u /\ FLOOKUP rv u = SOME (tok,(b,sz)) /\
      b <= w2n off /\ w2n off+len <= b+sz))` by
    (irule resolved_memory_access >> metis_tac[]) >>
  pop_assum strip_assume_tac
  >- (`op_taint tn ops.iao_ofst = {}` by
        (irule memory_offset_taint_empty >> metis_tac[]) >>
      `!v. ops.iao_ofst = Var v ==> ~retpc_var fn v /\ FLOOKUP rv v = NONE` by
        (rpt strip_tac >>
         metis_tac[disciplined_memory_offset_not_retpc]) >>
      drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_masked_operand >>
      disch_then drule_all >> strip_tac >> gvs[] >>
      `off = y` by metis_tac[frameRelocationGuardedValuesTheory.word_agree_except_empty] >>
      gvs[] >> qexists_tac `y` >> simp[]) >>
  `~retpc_var fn u` by
    (drule disciplined_memory_offset_not_retpc >>
     disch_then drule >> disch_then drule >>
     disch_then irule >> metis_tac[]) >>
  PairCases_on `tok` >> gvs[] >>
  `w2n off+len <= b+sz` by decide_tac >>
  drule_at (Pat `FLOOKUP _ _ = SOME _`) concretize_guarded_pointer_range >>
  disch_then drule_all >> strip_tac >>
  `?d owner.
    activation_cache (JointConfig stk PG (SND o_f rv) tn fn inst s oms om hs h)
      d owner tok1 (b,sz) /\
    activation_lookup (0:num) (concretize_positions C') (birth::ids)
      (fn::MAP (\f. f.cf_fn) stk) (tok0,tok1) =
      concretize_positions C' owner tok1` by
    metis_tac[resolved_activation_lookup] >>
  `lo <= b` by metis_tac[joint_activation_cache_lower_bound] >>
  qexists_tac `y` >> simp[] >>
  qexistsl_tac [`d`, `owner`, `tok1`, `b`, `sz`] >> simp[]
QED

val _ = List.app (fn th => if null (hyp th) then ()
                          else raise Fail "access geometry export has hypotheses")
  [frame_reachable_saved_allocas_from, joint_activation_cache_lower_bound,
   memory_offset_taint_empty, concretize_memory_access_geometry];
