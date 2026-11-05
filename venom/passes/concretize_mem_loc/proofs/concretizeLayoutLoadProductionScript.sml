Theory concretizeLayoutLoadProduction
Ancestors concretizeLayoutPointerRanges frameRelocationBinding
  frameRelocationLoadSteps frameRelocationLocal frameJointDemand frameJointTaint
  frameRelocationMemoryAccess frameRelocationMemoryOpaque
  frameRelocationCleanOperands frameJointTrace frameJointTransition frameOriginReachable
  frameOriginHistory memLocDefs finiteByteDemand venomExecSemantics
  frameResolvedTrace frameActivationLookup frameActivationLifetime
  o1PassContract ptrDiscipline unitMemInv contextCodegenRel finite_map list pred_set words

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
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def, step_inst_base_def, exec_read1_def] >>
     metis_tac[]) >>
  `MEM (w2n dst,32) (source_memory_read_ranges inst s)` by
    simp[source_memory_read_ranges_def] >>
  `mem_read_ops inst = SOME <| iao_ofst := opd; iao_size := SOME (Lit 32w);
      iao_max_size := SOME (Lit 32w) |>` by simp[mem_read_ops_def] >>
  `((w2n dst + 32 <= lo /\
      (!u. opd = Var u ==> FLOOKUP rv u = NONE)) \/
     (?u tok b sz. opd = Var u /\ FLOOKUP rv u = SOME (tok,(b,sz)) /\
       b <= w2n dst /\ w2n dst + 32 <= b+sz))` by
    (drule_at (Pat `SND o_f _ = _`) resolved_memory_access >>
     disch_then drule >> simp[] >> strip_tac >>
     first_x_assum (qspecl_then
       [`<| iao_ofst := opd; iao_size := SOME (Lit 32w);
            iao_max_size := SOME (Lit 32w) |>`, `w2n dst`, `32`] mp_tac) >> simp[]) >>
  pop_assum strip_assume_tac
  >- ( `eval_operand opd s = eval_operand opd t` by
         (drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
          disch_then drule >> simp[] >> disch_then drule >> simp[] >>
          disch_then drule >> simp[]) >>
       qexists_tac `dst` >>
       `eval_operand opd t = SOME dst` by metis_tac[] >>
       simp[step_inst_base_def, exec_read1_def] >>
       drule_then assume_tac local_rel_demand >>
       irule demand_agree_mload >>
       goal_assum (drule_at (Pat `demand_agree _ _ _`)) >>
       rpt strip_tac >> irule joint_relocation_demand_current >> simp[] >>
       conj_tac
       >- (simp[joint_observed_read_def, joint_reads_def, joint_mem_taint_def,
                source_memory_read_ranges_def, range_bytes_def] >> gvs[]) >>
       simp[relocation_pair_def] >> decide_tac) >>
  `~retpc_var fn u` by
    (drule disciplined_memory_offset_not_retpc >>
     disch_then drule >> disch_then drule >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  PairCases_on `tok` >> gvs[] >>
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
  qexists_tac `y` >> simp[step_inst_base_def, exec_read1_def] >>
  drule_then assume_tac local_rel_demand >>
  irule demand_agree_mload >>
  goal_assum (drule_at (Pat `demand_agree _ _ _`)) >>
  rpt strip_tac >> irule joint_relocation_demand_current >> simp[] >>
  conj_tac
  >- (simp[joint_observed_read_def, joint_reads_def, joint_mem_taint_def,
           source_memory_read_ranges_def, range_bytes_def] >> gvs[]) >>
  simp[relocation_pair_def] >>
  qexistsl_tac [`d`, `owner`, `tok1`, `b`, `sz`] >> simp[] >> decide_tac
QED

val _ = List.app (fn th => if null (hyp th) then ()
                          else raise Fail "load production export has hypotheses")
  [frame_reachable_saved_allocas_from, joint_activation_cache_lower_bound,
   concretize_mload_demand_execution];
