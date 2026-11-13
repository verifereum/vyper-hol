Theory concretizeLayoutStoreProduction
Ancestors concretizeLayoutAccessGeometry concretizeLayoutLoadProduction concretizeLayoutPointerRanges frameActivationSeparation
  frameJointDemand venomState byte
  frameActivationCache frameRelocationBinding frameJointTrace frameJointTransition
  frameRelocationOpaque frameRelocationStoreValues frameRelocationStoreSteps frameRelocationWriteCoverage
  frameRelocationReachableSupport concretizeLayoutRelocation
  frameRelocationMemoryAccess frameRelocationMemoryOpaque frameRelocationCleanOperands
  frameResolvedTrace frameActivationLookup frameActivationLifetime frameOriginReachable
  frameOriginHistory memLocDefs ptrDiscipline o1PassContract unitMemInv
  contextCodegenRel finiteByteDemand codegenRel venomWf venomInst concretizePtrParamSupport
  venomExecSemantics venomMemProps frameOriginCache finite_map list words pred_set

Theorem coherent_written_interval:
  (!a z w. D a z /\ R a w ==> z = w) /\
  (!i:num. i < len ==> R (dst+i) (dstT+i)) ==>
  !a z. D a z /\ dst <= a /\ a < dst+len ==>
    dstT <= z /\ z < dstT+len /\ a-dst = z-dstT
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `a = dst+(a-dst) /\ a-dst < len` by decide_tac >>
  `R a (dstT+(a-dst))` by metis_tac[] >>
  `z = dstT+(a-dst)` by metis_tac[] >> decide_tac
QED

Theorem joint_mstore_demand_address_coherence:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\ post.vs_allocas = s.vs_allocas /\
  joint_relocation_demand lo positions q0 es qs (SUC c) a z /\
  relocation_pair lo positions (EL c (q0::qs)) a w ==> z = w
Proof
  strip_tac >>
  drule_all joint_trace_edge_at >> strip_tac >>
  `!d owner aid site.
    activation_cache (EL c (q0::qs)) d owner aid site ==>
    activation_cache (EL (SUC c) (q0::qs)) d owner aid site` by
    (gvs[joint_transition_ordinary, activation_cache_def]) >>
  gvs[joint_relocation_demand_def, relocation_pair_def] >>
  `activation_cache (EL c qs) d'' owner'' aid'' (b'',sz'')` by
    metis_tac[] >>
  `d = d'' /\ owner = owner'' /\ aid = aid'' /\ b = b'' /\ sz = sz''` by
    (irule joint_activation_cache_byte_unique >>
     conj_tac >- (qexists_tac `a` >> simp[]) >>
     qexistsl_tac [`C`, `EL c qs`, `vs0`] >> simp[]) >> gvs[]
QED

val _ = if null (hyp joint_mstore_demand_address_coherence) then ()
        else raise Fail "store coherence export has hypotheses";

val _ = if null (hyp joint_relocation_demand_mstore_value_byte) then ()
        else raise Fail "value byte export has hypotheses";

Theorem concretize_mstore_execution_geometry:
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
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  ?dstT valueT tpost Q. eval_operand opd t = SOME dstT /\
    eval_operand opv t = SOME valueT /\ step_inst_base inst t = OK tpost /\
    tpost = mstore (w2n dstT) valueT t /\ post = mstore (w2n dst) value s /\
    fn_ptr_ok Q fn /\ (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv Q fn) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+32 ==>
      w2n dstT <= z /\ z < w2n dstT+32 /\ a-w2n dst = z-w2n dstT) /\
    (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+32) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+32))
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
  `~in_revert_forward fn s` by fs[joint_read_exempt_def] >>
  `post = mstore (w2n dst) value s` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def, step_inst_base_def, exec_write2_def] >>
     metis_tac[]) >>
  `?Q. fn_ptr_ok Q fn /\ (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv Q fn)` by
    suspend "support" >>
  pop_assum strip_assume_tac >>
  `?valueT. eval_operand opv t = SOME valueT` by suspend "value" >>
  pop_assum strip_assume_tac >>
  `?dstT. eval_operand opd t = SOME dstT /\
    ((w2n dst+32 <= lo /\ w2n dstT = w2n dst) \/
     (?d owner aid b sz.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,sz) /\ lo <= b /\ b <= w2n dst /\
       w2n dst+32 <= b+sz /\
       w2n dstT = concretize_positions C' owner aid + (w2n dst-b)))` by
    suspend "address" >>
  pop_assum strip_assume_tac >>
  `(!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      w2n dst <= a /\ a < w2n dst+32 ==>
      w2n dstT <= z /\ z < w2n dstT+32 /\ a-w2n dst = z-w2n dstT) /\
   (!a z. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a z /\
      ~(w2n dst <= a /\ a < w2n dst+32) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a z /\
      ~(w2n dstT <= z /\ z < w2n dstT+32))` by suspend "memory" >>
  qexistsl_tac [`dstT`, `valueT`, `Q`] >> asm_rewrite_tac[] >>
  (conj_tac >- simp[step_inst_base_def, exec_write2_def]) >>
  qpat_x_assum `!a z. _ /\ ~_ ==> _` mp_tac >> simp[]
QED

Resume concretize_mstore_execution_geometry[support]:
  `?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  qexists_tac `Q` >> conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[resolved_static_support]
QED
Resume concretize_mstore_execution_geometry[value]:
  `!v. opv = Var v ==> ~retpc_var fn v /\ FLOOKUP rv v = NONE` by
    (rpt strip_tac
     >- (spose_not_then assume_tac >>
         `MEM (Var v) inst.inst_operands` by simp[] >>
         drule_all disciplined_retpc_operand_use >> simp[]) >>
     drule_all mstore_value_origin_free >> simp[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_masked_operand >>
  disch_then drule_all >> metis_tac[]
QED
Resume concretize_mstore_execution_geometry[address]:
  irule concretize_memory_access_geometry >> simp[] >>
  conj_tac
  >- (qexists_tac `<| iao_ofst := opd; iao_size := SOME (Lit 32w);
                    iao_max_size := SOME (Lit 32w) |>` >>
      simp[source_memory_write_ranges_def, fixed_source_write_range_def,
           mem_write_ops_def]) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED
Resume concretize_mstore_execution_geometry[memory]:
  markerLib.RESUME_TAC >> (all_tac >>
  `(!i. i < 32 ==>
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
    range_bytes [(w2n dst,32)] /\ step_writes inst t t = [(w2n dstT,32)]` by
    (`step_writes inst s post = [(w2n dst,32)] /\
      step_writes inst t t = [(w2n dstT,32)]` by
       (conj_tac >> irule step_writes_store >> metis_tac[]) >>
     fs[joint_writes_ordinary] >> metis_tac[]) >>
  conj_tac
  >- (ho_match_mp_tac (Q.INST
        [`R` |-> `relocation_pair lo (concretize_positions C') (EL c (q0::qs))`]
        coherent_written_interval) >>
      conj_tac
      >- (rpt strip_tac >> irule joint_mstore_demand_address_coherence >>
          `post.vs_allocas = s.vs_allocas` by simp[mstore_def] >> metis_tac[]) >>
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
Finalise concretize_mstore_execution_geometry

val _ = if null (hyp concretize_mstore_execution_geometry) then ()
        else raise Fail "store execution export has hypotheses";

Theorem concretize_mstore_demand_execution:
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
  inst.inst_opcode = MSTORE /\ inst.inst_operands = [opd;opv] /\
  eval_operand opd s = SOME dst /\ eval_operand opv s = SOME value ==>
  ?dstT valueT tpost. eval_operand opd t = SOME dstT /\
    eval_operand opv t = SOME valueT /\ step_inst_base inst t = OK tpost /\
    tpost = mstore (w2n dstT) valueT t /\ post = mstore (w2n dst) value s /\
    demand_agree (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\a. read_byte a post.vs_memory) (\z. read_byte z tpost.vs_memory)
Proof
  strip_tac >>
  drule_all concretize_mstore_execution_geometry >> strip_tac >>
  qexistsl_tac [`dstT`, `valueT`, `tpost`] >> asm_rewrite_tac[] >>
  `demand_agree (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
     (\a. read_byte a (write_memory_with_expansion (w2n dst) (word_to_bytes value T) s).vs_memory)
     (\z. read_byte z (write_memory_with_expansion (w2n dstT) (word_to_bytes valueT T) t).vs_memory)`
    suffices_by simp[mstore_def, write_memory_with_expansion_def] >>
  irule demand_agree_write_memory >> simp[LENGTH_word_to_bytes] >> conj_tac
  >- (rpt strip_tac >>
      `w2n dstT <= b /\ b < w2n dstT+32 /\ a-w2n dst = b-w2n dstT` by metis_tac[] >>
      `a = w2n dst+(a-w2n dst) /\ a-w2n dst < 32` by decide_tac >>
      `joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c)
         (w2n dst+(a-w2n dst)) b` by metis_tac[] >>
      qpat_x_assum `fn_ptr_ok P fn` kall_tac >>
      drule_at (Pat `local_rel _ _ _ _ _ _ _`)
        (INST_TYPE [``:'a`` |-> ``:num#num``, ``:'b`` |-> ``:num``]
          joint_relocation_demand_mstore_value_byte) >>
      disch_then drule_all >> simp[]) >>
  qexists_tac `joint_relocation_demand lo (concretize_positions C') q0 es qs c` >>
  reverse conj_tac >- metis_tac[frameRelocationLocalTheory.local_rel_demand] >>
  rpt strip_tac >> metis_tac[]
QED

val _ = if null (hyp concretize_mstore_demand_execution) then ()
        else raise Fail "store execution export has hypotheses";
