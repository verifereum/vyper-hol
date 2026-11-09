Theory concretizeLayoutLocalSha3
Ancestors concretizeMemLocProofs concretizeLayoutAccessGeometry
  frameRelocationValues frameRelocationWriteCoverage frameJointTaint
  frameRelocationCleanValueSteps frameRelocationTaintOrder frameRelocationCopyTaint
  frameRelocationGuardedValues frameRelocationGhostCopy frameOriginUpdates
  venomState frameRelocationMemory
  concretizeLayoutPointerRanges frameRelocationCleanOperands
  frameRelocationReachableSupport frameRelocationBinding frameJointDemand
  frameRelocationEnvironment concretizeLayoutReaderContext frameResolvedTrace
  frameJointTrace frameJointTransition frameOriginReachable frameOriginHistory
  frameActivationLookup frameActivationLifetime frameRelocationLocal
  frameRelocationDemand frameRelocationMemoryAccess frameRelocationMemoryOpaque
  ptrDiscipline unitMemInv contextCodegenRel pointerConfinedDefs venomExecSemantics memLocDefs finite_map list pred_set words

(* Reuse the existing general padded-slice theorem rather than a SHA3 clone. *)
Theorem sha3_execution_envelope[local]:
  inst.inst_opcode = SHA3 /\ step_inst_base inst s = OK post ==>
  ?opd opn dst sz v.
    inst.inst_operands = [opd;opn] /\ inst.inst_outputs = [v] /\
    eval_operand opd s = SOME dst /\ eval_operand opn s = SOME sz /\
    post = update_var v
      (word_of_bytes T (0w:bytes32)
        (Keccak_256_w64 (TAKE (w2n sz)
          (DROP (w2n dst) s.vs_memory ++ REPLICATE (w2n sz) 0w)))) s
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem sha3_size_agreement[local]:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = SHA3 /\
  inst.inst_operands = [opd;opn] /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  eval_operand opn s = eval_operand opn t
Proof
  strip_tac >>
  `!v. opn = Var v ==> FLOOKUP rv v = NONE` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `v IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
     Cases_on `opd = Var v` >> gvs[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexists_tac `inst` >> simp[]
QED

Theorem sha3_read_clean[local]:
  taint_ok fn tn inst s /\ inst.inst_opcode = SHA3 /\
  inst.inst_operands = [opd;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand opn s = SOME sz ==>
  !i. i < w2n sz ==> w2n dst+i NOTIN tn.t_mem
Proof
  strip_tac >> fs[taint_ok_def, about_to_revert_def,
    source_memory_read_ranges_def, mem_read_ops_def,
    memory_range_of_operands_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `w2n dst+i` mp_tac) >> simp[]
QED

(* Read geometry is independent of width and of the consuming opcode. *)
Theorem concretize_read_demand_geometry:
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
  eval_operand opd s = SOME off /\
  mem_read_ops inst = SOME ops /\ ops.iao_ofst = opd /\
  MEM (w2n off,len) (source_memory_read_ranges inst s) ==>
  ?offT. eval_operand opd t = SOME offT /\
    (!i. i < len /\ w2n off+i NOTIN tn.t_mem ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c
        (w2n off+i) (w2n offT+i))
Proof
  strip_tac >> Cases_on `len = 0`
  >- (`variable_domains s t` by metis_tac[local_rel_domains] >>
      `?offT. eval_operand opd t = SOME offT` by
        (Cases_on `eval_operand opd t` >>
         metis_tac[operand_domain_agreement, optionTheory.NOT_SOME_NONE]) >>
      qexists_tac `offT` >> simp[]) >>
  `?offT. eval_operand opd t = SOME offT /\
    ((w2n off+len <= lo /\ w2n offT = w2n off) \/
     (?d owner aid b sz.
       activation_cache (JointConfig stk PG G tn fn inst s oms om hs h)
         d owner aid (b,sz) /\ lo <= b /\ b <= w2n off /\
       w2n off+len <= b+sz /\
       w2n offT = concretize_positions C' owner aid + (w2n off-b)))` by
    (irule concretize_memory_access_geometry >> simp[] >>
     conj_tac >- (qexists_tac `ops` >> simp[]) >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  `!i. i < len ==> relocation_pair lo (concretize_positions C')
      (EL c (q0::qs)) (w2n off+i) (w2n offT+i)` by
    (rpt strip_tac >> irule relocation_pair_range >> metis_tac[]) >>
  qexists_tac `offT` >> simp[] >> rpt strip_tac >>
  irule joint_relocation_demand_current >> simp[] >>
  (conj_tac
  >- (simp[joint_observed_read_def, joint_reads_def, joint_mem_taint_def,
           range_bytes_def] >>
       conj_tac >- (qexistsl_tac [`w2n off`, `len`] >> simp[]) >> metis_tac[])) >>
  qpat_x_assum `!i. i < len ==> relocation_pair _ _ _ _ _`
    (qspec_then `i` mp_tac) >> simp[arithmeticTheory.ADD_COMM]
QED

Theorem concretize_sha3_demand_execution:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
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
  inst.inst_opcode = SHA3 ==>
  ?v z. inst.inst_outputs = [v] /\ post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t)
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `step_inst_base inst s = OK post` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def]) >>
  drule_all sha3_execution_envelope >> strip_tac >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `eval_operand opn t = SOME sz` by metis_tac[sha3_size_agreement] >>
  `?dstT. eval_operand opd t = SOME dstT /\
     (!i. i < w2n sz /\ w2n dst+i NOTIN tn.t_mem ==>
       joint_relocation_demand lo (concretize_positions C') q0 es qs c
         (w2n dst+i) (w2n dstT+i))` by
    (irule concretize_read_demand_geometry >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def, source_memory_read_ranges_def,
          memory_range_of_operands_def] >> metis_tac[]) >>
  `TAKE (w2n sz) (DROP (w2n dst) s.vs_memory ++ REPLICATE (w2n sz) 0w) =
   TAKE (w2n sz) (DROP (w2n dstT) t.vs_memory ++ REPLICATE (w2n sz) 0w)` by
    (irule listTheory.LIST_EQ >>
     simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
     qx_gen_tac `j` >> strip_tac >>
     `w2n dst+j NOTIN tn.t_mem` by metis_tac[sha3_read_clean] >>
     `codegenRel$read_byte (w2n dst+j) s.vs_memory =
      codegenRel$read_byte (w2n dstT+j) t.vs_memory` by
       (drule local_rel_demand >> simp[demand_agree_def] >>
        metis_tac[arithmeticTheory.ADD_COMM]) >>
     fs[codegenRelTheory.read_byte_def] >>
     simp[EL_TAKE] >>
     Cases_on `w2n dst+j < LENGTH s.vs_memory` >>
     Cases_on `w2n dstT+j < LENGTH t.vs_memory` >>
     gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
         LENGTH_DROP, rich_listTheory.EL_DROP, rich_listTheory.EL_REPLICATE]) >>
  qexistsl_tac [`v`, `word_of_bytes T (0w:bytes32)
    (Keccak_256_w64 (TAKE (w2n sz)
      (DROP (w2n dst) s.vs_memory ++ REPLICATE (w2n sz) 0w)))`] >>
  simp[step_inst_base_def] >> metis_tac[]
QED

Theorem sha3_ghosts[local]:
  inst.inst_opcode = SHA3 /\ inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s (update_var v z s) tn =
    tn with t_var := tn.t_var |+ (v,{}) /\
  step_writes inst s post = []
Proof
  strip_tac >>
  `new_site_bytes s (update_var v z s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
       step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality,
       fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  rpt conj_tac >> rpt gen_tac >> rpt CASE_TAC >> simp[]
QED

Theorem concretize_sha3_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
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
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  inst.inst_opcode = SHA3 ==>
  ?v tpost. inst.inst_outputs = [v] /\ step_inst_base inst t = OK tpost /\
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
  drule_all concretize_sha3_demand_execution >> strip_tac >>
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >>
     metis_tac[resolved_frame_erasure]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     simp[joint_writes_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >>
     metis_tac[]) >>
  qexistsl_tac [`v`, `update_var v z t`] >> simp[] >> gvs[] >>
  simp[sha3_ghosts] >>
  conj_tac
  >- (irule guarded_clean_write_restrict >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (irule relocation_clean_write_taint >> metis_tac[]) >>
  fs[relocation_env_def, relocation_reader_context_def, update_var_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
                          else raise Fail "SHA3 export has hypotheses")
  [concretize_read_demand_geometry, concretize_sha3_demand_execution,
   concretize_sha3_local_complete];
