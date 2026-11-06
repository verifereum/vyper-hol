Theory concretizeLayoutExternalCreate
Ancestors concretizeLayoutExternalRequests concretizeLayoutSupplement
  venomCallOracleDefs extCallOracle ptrDiscipline venomState venomExecSemantics
  venomInst list pred_set frameRelocationAllocationSteps frameRelocationGuardedValues
  frameOriginUpdates frameRelocationGhostCopy frameRelocationLocal finite_map
  frameRelocationCleanOperands o1PassContract pointerConfinedDefs memLocDefs
  concretizeLayoutLocalSha3 frameRelocationReachableSupport frameResolvedTrace
  frameOriginReachable frameOriginHistory frameJointTransition frameJointDemand
  frameJointTrace frameActivationLookup frameActivationLifetime
  concretizeLayoutReaderContext frameRelocationEnvironment contextCodegenRel words
  frameRelocationBinding frameRelocationDemand frameRelocationCleanValueSteps
  frameRelocationTaintOrder frameRelocationCopyTaint frameRelocationMemory

(* CREATE's clean-storage side condition makes the adopted external snapshot
   exact; immutable taint and historical request agreement are retained. *)
Theorem concretize_clean_create_completion:
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  consume_create_outcome rq s = (w,post) /\
  consume_create_outcome rq t = (w',post') ==>
  w = w' /\ concretize_local_obs post post' /\
  concretize_supplement D tn post post' /\
  post.vs_vars = s.vs_vars /\ post'.vs_vars = t.vs_vars /\
  post.vs_memory = s.vs_memory /\ post'.vs_memory = t.vs_memory
Proof
  strip_tac >> drule_all concretize_supplement_clean_accounts >> strip_tac >>
  `s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[concretize_local_obs_def, dead_result_rel_def] >>
  `request_agree_except D rq rq` by
    simp[request_agree_except_def, call_request_component_equality,
         accounts_agree_except_def, transient_agree_except_def,
         storage_agree_except_def, word_agree_except_def] >>
  `LIST_REL (request_agree_except D)
     (record_request rq s.vs_requests) (record_request rq t.vs_requests)` by
    (irule request_agree_record_request >> fs[concretize_supplement_def]) >>
  `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
  qpat_x_assum `consume_create_outcome rq s = _` mp_tac >>
  qpat_x_assum `consume_create_outcome rq t = _` mp_tac >>
  simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[] >>
  gvs[concretize_local_obs_def, dead_result_rel_def, concretize_supplement_def,
      accounts_agree_except_def, transient_agree_except_def,
      storage_agree_except_def, word_agree_except_def] >>
  irule request_agree_record_request >>
  simp[request_agree_except_def, call_request_component_equality,
       accounts_agree_except_def, transient_agree_except_def,
       storage_agree_except_def, word_agree_except_def]
QED

Theorem create_success_envelope[local]:
  exec_create inst s value off sz salt = OK post ==>
  ?out w p. inst.inst_outputs = [out] /\ ~(w2n sz > 2 * max_code_size) /\
    consume_create_outcome (venom_create_request s value off sz salt) s = (w,p) /\
    post = update_var out w p
Proof
  simp[exec_create_def, AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  strip_tac >> pairarg_tac >> gvs[Excl "consume_create_outcome_eq"] >> metis_tac[]
QED

Theorem concretize_create_observation:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  exec_create inst s value off sz salt = OK post ==>
  ?post'. exec_create inst t value offT sz salt = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    post.vs_memory = s.vs_memory /\ post'.vs_memory = t.vs_memory /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)
Proof
  strip_tac >> drule_all concretize_supplement_clean_accounts >> strip_tac >>
  `venom_create_request s value off sz salt =
   venom_create_request t value offT sz salt` by simp[venom_create_request_def] >>
  drule create_success_envelope >> strip_tac >>
  Cases_on `consume_create_outcome (venom_create_request s value off sz salt) t` >>
  rename1 `consume_create_outcome _ t = (wT,pT)` >>
  `(venom_create_request s value off sz salt).cr_accounts = s.vs_accounts /\
   (venom_create_request s value off sz salt).cr_tStorage = s.vs_transient` by
    simp[venom_create_request_def] >>
  drule_all concretize_clean_create_completion >> strip_tac >>
  gns[Excl "consume_create_outcome_eq"] >>
  qexists_tac `update_var out wT pT` >> conj_tac
  >- (simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
      qpat_x_assum `venom_create_request s _ _ _ _ = _`
        (fn th => rewrite_tac[GSYM th]) >>
      simp[Excl "consume_create_outcome_eq"]) >>
  conj_tac
  >- gvs[concretize_local_obs_def, dead_result_rel_def, update_var_def,
          Excl "consume_create_outcome_eq"] >>
  `concretize_supplement D tn (update_var out w p) (update_var out wT pT)` by
    metis_tac[concretize_supplement_update_var] >>
  (conj_tac >- gvs[concretize_supplement_def, step_taint_def, adopt_reset_def,
     store_taint_def, imm_taint_def, update_var_def, MEM,
     Excl "consume_create_outcome_eq"]) >>
  simp[update_var_def] >> qexists_tac `wT` >> simp[]
QED

Theorem concretize_create_abort_observation:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  exec_create inst s value off sz salt = Abort a post ==>
  ?post'. exec_create inst t value offT sz salt = Abort a post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post'
Proof
  pure_rewrite_tac[exec_create_abort_iff] >> strip_tac >>
  qexists_tac `halt_state (set_returndata [] t)` >>
  gvs[concretize_local_obs_def, dead_result_rel_def, concretize_supplement_def,
      halt_state_def, set_returndata_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def, MEM, Excl "consume_create_outcome_eq"]
QED

Theorem create_execution_fields:
  exec_create inst s value off sz salt = OK post ==>
  ?out w. inst.inst_outputs = [out] /\
    post.vs_vars = (update_var out w s).vs_vars /\
    post.vs_memory = s.vs_memory /\
    post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp /\
    post.vs_labels = s.vs_labels /\ post.vs_call_ctx = s.vs_call_ctx /\
    post.vs_gas_readings = s.vs_gas_readings /\
    post.vs_tx_ctx = s.vs_tx_ctx /\ post.vs_block_ctx = s.vs_block_ctx /\
    post.vs_prev_hashes = s.vs_prev_hashes /\
    post.vs_code = s.vs_code /\ post.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule create_success_envelope >> strip_tac >>
  qexistsl_tac [`out`,`w`] >>
  gvs[consume_create_outcome_eq, update_var_def]
QED

Theorem concretize_create_local_execution:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  concretize_supplement D tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  exec_create inst s value off sz salt = OK post /\
  (!a b. next a b ==> R a b) ==>
  ?post'. exec_create inst t value offT sz salt = OK post' /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes Opaque (origin_set rv inst.inst_outputs NONE) (step_taint inst s post tn))
      next concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post'
Proof
  strip_tac >>
  `concretize_local_obs s t` by metis_tac[local_rel_observation] >>
  drule_all concretize_create_observation >> strip_tac >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  `local_rel (\u. F) (guarded_ptr Opaque L rv)
     (guarded_bytes Opaque rv tn) R (\s t. T) s t` by
    (fs[local_rel_def]) >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [out] NONE))
     (guarded_bytes Opaque (origin_set rv [out] NONE) (step_taint inst s post tn))
     R (\s t. T) (update_var out w s) (update_var out w t)` by
    suspend "values" >>
  irule local_rel_field_frame >> simp[update_var_def] >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >> simp[update_var_def]
QED
Resume concretize_create_local_execution[values]:
  irule local_rel_update >> simp[] >>
  (conj_tac >- simp[guarded_bytes_def, frameRelocationGhostCopyTheory.copy_bytes_def,
    word_agree_except_def]) >>
  (conj_tac >- simp[guarded_ptr_def, copy_ptr_def, origin_set_lookup]) >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def,
    frameRelocationGhostCopyTheory.copy_bytes_def, origin_set_lookup,
    step_taint_def, set_var_taint_def, out_taint_def, MEM, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[op_taint_def, FLOOKUP_UPDATE]
QED
Finalise concretize_create_local_execution

Theorem create_scalar_agreement[local]:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  inst.inst_operands = opv::opd::opn::salts /\
  ((inst.inst_opcode = CREATE /\ salts = []) \/
   (inst.inst_opcode = CREATE2 /\ LENGTH salts = 1)) /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  !op. MEM op (opv::opn::salts) ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >> Cases_on `salts` >> gvs[] >> rpt strip_tac >>
  `!v. op = Var v ==> FLOOKUP rv v = NONE` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `v IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     qpat_x_assum `!v. _ ==> _` (qspec_then `v` mp_tac) >>
     simp[] >> Cases_on `opd = Var v` >> gvs[] >>
     Cases_on `opv = Var v` >> gvs[] >>
     Cases_on `opn = Var v` >> gvs[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
  disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >> (conj_tac >- metis_tac[]) >>
  qexists_tac `inst` >> simp[] >> fs[] >> metis_tac[]
QED

Theorem create_base_envelope[local]:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  step_inst_base inst s = OK post ==>
  ?opv opd opn salts value off sz salt.
    inst.inst_operands = opv::opd::opn::salts /\
    ((inst.inst_opcode = CREATE /\ salts = [] /\ salt = NONE) \/
     (inst.inst_opcode = CREATE2 /\
       ?ops w. salts = [ops] /\ salt = SOME w /\ eval_operand ops s = SOME w)) /\
    eval_operand opv s = SOME value /\ eval_operand opd s = SOME off /\
    eval_operand opn s = SOME sz /\ ~s.vs_call_ctx.cc_static /\
    exec_create inst s value off sz salt = OK post
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  fs[MEM] >> asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  rpt strip_tac >> gvs[eval_operands_def, Excl "consume_create_outcome_eq"] >>
  metis_tac[]
QED

Theorem create_read_clean[local]:
  taint_ok fn tn inst s /\ MEM inst.inst_opcode [CREATE; CREATE2] /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  !i. i < len ==> off+i NOTIN tn.t_mem
Proof
  simp[MEM] >> strip_tac >> fs[taint_ok_def, about_to_revert_def] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`off`,`len`,`off+i`] mp_tac) >> simp[]
QED


Theorem create_ghosts[local]:
  MEM inst.inst_opcode [CREATE; CREATE2] /\ inst.inst_outputs = [v] /\
  post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp /\
  (inst.inst_operands = [opv;opd;opn] \/
   inst.inst_operands = [opv;opd;opn;ops]) ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >>
  `new_site_bytes s post = {}` by
    (irule new_site_bytes_unchanged >> simp[]) >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def, origin_set_def,
       step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality,
       fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
  rpt conj_tac >> rpt gen_tac >>
  Cases_on `x = v` >> simp[]
QED

Theorem concretize_create_local_complete:
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
    concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  MEM inst.inst_opcode [CREATE; CREATE2] ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    step_prov PG G inst post = SND o_f (origin_set rv inst.inst_outputs NONE) /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gnvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `step_inst_base inst s = OK post` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def] >> fs[MEM]) >>
  drule_all (SRULE [MEM] create_base_envelope) >> strip_tac >> (
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!op. MEM op (opv::opn::salts) ==> eval_operand op s = eval_operand op t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) create_scalar_agreement >>
     disch_then assume_tac >> rpt strip_tac >> first_x_assum irule >>
     simp[] >>
     (conj_tac >- (qexists_tac `P` >> simp[])) >>
     (conj_tac >- (qexists_tac `C` >> simp[])) >>
     goal_assum (drule_at (Pat `_ .inst_operands = _`)) >> fs[]) >>
  `MEM (w2n off,w2n sz) (source_memory_read_ranges inst s)` by
    (gvs[source_memory_read_ranges_def, memory_range_of_operands_def]) >>
  `?offT. eval_operand opd t = SOME offT /\
     (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
       joint_relocation_demand lo (concretize_positions C') q0 es qs c
         (w2n off+i) (w2n offT+i))` by
    (irule concretize_read_demand_geometry >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def] >> metis_tac[]) >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t` by
    suspend "read" >>
  `tn.t_stor = {} /\ tn.t_trans = {}` by (fs[taint_ok_def] >> fs[MEM]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     simp[joint_writes_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >> fs[MEM] >> metis_tac[]) >>
  drule_all (SRULE [MEM] concretize_create_local_execution) >> strip_tac >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  (conj_tac >- suspend "target") >>
  (conj_tac >- suspend "ghosts") >>
  (conj_tac >- suspend "taint") >>
  suspend "environment")
QED
Resume concretize_create_local_complete[read]:
  markerLib.RESUME_TAC >> (simp[read_memory_def] >> irule listTheory.LIST_EQ >>
  simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP] >>
  qx_gen_tac `j` >> strip_tac >>
  `w2n off+j NOTIN tn.t_mem` by metis_tac[create_read_clean, MEM] >>
  `codegenRel$read_byte (w2n off+j) s.vs_memory =
   codegenRel$read_byte (w2n offT+j) t.vs_memory` by
    (drule local_rel_demand >> simp[demand_agree_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  fs[codegenRelTheory.read_byte_def] >> simp[EL_TAKE] >>
  Cases_on `w2n off+j < LENGTH s.vs_memory` >>
  Cases_on `w2n offT+j < LENGTH t.vs_memory` >>
  gvs[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2,
      LENGTH_DROP, rich_listTheory.EL_DROP, rich_listTheory.EL_REPLICATE])
QED
Resume concretize_create_local_complete[target]:
  markerLib.RESUME_TAC >> (pure_once_rewrite_tac[step_inst_base_def] >>
  `~t.vs_call_ctx.cc_static` by (fs[relocation_env_def] >> metis_tac[]) >>
  gvs[MEM] >> simp[] >> metis_tac[listTheory.MEM])
QED
Resume concretize_create_local_complete[environment]:
  markerLib.RESUME_TAC >> (drule create_execution_fields >> strip_tac >>
  rev_drule create_execution_fields >> strip_tac >>
  fs[relocation_env_def, relocation_reader_context_def])
QED
Resume concretize_create_local_complete[ghosts]:
  markerLib.RESUME_TAC >> (
  `SND o_f rv = G` by
    (drule resolved_config_current >> simp[] >>
     metis_tac[resolved_frame_erasure]) >>
  rev_drule create_execution_fields >> strip_tac >>
  qpat_x_assum `SND o_f rv = G` (fn th => rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[] >>
  irule (cj 1 create_ghosts) >> simp[MEM] >> metis_tac[])
QED
Resume concretize_create_local_complete[taint]:
  markerLib.RESUME_TAC >> (
  drule create_execution_fields >> strip_tac >>
  rev_drule create_execution_fields >> strip_tac >> gvs[] >>
  `step_taint inst s post tn = tn with t_var := tn.t_var |+ (out,{})` by
    (irule (cj 2 create_ghosts) >> simp[MEM] >> metis_tac[]) >>
  `step_taint inst t post' un = un with t_var := un.t_var |+ (out,{})` by
    (irule (cj 2 create_ghosts) >> simp[MEM] >> metis_tac[]) >>
  asm_rewrite_tac[] >> irule relocation_clean_write_taint >> metis_tac[])
QED
Finalise concretize_create_local_complete

val _ = List.app (fn th => if null (hyp th) then ()
                          else raise Fail "CREATE export has hypotheses")
  [concretize_clean_create_completion, concretize_create_observation,
   concretize_create_abort_observation, create_execution_fields,
   concretize_create_local_execution, concretize_create_local_complete];

val _ = export_theory();
