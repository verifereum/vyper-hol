Theory concretizeLayoutExternalCreate
Ancestors concretizeLayoutCutSafe concretizeLayoutExternalRequests concretizeLayoutSupplement
  lowerDloadPtrCreateInterfaces lowerDloadPtrScalar
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

Theorem concretize_clean_create_completion:
  concretize_local_obs s t /\ concretize_supplement D tn s t /\ s.vs_outcomes <> [] /\
  request_agree_except D (venom_create_request s value off sz salt)
    (venom_create_request t value offT sz salt) /\
  consume_create_outcome (venom_create_request s value off sz salt) s = (w,post) /\
  consume_create_outcome (venom_create_request t value offT sz salt) t = (w',post') ==>
  w = w' /\ concretize_local_obs post post' /\
  concretize_supplement D (tn with <|t_stor := Mst; t_trans := Mtr|>) post post' /\
  post.vs_vars = s.vs_vars /\ post'.vs_vars = t.vs_vars /\
  post.vs_memory = s.vs_memory /\ post'.vs_memory = t.vs_memory
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
  drule_all dload_consume_create_world >> disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
  `LIST_REL (request_agree_except D)
     (record_request (venom_create_request s value off sz salt) s.vs_requests)
     (record_request (venom_create_request t value offT sz salt) t.vs_requests)` by
    (irule request_agree_record_request >> fs[concretize_supplement_def]) >>
  qabbrev_tac `M = <|d_stor := K (K UNIV); d_trans := K (K UNIV);
                     d_imm := K UNIV; d_ret := K {}|>` >>
  `LIST_REL (request_agree_except M) s.vs_requests t.vs_requests` by
    fs[Abbr `M`, concretize_local_obs_def, dead_result_rel_def] >>
  `request_agree_except M (venom_create_request s value off sz salt)
      (venom_create_request t value offT sz salt)` by
    fs[Abbr `M`, request_agree_except_def, accounts_agree_except_def,
       transient_agree_except_def, storage_agree_except_def, key_taint_def,
       word_agree_except_def, Excl "consume_create_outcome_eq"] >>
  `LIST_REL (request_agree_except M)
     (record_request (venom_create_request s value off sz salt) s.vs_requests)
     (record_request (venom_create_request t value offT sz salt) t.vs_requests)` by
    metis_tac[request_agree_record_request] >>
  `post.vs_logs = post'.vs_logs /\ post.vs_pending_deletions = post'.vs_pending_deletions` by
    fs[concretize_local_obs_def, dead_result_rel_def, Excl "consume_create_outcome_eq"] >>
  qpat_assum `consume_create_outcome _ s = _`
    (fn th => once_rewrite_tac[MATCH_MP dload_consume_create_state th]) >>
  qpat_assum `consume_create_outcome _ t = _`
    (fn th => once_rewrite_tac[MATCH_MP dload_consume_create_state th]) >>
  fs[Abbr `M`, concretize_local_obs_def, dead_result_rel_def, concretize_supplement_def,
     accounts_agree_except_def, transient_agree_except_def,
     storage_agree_except_def, word_agree_except_def, Excl "consume_create_outcome_eq"]
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
  s.vs_call_ctx = t.vs_call_ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
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
  strip_tac >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [dload_exec_create_success_iff]) >>
  `request_agree_except D (venom_create_request s value off sz salt)
     (venom_create_request t value offT sz salt)` by
    (irule concretize_request_observation >> simp[venom_create_request_def] >>
     metis_tac[]) >>
  Cases_on `consume_create_outcome (venom_create_request t value offT sz salt) t` >>
  rename1 `consume_create_outcome _ t = (wT,pT)` >>
  drule_all concretize_clean_create_completion >>
  disch_then (qspecl_then [`if s.vs_call_ctx.cc_static then tn.t_trans else {}`,
    `if s.vs_call_ctx.cc_static then tn.t_stor else {}`] strip_assume_tac) >>
  qpat_x_assum `w = wT` (SUBST_ALL_TAC o SYM) >>
  rename1 `consume_create_outcome _ s = (w,p)` >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >>
  `t.vs_outcomes <> []` by
    metis_tac[concretize_supplement_def] >>
  qexists_tac `update_var out w pT` >> conj_tac
  >- (pure_rewrite_tac[dload_exec_create_success_iff] >>
      qexistsl_tac [`out`,`w`,`pT`] >>
      fs[concretize_supplement_def, Excl "consume_create_outcome_eq"]) >>
  conj_tac
  >- gvs[concretize_local_obs_def, dead_result_rel_def, update_var_def,
          Excl "consume_create_outcome_eq"] >>
  conj_tac
  >- (`step_taint inst s (update_var out w p) tn =
        tn with <|t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s);
          t_stor := if s.vs_call_ctx.cc_static then tn.t_stor else {};
          t_trans := if s.vs_call_ctx.cc_static then tn.t_trans else {}|>` by
        (irule dload_create_taint_after_consume >>
         qpat_assum `consume_create_outcome _ s = _` (irule_at Any) >>
         simp[Excl "consume_create_outcome_eq"]) >>
      simp[Excl "consume_create_outcome_eq"] >>
      irule concretize_supplement_update_var >>
      qpat_assum `s.vs_call_ctx = t.vs_call_ctx` (fn th =>
        fs[th, concretize_supplement_def, Excl "consume_create_outcome_eq"])) >>
  simp[update_var_def] >> qexists_tac `w` >> simp[]
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
  concretize_supplement D tn s t /\ s.vs_call_ctx = t.vs_call_ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
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

Theorem create_scalar_agreement:
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
  ~s.vs_call_ctx.cc_static /\ exec_create inst s value off sz salt = OK post ==>
  step_taint inst s post tn =
    tn with <|t_var := tn.t_var |+ (v,{}); t_stor := {}; t_trans := {}|>
Proof
  strip_tac >>
  `out_taint tn inst s = {}` by
    (irule out_taint_opcode_exclusion >> fs[MEM]) >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [dload_exec_create_success_iff]) >>
  `out = v` by metis_tac[listTheory.CONS_11] >>
  qpat_x_assum `out = v` SUBST_ALL_TAC >>
  qpat_assum `consume_create_outcome _ s = _`
    (mp_then (Pat `consume_create_outcome _ _ = _`) mp_tac
      dload_create_taint_after_consume) >>
  disch_then (qspecl_then [`tn`,`v`,`inst`] mp_tac) >>
  simp[set_var_taint_def, Excl "consume_create_outcome_eq"]
QED

Theorem concretize_create_local_complete_headroom_static:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0) /\
  EVERY wf_function C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ layout_cut_safe D lo ncut vs0 C q /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  (~ctx_has_dalloca C ==> resolved_complete (EL c (q0::qs)) ((rp,rv)::anns)) /\
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
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gnvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by metis_tac[layout_cut_safe_ptr_edge, layout_cut_safe_ptr_at, layout_cut_safe_ptr_cfg] >>
  `step_inst_base inst s = OK post` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def] >> fs[MEM]) >>
  drule_all (SRULE [MEM] create_base_envelope) >> strip_tac >> (
  `s.vs_labels = t.vs_labels /\ s.vs_call_ctx = t.vs_call_ctx` by fs[relocation_env_def] >>
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
    (irule concretize_read_demand_geometry_headroom_static >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def] >> metis_tac[]) >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t` by
    suspend "read" >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
     (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
     (s.vs_transient s.vs_call_ctx.cc_address)` by
    (`active_inst fn inst s` by
       (fs[joint_config_reachable_def] >>
        metis_tac[joint_origin_history_projection, frameHistoryDefinitionsTheory.frame_history_active]) >>
     `gas_cut ncut vs0 s` by
       metis_tac[layout_cut_safe_edge_frame, layout_cut_safe_frame, layout_cut_safe_frame_cfg] >>
     `taint_within_upto D ncut C vs0` by fs[layout_cut_safe_def] >>
     `inst.inst_opcode <> INVOKE` by fs[MEM] >>
     `step_inst 0 C inst s = OK post` by gvs[step_inst_non_invoke] >>
     `LENGTH s.vs_requests < LENGTH post.vs_requests` by
       (irule ld_create_step_request_growth >> fs[MEM] >> metis_tac[]) >>
     drule_all taint_within_upto_request >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     simp[joint_writes_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >> fs[MEM] >> metis_tac[]) >>
  drule_all (SRULE [MEM] concretize_create_local_execution) >> strip_tac >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  (conj_tac >- suspend "target") >>
  (conj_tac >- suspend "taint") >>
  suspend "environment")
QED
Resume concretize_create_local_complete_headroom_static[read]:
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
Resume concretize_create_local_complete_headroom_static[target]:
  markerLib.RESUME_TAC >> (pure_once_rewrite_tac[step_inst_base_def] >>
  `~t.vs_call_ctx.cc_static` by (fs[relocation_env_def] >> metis_tac[]) >>
  gvs[MEM] >> simp[] >> metis_tac[listTheory.MEM])
QED
Resume concretize_create_local_complete_headroom_static[environment]:
  markerLib.RESUME_TAC >> (drule create_execution_fields >> strip_tac >>
  rev_drule create_execution_fields >> strip_tac >>
  fs[relocation_env_def, relocation_reader_context_def])
QED
Resume concretize_create_local_complete_headroom_static[taint]:
  markerLib.RESUME_TAC >> (
  drule create_execution_fields >> strip_tac >>
  rev_drule create_execution_fields >> strip_tac >> gvs[] >>
  `~t.vs_call_ctx.cc_static` by fs[relocation_env_def] >>
  `step_taint inst s post tn =
    tn with <|t_var := tn.t_var |+ (out,{}); t_stor := {}; t_trans := {}|>` by
    (irule create_ghosts >> simp[MEM] >> metis_tac[]) >>
  `step_taint inst t post' un =
    un with <|t_var := un.t_var |+ (out,{}); t_stor := {}; t_trans := {}|>` by
    (irule create_ghosts >> simp[MEM] >> metis_tac[]) >>
  qpat_x_assum `relocation_taint_le _ tn un` mp_tac >>
  simp[relocation_taint_le_def, op_taint_def, FLOOKUP_UPDATE] >>
  strip_tac >> conj_tac
  >- (qpat_x_assum `demand_taint _ _ _` mp_tac >>
      qpat_x_assum `!a b. joint_relocation_demand _ _ _ _ _ (SUC c) a b ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[demand_taint_def] >> metis_tac[]) >>
  gen_tac >> IF_CASES_TAC >> fs[])
QED
Finalise concretize_create_local_complete_headroom_static

Theorem concretize_create_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ layout_cut_safe D lo ncut vs0 C q /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  (~ctx_has_dalloca C ==> resolved_complete (EL c (q0::qs)) ((rp,rv)::anns)) /\
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
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL concretize_create_local_complete_headroom_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED

val _ = export_theory();
