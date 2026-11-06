Theory concretizeLayoutExternalCreate
Ancestors concretizeLayoutExternalRequests concretizeLayoutSupplement
  venomCallOracleDefs extCallOracle ptrDiscipline venomState venomExecSemantics
  venomInst list pred_set frameRelocationAllocationSteps frameRelocationGuardedValues
  frameOriginUpdates frameRelocationGhostCopy frameRelocationLocal finite_map
  frameRelocationCleanOperands o1PassContract pointerConfinedDefs memLocDefs

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

val _ = export_theory();
