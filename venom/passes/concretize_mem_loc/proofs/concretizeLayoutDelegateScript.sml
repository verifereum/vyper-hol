Theory concretizeLayoutDelegate
Ancestors concretizeLayoutDelegateBoundary concretizeLayoutExtractResult
  concretizeLayoutCleanRead concretizeLayoutSupplement concretizeLayoutReaderContext
  frameRelocationEnvironment frameRelocationAllocationSteps frameRelocationMemory
  venomExecSemantics venomState ptrDiscipline list venomMemProps
  frameRelocationLocal frameRelocationValues frameRelocationGuardedValues
  frameRelocationStoreSteps frameRelocationGhostCopy frameRelocationDemand
  frameOriginUpdates finite_map frameRelocationTaintOrder frameRelocationCopyTaint
  codegenRel memLocDefs contextCodegenRel

Theorem delegate_success_envelope:
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post ==>
  ?out w p. inst.inst_outputs = [out] /\ post = update_var out w p /\
    extract_venom_result s 1w (w2n ro) (w2n rs)
      (run (make_venom_delegatecall_state s (w2w addr) (w2n gas)
        (read_memory (w2n off) (w2n sz) s)
        (lookup_account (w2w addr) s.vs_accounts).code
        s.vs_call_ctx.cc_static)) = SOME (w,p)
Proof
  simp[exec_delegatecall_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem delegate_taint:
  inst.inst_opcode = DELEGATECALL /\ inst.inst_outputs = [v] /\
  inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
  post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp ==>
  step_taint inst s post tn =
    tn with <|t_mem := tn.t_mem DIFF range_bytes (step_writes inst s post);
              t_var := tn.t_var |+ (v,{})|>
Proof
  strip_tac >>
  `new_site_bytes s post = {}` by
    (irule new_site_bytes_unchanged >> simp[]) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, out_taint_def,
       set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       taint_component_equality]
QED

Theorem concretize_delegate_observation:
  inst.inst_opcode = DELEGATECALL /\ taint_ok fn tn inst s /\
  relocation_env s t /\ relocation_reader_context s t /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n (offT:bytes32)) (w2n sz) t /\
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post ==>
  ?post'. exec_delegatecall inst t gas addr offT sz (roT:bytes32) rs = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    relocation_env post post' /\ relocation_reader_context post post' /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)
Proof
  strip_tac >> drule_all concretize_delegate_clean_snapshots >> strip_tac >>
  `s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[concretize_local_obs_def, dead_result_rel_def] >>
  `make_venom_delegatecall_state s (w2w addr) (w2n gas)
     (read_memory (w2n off) (w2n sz) s)
     (lookup_account (w2w addr) s.vs_accounts).code s.vs_call_ctx.cc_static =
   make_venom_delegatecall_state t (w2w addr) (w2n gas)
     (read_memory (w2n offT) (w2n sz) t)
     (lookup_account (w2w addr) t.vs_accounts).code t.vs_call_ctx.cc_static` by
    (gvs[relocation_env_def] >> irule concretize_delegate_input >> simp[]) >>
  drule delegate_success_envelope >> strip_tac >>
  qmatch_asmsub_abbrev_tac `extract_venom_result s _ _ _ result = _` >>
  `?pT. extract_venom_result t 1w (w2n roT) (w2n rs) result = SOME (w,pT)` by
    (irule concretize_extract_exists >> goal_assum (drule_at Any)) >>
  drule_all concretize_extract_observables >> strip_tac >>
  rev_drule concretize_extract_unchanged >> strip_tac >>
  drule concretize_extract_unchanged >> strip_tac >>
  qexists_tac `update_var out w pT` >> conj_tac
  >- (simp[exec_delegatecall_def] >>
      qpat_assum `make_venom_delegatecall_state _ _ _ _ _ _ = _`
        (fn th => pure_once_rewrite_tac[GSYM th]) >> fs[Abbr `result`]) >>
  rpt conj_tac
  >- gvs[concretize_local_obs_def, dead_result_rel_def, update_var_def,
         accounts_agree_except_def, transient_agree_except_def,
         storage_agree_except_def, word_agree_except_def]
  >- gvs[concretize_supplement_def, step_taint_def, store_taint_def,
         imm_taint_def, adopt_reset_def, update_var_def,
         accounts_agree_except_def, transient_agree_except_def,
         storage_agree_except_def, word_agree_except_def]
  >- gvs[relocation_env_def, update_var_def]
  >- gvs[relocation_reader_context_def, update_var_def] >>
  qexistsl_tac [`out`,`w`] >> simp[update_var_def]
QED

Theorem delegate_execution_fields:
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post ==>
  ?out w. inst.inst_outputs = [out] /\
    post.vs_vars = (update_var out w s).vs_vars /\
    post.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rs) post.vs_returndata) s).vs_memory /\
    post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule delegate_success_envelope >> strip_tac >>
  drule concretize_extract_unchanged >> strip_tac >>
  drule extract_venom_result_memory >> strip_tac >>
  qexistsl_tac [`out`,`w`] >> gvs[update_var_def]
QED

Theorem concretize_delegate_local_execution:
  inst.inst_opcode = DELEGATECALL /\ taint_ok fn tn inst s /\
  inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n (offT:bytes32)) (w2n sz) t /\
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post /\
  (!a b. next a b /\ w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
     b = w2n (roT:bytes32) + (a-w2n ro)) /\
  (!a b. next a b /\ ~(w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
     R a b /\ ~(w2n roT <= b /\
       b < w2n roT + LENGTH (TAKE (w2n rs) post.vs_returndata))) ==>
  ?post'. exec_delegatecall inst t gas addr offT sz roT rs = OK post' /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes Opaque (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn)) next concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    relocation_env post post' /\ relocation_reader_context post post'
Proof
  strip_tac >>
  `concretize_local_obs s t` by metis_tac[local_rel_observation] >>
  `?post'. exec_delegatecall inst t gas addr offT sz roT rs = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    relocation_env post post' /\ relocation_reader_context post post' /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)` by
    (irule concretize_delegate_observation >> simp[] >>
     conj_tac >- (qexistsl_tac [`off`,`ro`] >> simp[]) >>
     qexists_tac `fn` >> simp[]) >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  `post.vs_returndata = post'.vs_returndata` by
    (fs[concretize_local_obs_def, dead_result_rel_def] >>
     irule listTheory.LIST_EQ >> simp[]) >>
  `demand_agree next (\a. read_byte a post.vs_memory)
    (\b. read_byte b post'.vs_memory)` by suspend "memory" >>
  `local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R (\s t. T) s t` by fs[local_rel_def] >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [out] NONE))
    (guarded_bytes Opaque (origin_set rv [out] NONE) (step_taint inst s post tn))
    R (\s t. T) (update_var out w s) (update_var out w t)` by suspend "values" >>
  fs[local_rel_def, variable_domains_def, variables_agree_on_def,
     local_values_def, lookup_var_def, update_var_def]
QED
Resume concretize_delegate_local_execution[memory]:
  drule delegate_execution_fields >> strip_tac >>
  rev_drule delegate_execution_fields >> strip_tac >>
  qpat_x_assum `post.vs_returndata = post'.vs_returndata` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> irule demand_agree_write_memory >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!a b. _ ==> b = _`
      (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  qexists_tac `R` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a b. _ ==> R a b /\ _`
        (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[local_rel_demand]
QED
Resume concretize_delegate_local_execution[values]:
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
Finalise concretize_delegate_local_execution

Theorem concretize_delegate_taint_order:
  inst.inst_opcode = DELEGATECALL /\
  inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
  eval_operand opg s = SOME gas /\ eval_operand opa s = SOME addr /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
  eval_operand opg t = SOME gas /\ eval_operand opa t = SOME addr /\
  eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
  eval_operand opr s = SOME ro /\ eval_operand opm s = SOME rs /\
  eval_operand opr t = SOME roT /\ eval_operand opm t = SOME rs /\
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post /\
  exec_delegatecall inst t gas addr (offT:bytes32) sz (roT:bytes32) rs = OK post' /\
  post.vs_returndata = post'.vs_returndata /\
  relocation_taint_le R tn un /\
  (!a b. next a b /\ w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
     b = w2n roT + (a-w2n ro)) /\
  (!a b. next a b /\ ~(w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata)) ==> R a b) ==>
  relocation_taint_le next (step_taint inst s post tn) (step_taint inst t post' un)
Proof
  strip_tac >> dxrule delegate_execution_fields >> strip_tac >>
  dxrule delegate_execution_fields >> strip_tac >>
  `out' = out` by fs[] >> gvs[] >>
  `step_taint inst s post tn =
    tn with <|t_mem := tn.t_mem DIFF range_bytes (step_writes inst s post);
              t_var := tn.t_var |+ (out,{})|>` by
    (irule delegate_taint >> simp[] >> metis_tac[]) >>
  `step_taint inst t post' un =
    un with <|t_mem := un.t_mem DIFF range_bytes (step_writes inst t post');
              t_var := un.t_var |+ (out,{})|>` by
    (irule delegate_taint >> simp[] >> metis_tac[]) >>
  `LENGTH (TAKE (w2n rs) post'.vs_returndata) =
    MIN (w2n rs) (LENGTH post'.vs_returndata)` by
    simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  gvs[] >> fs[relocation_taint_le_def] >>
  simp[relocation_taint_le_def] >> conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
           memory_range_of_operands_def, range_bytes_def, demand_taint_def] >>
      qpat_x_assum `demand_taint _ _ _` mp_tac >>
      qpat_x_assum `!a b. _ ==> b = _` mp_tac >>
      qpat_x_assum `!a b. _ ==> R a b` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[demand_taint_def, LENGTH_TAKE] >> rpt strip_tac >>
      `~(w2n ro <= a /\ a < w2n ro + MIN (w2n rs) (LENGTH post'.vs_returndata))` by
        (strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
      metis_tac[]) >>
  simp[op_taint_def, FLOOKUP_UPDATE] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >> fs[op_taint_def]
QED
