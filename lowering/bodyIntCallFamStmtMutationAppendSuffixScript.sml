(* Counted storage/transient append action at the forced operand landing. *)
Theory bodyIntCallFamStmtMutationAppendSuffix
Ancestors
  stmtSimAppendStorageCompose appendStorageSuccessPostPtr
  exprSimWordArgs vyperScopePreservation gasOutcome gasSummary
  stateFrame venomState exprLoweringProps exprSimDefs fragExec

Theorem intcall_append_storage_suffix:
  compile_dynarray_append ce (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,w)] /\
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
    (es,s)
    (\res ee u. res = INL () /\ stmt_state_rel ctx func ce cx ee u /\
      ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
      u.vs_inst_idx = LENGTH sf.cs_current_insts /\
      ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
      u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
      u.vs_alloca_next = s.vs_alloca_next /\
      (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
             lookup_var x u = SOME a))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule_all append_storage_word_suffix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  Cases_on `cap <= w2n (lookup_storage slot (get_storage cx es tr))`
  >- (qpat_x_assum `_ ==> ?a t. _` mp_tac >> simp[] >> strip_tac >>
      `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
        (INR (Error (RuntimeError "append full storage array")),es)` by
        (irule stmtSimAppendStorageTheory.append_storage_full >> simp[]) >>
      simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR (Error (RuntimeError "append full storage array"))`,
                    `es`, `Abort a t`] >>
      simp[gas_marked_exec_def, expr_exit_def, exit_result_def] >>
      metis_tac[append_storage_place_gas_obs]) >>
  suspend "success"
QED

Resume intcall_append_storage_suffix[success]:
  `w2n (lookup_storage slot (get_storage cx es tr)) < cap` by decide_tac >>
  qpat_x_assum `!len. _` (qspec_then
    `w2n (lookup_storage slot (get_storage cx es tr))` mp_tac) >>
  pure_asm_rewrite_tac [boolTheory.REFL_CLAUSE, boolTheory.AND_CLAUSES, boolTheory.IMP_CLAUSES] >>
  strip_tac >>
  Cases_on `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es` >>
  rename1 `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,ee)` >>
  drule appendStorageSuccessPostPtrTheory.append_storage_word_success_post >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_all_then strip_assume_tac o
    PURE_REWRITE_RULE [boolTheory.REFL_CLAUSE, boolTheory.AND_CLAUSES]) >>
  drule_all append_storage_place_scopes_immutables >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `state_frame u = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `tr` >>
     simp[state_frame_def, sstore_def, tstore_def, LET_THM]) >>
  drule append_storage_word_suffix_structure >> strip_tac >>
  `sf.cs_current_bb = sb.cs_current_bb` by
    fs[same_blocks_def] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `ee`, `OK (u with vs_inst_idx := LENGTH sf.cs_current_insts)`] >>
  simp[gas_marked_exec_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  conj_tac >- metis_tac[append_storage_place_gas_obs] >>
  fs[lookup_var_def]
QED

Finalise intcall_append_storage_suffix
