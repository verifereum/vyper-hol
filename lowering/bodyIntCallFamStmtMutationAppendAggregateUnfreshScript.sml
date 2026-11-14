(* Only the straight-line aggregate prefix requires a cleaned variable map. *)
Theory bodyIntCallFamStmtMutationAppendAggregateUnfresh
Ancestors
  bodyIntCallFamStmtMutationAppendAggregateSuffix varsExt freshWrites
  fragGasSeqAbort fragGasPath fragGasMode exprSimHashBoundary
  stmtReasonLitFragMemory finite_map
  bodyIntCallFamStmtMutationAppendAggregatePrefix emitHelper compileEnv
  exprLoweringProps venomInst venomState stateFrame
  bodyIntCallFamStmtMutationAppendAggregateCopy
  bodyIntCallFamStmtMutationAppendAggregateHeader
  bodyIntCallFamStmtMutationAppendAggregatePost
  vyperStoragePlaceRegion vyperScopePreservation gasOutcome gasSummary
  exprSimWordArgs stmtSimAppendStorageCompose fragExec stmtLoweringMono
  loweringStateRelDefs exprSimDefs typedMemoryCopy appendStorageRel

Theorem intcall_append_aggregate_prefix_unfresh:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop;Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop;Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop;Lit (n2w sz)] s4 = (off,s5) /\
  emit_op ADD [dop;off] s5 = (pop,s6) /\
  fn_has_code sa s6 func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand bop s = SOME slot /\ (!x. bop = Var x ==> not_fresh_at sa x) /\
  cap < dimword (:256) ==>
  if cap <= w2n (if tr then tload slot s else sload slot s) then
    ?a t. gas_marked_path F ctx func s 0 (Abort a t)
  else ?u.
    gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := LENGTH s6.cs_current_insts)) /\
    ~u.vs_halted /\ u.vs_current_bb = s6.cs_current_bb /\
    state_frame u = state_frame s /\
    eval_operand pop u = SOME
      (slot+1w+(if tr then tload slot s else sload slot s)*n2w sz) /\
    eval_operand lop u = SOME (if tr then tload slot s else sload slot s) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x u = SOME a)
Proof
  strip_tac >>
  drule_all intcall_append_aggregate_prefix_structure >> strip_tac >>
  `s6.cs_current_bb = sa.cs_current_bb` by fs[same_blocks_def] >>
  qmatch_asmsub_abbrev_tac `s6.cs_current_insts = sa.cs_current_insts ++ code` >>
  `emitted_insts sa s6 = code` by
    simp[emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
       ~is_ext_call_op i.inst_opcode) code` by
    (Cases_on `tr` >>
     gvs[emit_op_def,emit_void_def,fresh_id_def,fresh_var_def,emit_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,emitted_insts_def,
       Abbr `code`,mk_inst_def,is_terminator_def,is_ext_call_op_def,
       rich_listTheory.DROP_LENGTH_APPEND,rich_listTheory.DROP_APPEND2]) >>
  `eval_operand bop (drop_fresh sa s) = SOME slot` by
    (Cases_on `bop` >> gvs[eval_operand_def,lookup_var_drop_fresh,drop_fresh_def]) >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `sload slot (drop_fresh sa s) = sload slot s /\
   tload slot (drop_fresh sa s) = tload slot s` by
    simp[drop_fresh_def,sload_def,tload_def,contract_storage_def,contract_transient_def] >>
  drule_all intcall_append_aggregate_guard_address_run >>
  asm_rewrite_tac[] >> strip_tac >>
  IF_CASES_TAC >>
  qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac
  >- (`run_inst_seq code (drop_fresh sa s) =
        Abort Revert_abort (revert_state (set_returndata [] u2))` by
        (simp[Abbr `code`] >> imp_res_tac run_inst_seq_append >>
         pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> asm_rewrite_tac[] >>
         irule EQ_TRANS >> qexists `run_inst_seq (emitted_insts s2 s3) u2` >>
         conj_tac >- (irule run_inst_seq_append_err >> asm_rewrite_tac[] >> simp[]) >>
         asm_rewrite_tac[]) >>
      `vars_ext_result (run_inst_seq code (drop_fresh sa s)) (run_inst_seq code s)` by
        (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
      gvs[vars_ext_result_def] >>
      drule_all fn_has_code_code >> strip_tac >>
      drule_at (Pat `run_inst_seq _ s = Abort _ _`) run_inst_seq_abort_zero_path >>
      disch_then (qspecl_then [`ctx`,`func`,`bb`] mp_tac) >>
      (impl_tac >- simp[]) >> metis_tac[]) >>
  rename1 `run_inst_seq (emitted_insts s5 s6) u5 = OK u6` >>
  `run_inst_seq code (drop_fresh sa s) = OK u6` by
    (simp[Abbr `code`] >> imp_res_tac run_inst_seq_append >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> asm_rewrite_tac[]) >>
  `vars_ext_result (run_inst_seq code (drop_fresh sa s)) (run_inst_seq code s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  asm_rewrite_tac[vars_ext_result_def] >> strip_tac >>
  rename1 `run_inst_seq code s = OK t` >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[listTheory.EVERY_MEM,listTheory.FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all hash_run_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t` >> asm_rewrite_tac[] >>
  `state_frame t = state_frame s` by
    (qpat_x_assum `vars_ext u6 t` mp_tac >>
     qpat_x_assum `state_frame u6 = _` mp_tac >>
     simp[vars_ext_def,state_frame_def,drop_fresh_def] >> strip_tac >> strip_tac >>
     qpat_x_assum `t = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  asm_rewrite_tac[] >>
  `!op w. eval_operand op u6 = SOME w ==> eval_operand op t = SOME w` by
    (rpt strip_tac >>
     qpat_assum `vars_ext u6 t` (strip_assume_tac o REWRITE_RULE[vars_ext_def]) >>
     metis_tac[eval_operand_vars_ext,optionTheory.NOT_SOME_NONE]) >>
  simp[] >> conj_tac >- gvs[] >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def,lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  fs[eval_operand_def]
QED

Theorem intcall_append_aggregate_suffix_exec_unfresh:
  compile_dynarray_append ce (Lit slot) op 1 (type_slot_size tv) elem elem cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ cap < dimword (:256) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  expr_sim_inv ce cx env es /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
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
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==>
             lookup_var x u = SOME a) /\
      ?marks raw. ee = raw with gas_obs := [] /\
        gas_marked_exec F (ctx,func)
          (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
          (es,s) marks res raw (OK u))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule intcall_append_aggregate_suffix_parts >> strip_tac >>
  drule_all intcall_append_aggregate_suffix_code >> strip_tac >>
  `eval_operand (Lit slot) s = SOME slot /\
   (!x. Lit slot = Var x ==> not_fresh_at sa x)` by simp[eval_operand_def] >>
  drule_all intcall_append_aggregate_prefix_unfresh >>
  Cases_on `cap <= w2n (lookup_storage slot (get_storage cx es tr))` >>
  asm_rewrite_tac[] >> disch_then (qspec_then `ctx` strip_assume_tac)
  >- (`append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
        (INR (Error (RuntimeError "append full storage array")),es)` by
        (irule stmtSimAppendStorageTheory.append_storage_full >> simp[]) >>
      simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR (Error (RuntimeError "append full storage array"))`, `es`, `Abort a t`] >>
      simp[gas_marked_exec_def,expr_exit_def,exit_result_def] >>
      metis_tac[append_storage_place_gas_obs]) >>
  `w2n (lookup_storage slot (get_storage cx es tr)) < cap` by decide_tac >>
  qmatch_asmsub_abbrev_tac `w2n head < cap` >>
  qabbrev_tac `start = w2n slot + 1 + w2n head * type_slot_size tv` >>
  `start + type_slot_size tv <= dimword (:256)` by
    (`(w2n head + 1) * type_slot_size tv <= cap * type_slot_size tv` by
       (simp[arithmeticTheory.LE_MULT_RCANCEL] >> decide_tac) >>
     qpat_x_assum `(w2n head + 1) * _ <= _` mp_tac >>
     pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,arithmeticTheory.MULT_CLAUSES] >>
     qpat_x_assum `w2n slot + type_slot_size _ <= _` mp_tac >>
     pure_rewrite_tac[vyperValueTheory.type_slot_size_def] >>
     simp_tac pure_ss [Abbr `start`] >> decide_tac) >>
  `n2w start = slot + 1w + head * n2w (type_slot_size tv)` by
    (simp[Abbr `start`,GSYM wordsTheory.word_add_n2w,GSYM wordsTheory.word_mul_n2w]) >>
  `sa.cs_next_var <= s6.cs_next_var /\ s1.cs_next_var <= s6.cs_next_var` by
    (imp_res_tac emitHelperPropsTheory.emitted_insts_emit_op >>
     imp_res_tac emitHelperPropsTheory.emitted_insts_emit_void >> fs[]) >>
  `local_ptrs_reserved ce s6` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule stmt_state_rel_reserved_frame >> qexistsl [`s`,`sa`] >> asm_rewrite_tac[]) >>
  qabbrev_tac `u0 = u with vs_inst_idx := LENGTH s6.cs_current_insts` >>
  `eval_operand op u = SOME sw` by
    (Cases_on `op` >> gvs[eval_operand_def,state_frame_def] >> metis_tac[]) >>
  `(!x. op = Var x \/ pop = Var x \/ lop = Var x ==> not_fresh_at s6 x)` by
    (imp_res_tac typed_copy_emit_op_fresh >> fs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `storage_subregion (ArrayTV tv (Dynamic cap))
     [ValueSubscript (IntV (&w2n head))] (1+w2n head*type_slot_size tv) tv` by
    simp[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  `start = w2n slot + (1+w2n head*type_slot_size tv)` by simp[Abbr `start`] >>
  `stmt_state_rel ctx func ce cx es u0 /\
   ~u0.vs_halted /\ ~u0.vs_call_ctx.cc_static /\
   u0.vs_current_bb = s6.cs_current_bb /\
   u0.vs_inst_idx = LENGTH s6.cs_current_insts /\
   eval_operand op u0 = SOME sw /\ eval_operand pop u0 = SOME (n2w start) /\
   val_in_memory tv v (w2n sw) u0.vs_memory` by
    (qpat_assum `state_frame u = state_frame s`
       (strip_assume_tac o SRULE [state_frame_def]) >>
     simp[Abbr `u0`,stmt_state_rel_inst_idx,eval_operand_def] >>
     metis_tac[Abbr `u0`,stmt_state_rel_inst_idx,eval_operand_def]) >>
  `!x. op = Var x \/ pop = Var x ==> not_fresh_at s6 x` by metis_tac[] >>
  drule_all intcall_append_aggregate_copy >> strip_tac >>
  `s6.cs_next_var <= s7.cs_next_var` by
    (mp_tac (cj 1 ci_mono_compile_store_slots) >>
     disch_then (qspecl_then [`ce`,`op`,`pop`,`elem`,`tr`,`s6`] mp_tac) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved ce s7` by
    (irule local_ptrs_reserved_next_var >> qexists `s6` >> simp[]) >>
  `!x. lop = Var x ==> not_fresh_at s6 x` by metis_tac[] >>
  `!x. lop = Var x \/ Lit slot = Var x ==> not_fresh_at s7 x` by
    (simp[] >> fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `eval_operand lop t = SOME head` by
    (qpat_assum `eval_operand lop u = SOME head` mp_tac >>
     qpat_assum `!x. not_fresh_at s6 x ==> lookup_var x t = _` mp_tac >>
     qpat_assum `!x. lop = Var x ==> not_fresh_at s6 x` mp_tac >>
     qpat_assum `t.vs_labels = u0.vs_labels` mp_tac >>
     unabbrev_all_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `lop` >> simp[eval_operand_def,lookup_var_def] >> metis_tac[]) >>
  `eval_operand (Lit slot) t = SOME slot /\ ~t.vs_call_ctx.cc_static` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  `fn_has_code s7 sf func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  drule_all intcall_append_aggregate_header_old_landing >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t')` by
    (metis_tac[fragGasModeTheory.gas_marked_path_then,arithmeticTheory.ADD_CLAUSES]) >>
  `~cx.txn.is_static` by
    (qpat_assum `stmt_state_rel ctx func ce cx es s`
       (mp_tac o SRULE [stmt_state_rel_def,state_rel_def]) >> simp[]) >>
  `append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
    (INL (),set_storage cx (set_storage cx es tr
      (apply_writes (n2w start) writes (get_storage cx es tr))) tr
      (update_storage slot (head+1w)
        (apply_writes (n2w start) writes (get_storage cx es tr))))` by
    (mp_tac (Q.INST [`len` |-> `w2n (lookup_storage slot (get_storage cx es tr))`]
        intcall_append_aggregate_success) >>
     simp[Abbr `start`,Abbr `head`,GSYM wordsTheory.word_add_n2w,
       GSYM wordsTheory.word_mul_n2w,wordsTheory.WORD_ADD_ASSOC]) >>
  qmatch_asmsub_abbrev_tac `append_place _ _ _ es = (INL (),ee)` >>
  `stmt_state_rel ctx func ce cx ee t'` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ t'`
       (mp_tac o SRULE [vyperStorageBackendTheory.get_storage_after_set]) >>
     pure_rewrite_tac[markerTheory.Abbrev_def] >> unabbrev_all_tac >> metis_tac[]) >>
  `!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==>
      lookup_var x t' = SOME a` by
    (rpt strip_tac >>
     `not_fresh_at s6 x /\ not_fresh_at s7 x` by
       (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     `lookup_var x u = SOME a` by metis_tac[] >>
     `lookup_var x u0 = SOME a` by
       (qpat_assum `lookup_var x u = SOME a` mp_tac >>
        simp[NoAsms,Abbr `u0`,lookup_var_def]) >>
     metis_tac[]) >>
  `t'.vs_memory = s.vs_memory /\ t'.vs_allocas = s.vs_allocas /\
   t'.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `state_frame u = state_frame s`
       (strip_assume_tac o SRULE [state_frame_def]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`t'.vs_memory = t.vs_memory`, `t.vs_memory = u0.vs_memory`,
        `u.vs_memory = s.vs_memory`,
        `t'.vs_allocas = t.vs_allocas`, `t.vs_allocas = u0.vs_allocas`,
        `u.vs_allocas = s.vs_allocas`,
        `t'.vs_alloca_next = t.vs_alloca_next`,
        `t.vs_alloca_next = u0.vs_alloca_next`,
        `u.vs_alloca_next = s.vs_alloca_next`] >>
     simp[NoAsms,Abbr `u0`] >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL ()`,`ee with gas_obs := []`,`OK t'`] >>
  simp[gas_marked_exec_def] >>
  conj_asm1_tac >- (drule append_storage_place_gas_obs >> simp[]) >>
  conj_tac >- (drule append_storage_place_scopes_immutables >> simp[]) >>
  conj_tac >- (drule append_storage_place_scopes_immutables >> simp[]) >>
  qexistsl [`[]`,`ee`] >> simp[gas_explicit_def]
QED
