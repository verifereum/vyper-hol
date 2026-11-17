(* The full-family internal Return of a memory-backed value: release the
   guard, copy the value into the caller's buffer, return with RET and the
   return PC only.
 *
 * TOP-LEVEL:
 *   internal_return_memory_full -- stmt_frag_full of `return e` when the
 *     function returns through the caller's buffer (ce_returns_count = 0)
 *)
Theory internalReturnMemoryMem
Ancestors
  internalReturnImmutableTypes internalReturnMemoryInputs
  internalReturnMemoryExitFrame bodyFullMemorySameTypeStore
  typedCopyOriginPtrBase typedMemoryCopy vyperTypeEnvPreservation loweringStateRelDefs
  stateRelProj
  gasExemptCert exprSimDefs
  intCallReturnMem stmtSimReturn intCallResult
  loweringSlice instIdxIndep vyperStorageTrace vyperStatePreservation
  vyperStorageFootprint
  ptrSafetyTransport
  fragGasOriginPtrExec fragGasOriginPtr fragGasPathPtr gasPathPtrExec
  fragGasPathMem fragGasPath fragGasSeqMem fragExecMem fragExec
  bodyDeclMemoryCore bodyDeclCopyMemory exprSimBufferStore exprSimMemDefs
  exprSimProps exprSimHyps exprSimHypsDefs exprSimWordArgs returnValueTyped
  valueTypingMemoryProps tupleTargetStoreRun instMemFrontier valueCopy
  exprOperandVar stmtLoweringMono externalEntryShape
  bodySimFull bodySim bodyPtrDefs gasOutcomeFullCompose gasOutcomeFull
  gasShadowCompilePure gasShadowState gasShadow gasCount memSafeRun ptrSafeRun ptrDiscipline
  loweringPosts exprLoweringProps emitHelperProps emitHelper context
  compileEnv stmtLowering exprLowering freshWrites vyperTypeInvariants
  vyperState vyperInterpreter venomExecSemantics venomState venomInst
  list rich_list
Libs
  monadsyntax


Theorem internal_return_full_shadow_copy[local]:
  ~is_word_type ty /\ 0 < type_memory_bytes cenv ty /\
  compile_store_memory cenv op dst ty ty sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\
  compile_store_memory cenv op' dst ty ty sa' = ((),sm') /\
  emit_inst RET [rpc] [] sm' = ((),sb') /\
  gas_shadow_state sb sb' ==>
  op = op' /\ gas_shadow_state sa sa'
Proof
  Cases_on `is_bytestring_type ty` >>
  simp[compile_store_memory_def, compile_store_bytestring_def,
    compile_bytestring_copy_len_def, comp_bind_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def,
    emit_def, comp_return_def] >>
  strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
    emit_def, comp_return_def, gas_shadow_state_def, gas_shadow_inst_def,
    mk_inst_def] >>
  Cases_on `type_memory_bytes cenv ty` >>
  gvs[contextTheory.compile_copy_memory_def, emitHelperTheory.emit_void_def,
    emitHelperTheory.emit_inst_def, comp_ignore_bind_def, comp_bind_def,
    fresh_id_def, emit_def, comp_return_def,
    gasShadowStateTheory.gas_shadow_inst_def, venomInstTheory.mk_inst_def]
QED

Theorem internal_return_source_env[local]:
  env_consistent env cx es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,ee) ==>
  env_consistent env cx ee
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac read_result_state >> gvs[] >>
  irule eval_expr_preserves_ec >> metis_tac[vyperTypeInvariantsTheory.gas_obs_type_invariants]
QED

Theorem compile_internal_memory_return_parts[local]:
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  cenv.ce_returns_count = 0 /\
  compile_internal_return_from_env cenv ty ty op rpc sm = ((),sb) ==>
  ?elems su sc.
    compile_return_unlock cenv sm = ((),su) /\
    compile_internal_return cenv (SOME op) rpc cenv.ce_returns_count ty ty
      elems (SOME (Var bp)) su = ((),sb) /\
    compile_store_memory cenv op (Var bp) ty ty su = ((),sc) /\
    emit_inst RET [rpc] [] sc = ((),sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_return_unlock cenv sm` >> rename1 `_ = (u, su)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `compile_store_memory cenv op (Var bp) ty ty su` >>
  rename1 `_ = (u', sc)` >> Cases_on `u'` >> simp[]
QED

Theorem return_memory_compile_parts[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  lowered_value_type cenv e = ty /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv', sb) /\
  fn_has_code sa sb func ==>
  cenv' = cenv /\
  ?op sm elems su sc.
    lower_value compile_expr cenv ty e sa = (op, sm) /\
    compile_return_unlock cenv sm = ((),su) /\
    compile_internal_return cenv (SOME op) (Var rpc) cenv.ce_returns_count
      ty ty elems (SOME (Var bp)) su = ((),sb) /\
    compile_store_memory cenv op (Var bp) ty ty su = ((),sc) /\
    emit_inst RET [Var rpc] [] sc = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\
    fn_has_code su sc func /\ fn_has_code sc sb func /\
    fn_has_code sm sb func
Proof
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, Once compile_stmt_def] >>
  Cases_on `lower_value compile_expr cenv ty e sa` >>
  rename1 `_ = (op, sm)` >> simp[] >>
  Cases_on `compile_internal_return_from_env cenv ty ty op (Var rpc) sm` >>
  rename1 `_ = (u, sb')` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_internal_memory_return_parts >> strip_tac >>
  qexistsl_tac [`elems`, `su`, `sc`] >> simp[] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_expr_grows] >>
  `cs_extends su sc` by
    metis_tac[compile_store_memory_labels, pairTheory.SND] >>
  `cs_extends sc sb` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends sm su /\ cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem return_unlock_alloca_frames[local]:
  !cenv s.
    (return_unlock_state cenv s).vs_alloca_next = s.vs_alloca_next /\
    (return_unlock_state cenv s).vs_allocas = s.vs_allocas
Proof
  rpt gen_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, tstore_def, sstore_def]
QED


(* From the state after the value, the release, the copy and RET: one
   checked path, with ghosts fixed before the dead bytes are chosen, that
   ends in the IntRet the exact contract describes. *)
Theorem return_memory_suffix_origin_ptr[local]:
  compile_return_unlock cenv sm = ((),su) /\
  compile_store_memory cenv (Var src) (Var bp) ty ty su = ((),sc) /\
  emit_inst RET [Var rpc] [] sc = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sc func /\
  fn_has_code sc sb func /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  w2n bw + type_memory_size tv <= t.vs_alloca_next /\
  expr_val_rel cx ty v (Var src) t /\
  expr_store_bound cx ty v (Var src) t /\
  lookup_var src t = SOME a /\ lookup_var bp t = SOME bw /\
  lookup_var rpc t = SOME pc /\
  not_fresh_at sm src /\ not_fresh_at sm bp /\ not_fresh_at sm rpc /\
  ptr_covers G tn src t (type_memory_size tv) /\
  ptr_covers G tn bp t (type_memory_size tv) /\
  (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
       val_in_memory tv v (w2n a) m) /\
  op_taint tn (Var rpc) = {} /\
  0 < type_memory_size tv /\
  w2n a + val_store_size tv v < dimword (:256) /\
  w2n a + val_store_size tv v <= t.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~t.vs_call_ctx.cc_static) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?r G' tn' copied. exit_result r /\
    (?fuel. run_from fuel ctx func t = r) /\
    (!D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (t, G, tn) []
          (r, G', tn')) /\
    r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (copied with vs_inst_idx := LENGTH sc.cs_current_insts) /\
    val_in_memory tv v (w2n bw) copied.vs_memory /\
    (copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) =
      return_unlock_state cenv t /\
    (!x. not_fresh_at su x ==> lookup_var x copied = lookup_var x t) /\
    (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
       mem_bytes_at a len copied.vs_memory = mem_bytes_at a len t.vs_memory) /\
    LENGTH t.vs_memory <= LENGTH copied.vs_memory /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <= LENGTH sc.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `t`] return_unlock_origin_ptr) >>
  (impl_tac >- fs[]) >> strip_tac >>
  rename1 `tn1.t_var = tn.t_var` >>
  qpat_x_assum `G' = G` SUBST_ALL_TAC >>
  drule compile_return_unlock_shape >> strip_tac >>
  qabbrev_tac `u = return_unlock_state cenv t` >>
  `u.vs_vars = t.vs_vars /\ u.vs_memory = t.vs_memory /\
   u.vs_alloca_next = t.vs_alloca_next /\ u.vs_allocas = t.vs_allocas /\
   ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts /\
   (allocas_below_fmp u <=> allocas_below_fmp t)` by suspend "unlock_frame" >>
  `!x. lookup_var x u = lookup_var x t` by fs[lookup_var_def] >>
  `!x k. ptr_covers G tn1 x u k <=> ptr_covers G tn x t k` by
    fs[ptr_covers_def, op_taint_def] >>
  `!m. mem_agree_outside tn1.t_mem u.vs_memory m <=>
       mem_agree_outside tn.t_mem t.vs_memory m` by fs[] >>
  `not_fresh_at su src /\ not_fresh_at su bp /\ not_fresh_at su rpc` by
    fs[not_fresh_at_def] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by (fs[allocas_from_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `u`, `sa` |-> `su`, `sb` |-> `sc`,
    `xs` |-> `src`, `xd` |-> `bp`, `sw` |-> `a`, `dw` |-> `bw`,
    `tenv` |-> `get_tenv cx`, `tn` |-> `tn1`]
      body_full_memory_same_type_store_path) >>
  (impl_tac >- (fs[] >> metis_tac[])) >> strip_tac >>
  rename1 `typed_copy_state_frame su (w2n bw) (type_memory_size tv) u tcopy` >>
  qabbrev_tac `copied = tcopy with vs_inst_idx := u.vs_inst_idx` >>
  `tcopy = copied with vs_inst_idx := LENGTH sc.cs_current_insts` by
    simp[Abbr `copied`, venom_state_component_equality] >>
  `lookup_var rpc tcopy = SOME pc /\ op_taint tf (Var rpc) = {} /\
   allocas_from lo tcopy /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp tcopy)` by suspend "copy_frame" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (tcopy,Gf,tf) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> tcopy,Gf,tf)` by
    suspend "ret" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> tcopy,Gf,tf)` by
    suspend "compose" >>
  qexistsl_tac [`IntRet <|iret_values := []; iret_adopt_fmp := NONE|> tcopy`,
    `Gf`,`tf`,`copied`] >>
  simp[exit_result_def, Abbr `copied`, lookup_var_def] >>
  rpt conj_tac
  >- suspend "exec"
  >- suspend "state_frame"
  >- suspend "vars"
  >- suspend "memory"
  >- suspend "length" >> suspend "index"
QED

Resume return_memory_suffix_origin_ptr[unlock_frame]:
  simp[Abbr `u`, return_unlock_state_frames, return_unlock_alloca_frames,
       return_unlock_frames] >>
  simp[allocas_below_fmp_def, return_unlock_alloca_frames] >>
  Cases_on `cenv.ce_nonreentrant` >> rename1 `cenv.ce_nonreentrant = (nr,rest)` >>
  PairCases_on `rest` >>
  Cases_on `nr` >> Cases_on `rest1` >> Cases_on `rest2` >>
  fs[return_unlock_state_def, return_unlock_insts_def, tstore_def, sstore_def]
QED
Resume return_memory_suffix_origin_ptr[copy_frame]:
  `op_taint tn1 (Var rpc) = {}` by fs[op_taint_def] >>
  `lookup_var rpc tcopy = SOME pc /\ op_taint tf (Var rpc) = {}` by metis_tac[] >>
  drule typed_copy_state_frame_allocas_below_fmp >> strip_tac >>
  fs[typed_copy_state_frame_def, venom_state_component_equality, allocas_from_def] >>
  metis_tac[]
QED
Resume return_memory_suffix_origin_ptr[ret]:
  qpat_x_assum `tcopy = _` kall_tac >>
  gen_tac >>
  qpat_x_assum `emit_inst RET _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sc.cs_next_id RET [Var rpc] []) tcopy =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> tcopy` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     irule (SRULE [mk_inst_def, eval_operands_def]
       (Q.SPECL [`sc.cs_next_id`, `[]`] step_ret_values)) >> metis_tac[]) >>
  irule (cj 3 gas_origin_ptr_path_rules) >>
  simp[exit_result_def, gas_origin_ptr_edge_def,
       fragGasOriginTheory.gas_origin_edge_def,
       fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
  conj_tac
  >- (qexists_tac `0` >>
      simp[gasEventsTheory.gas_events_step_def, mk_inst_def,
           memSafeRunTheory.mem_safe_step_non_invoke,
           unitTransformDefsTheory.inst_mem_below_frontier_def,
           contextCodegenRelTheory.source_memory_read_ranges_def,
           codegenRelTheory.source_memory_write_ranges_def]) >>
  qexists_tac `0` >>
  simp[gasCountTheory.gas_count_step_def,
       ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ptr_inst_ok_def, mk_inst_def] >>
  simp[ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED
Resume return_memory_suffix_origin_ptr[compose]:
  gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
Resume return_memory_suffix_origin_ptr[exec]:
  qpat_assum `!D. gas_origin_ptr_path _ (t,_,_) _ (IntRet _ _,_,_)`
    (qspec_then `ARB` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_exec) >>
  fs[exit_result_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr[state_frame]:
  fs[typed_copy_state_frame_def, venom_state_component_equality]
QED
Resume return_memory_suffix_origin_ptr[vars]:
  fs[lookup_var_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr[memory]:
  fs[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr[length]:
  fs[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr[index]:
  `sc.cs_current_insts = su.cs_current_insts ++ emitted_insts su sc` by
    (irule (cj 1 compile_store_memory_run_size_bound_with_capacity) >>
     simp[] >>
     qexistsl_tac [`cenv`, `Var bp`, `bw`, `u`, `Var src`, `a`, `get_tenv cx`, `tv`, `ty`, `v`] >>
     simp[eval_operand_def] >>
     qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _`
       (qspec_then `t.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def]) >>
  fs[]
QED
Finalise return_memory_suffix_origin_ptr

Theorem internal_return_memory_full:
  !DF lo ctx shadow_ctx PG func shadow_func tops cx ce cenv env es
   ty tv e lctx bw rpc rsz.
  body_inv tops ctx cenv cx /\ cenv.ce_module = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
    ~cx.txn.is_static) /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\ cenv.ce_imm_alloca = NONE /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = ty /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ 0 < type_memory_size tv /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  w2n bw + type_memory_size tv + 64 < dimword (:256) /\
  (cenv.ce_is_ctor ==> !nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  (!ety. expr_sim_full
     (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ety e es /\
   expr_vv_sim_full
     (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ety e es) ==>
  stmt_frag_full
    (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx (\H v ee gt r. intret_mem_q H func ce cx tv bw v ee r) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env cenv lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `ce.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  `?bp cap. cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    lookup_var bp s0 = SOME bw /\ not_fresh_at sa bp /\
    w2n bw + type_memory_size tv <= s0.vs_alloca_next` by
    fs[return_buf_frame_def] >>
  `lowered_value_type cenv e = ty /\
   lowered_value_type cenv (gas_shadow_expr e) = ty` by
    fs[gasShadowCompilePureTheory.gas_shadow_lowered_value_type] >>
  qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
    (mp_then Any mp_tac return_memory_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
    (mp_then Any mp_tac return_memory_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  rename1 `lower_value compile_expr cenv ty (gas_shadow_expr e) shadow_sa =
             (shadow_op, shadow_sm)` >>
  rename1 `compile_return_unlock cenv shadow_sm = ((), shadow_su)` >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `0 < type_memory_bytes cenv ty` by simp[] >>
  `op = shadow_op /\ gas_shadow_state su shadow_su` by
    metis_tac[internal_return_full_shadow_copy] >>
  `gas_shadow_state sm shadow_sm` by
    metis_tac[return_unlock_shadow_prefix] >>
  qpat_x_assum `op = shadow_op` (SUBST_ALL_TAC o SYM) >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  `?pc. lookup_var rpc s0 = SOME pc /\ not_fresh_at sa rpc` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `!ety. _` (qspec_then `ty` strip_assume_tac) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                           `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_raise]
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ (bind _ _)`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >> qexists_tac `\H res mid G1 tn1 t. ?v. res = INL v /\
     expr_post H ctx func cenv cx e es sa sm s0 mid v op t /\
     expr_store_bound cx (post_value_type cenv e) v op t /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     alloca_history func t /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
     ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv)) cenv cx mid
       G1 tn1 t /\
     ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> fs[] >>
      Cases_on `res` >> Cases_on `r` >>
      gvs[expr_exit_def, stmt_exit_ptr_def, halt_exit_def] >>
      Cases_on `y` >> gvs[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]) >>
  (* the value is on hand: release, copy and RET *)
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >> fs[] >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `post_value_type cenv e = ty` by metis_tac[post_value_type_lowered] >>
  `lookup_var rpc t = SOME pc /\ lookup_var bp t = SOME bw` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `not_fresh_at sm bp /\ not_fresh_at sm rpc` by
    metis_tac[not_fresh_at_mono, compile_expr_grows] >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[]) >>
  `value_has_type tv v` by
    (drule_at (Pos last) return_value_typed >> simp[] >>
     disch_then drule_all >> strip_tac >> gvs[]) >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `?src a. op = Var src /\ lookup_var src t = SOME a /\
     ptr_covers G1 tn1 src t (type_memory_size tv) /\
     (!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
          val_in_memory tv v (w2n a) m) /\
     w2n a + val_store_size tv v <= t.vs_alloca_next` by
    (drule internal_return_memory_value_inputs >>
     simp[] >> gvs[]) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 bp t (type_memory_size tv) /\
   op_taint tn1 (Var rpc) = {} /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ghost_inv_at_def, return_buf_ptr_def] >> gvs[]) >>
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~t.vs_call_ctx.cc_static) /\ expr_val_rel cx ty v (Var src) t` by
    (fs[expr_post_def] >>
     imp_res_tac stmt_state_rel_state_rel >>
     imp_res_tac state_rel_call_ctx_rel >> fs[call_ctx_rel_def]) >>
  `w2n bw + type_memory_size tv <= t.vs_alloca_next` by decide_tac >>
  `t.vs_alloca_next < dimword (:256)` by
    (fs[expr_post_def] >>
     metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt]) >>
  `w2n a + val_store_size tv v < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                  `G` |-> `G1`, `tn` |-> `tn1`]
            return_memory_suffix_origin_ptr) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  rename1 `val_in_memory tv v (w2n bw) copied.vs_memory` >>
  irule (Q.INST [`res` |-> `INR (ReturnException v)`, `ee` |-> `mid`]
           gas_outcome_full_exit) >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `mid`, `r`, `tn'`, `v`] >>
  simp[raise_def] >>
  rpt conj_tac >> TRY (fs[] >> NO_TAC) >>
  rpt strip_tac
  >~ [`stmt_exit_ptr _ _ _ _ _`]
  >- (simp[stmt_exit_ptr_def, expr_exit_def] >>
  (* Frame the actual copy back before the release. *)
  first_x_assum (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx mid t` by gvs[expr_post_def] >>
  `env_consistent env cx (mid with gas_obs := [])` by
    (irule internal_return_source_env >> fs[expr_sim_inv_def] >>
     metis_tac[]) >>
  `cenv.ce_is_ctor ==> !name itv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP (mid with gas_obs := []).immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (strip_tac >>
     drule_at (Pos (el 5)) internal_return_immutable_separation >>
     simp[] >> metis_tac[]) >>
  irule (SRULE [] internal_return_memory_copy_exit) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `ctx`, `sm.cs_next_id`, `t`] >> gvs[] >> metis_tac[]) >>
  simp[halt_exit_def] >>
  qpat_x_assum `copied with <|vs_vars := _; vs_memory := _|> = _`
    (mp_tac o AP_TERM ``allocas_below_fmp``) >>
  Cases_on `cenv.ce_nonreentrant` >> rename1 `cenv.ce_nonreentrant = (nr,rest)` >>
  PairCases_on `rest` >>
  Cases_on `nr` >> Cases_on `rest1` >> Cases_on `rest2` >>
  fs[allocas_below_fmp_def, return_unlock_state_def, tstore_def, sstore_def] >>
  metis_tac[]
QED
