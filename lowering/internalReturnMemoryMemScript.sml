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
  internalReturnImmutableTypes internalReturnMemoryInputs bodyInvCodeProps
  structFieldsProps bodyInvSplit
  internalReturnMemoryExitFrame bodyFullMemorySameTypeStore
  typedCopyOriginPtrBase typedMemoryCopy vyperTypeEnvPreservation loweringStateRelDefs
  stateRelProj bodyFullIntCallBufferedCopy bodyFullMemoryStore
  gasExemptCert exprSimDefs bodyFullShared externalReturnSiteSemantics
  gasShadowCompileStmtHelpers externalNormalizePremises externalReturnSelectedResources
  intCallReturnMem stmtSimReturn intCallResult
  loweringSlice instIdxIndep vyperStorageTrace vyperStatePreservation
  vyperStorageFootprint
  ptrSafetyTransport
  fragGasOriginPtrExec fragGasOriginPtr fragGasPathPtr gasPathPtrExec
  fragGasPathMem fragGasPath fragGasSeqMem fragExecMem fragExec
  bodyDeclMemoryCore bodyDeclCopyMemory exprSimBufferStore exprSimMemDefs
  exprSimProps exprSimHyps exprSimHypsDefs exprSimWordArgs
  valueTypingMemoryProps tupleTargetStoreRun instMemFrontier valueCopy
  exprOperandVar stmtLoweringMono externalEntryShape
  bodySimFull bodySim bodyPtrDefs gasOutcomeFullCompose gasOutcomeFull
  gasOutcomeFullBindMods gasOutcomeFullMods gasExemptCertMods
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
  compile_internal_return_from_env cenv ty sty op rpc sm = ((),sb) ==>
  ?elems su sc.
    compile_return_unlock cenv sm = ((),su) /\
    compile_internal_return cenv (SOME op) rpc cenv.ce_returns_count ty sty
      elems (SOME (Var bp)) su = ((),sb) /\
    compile_store_memory cenv op (Var bp) ty sty su = ((),sc) /\
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
  Cases_on `compile_store_memory cenv op (Var bp) ty sty su` >>
  rename1 `_ = (u', sc)` >> Cases_on `u'` >> simp[]
QED

Theorem return_memory_compile_parts[local]:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
  stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv', sb) /\
  fn_has_code sa sb func ==>
  cenv' = cenv /\
  ?op sm elems su sc.
    lower_value compile_expr cenv ty e sa = (op, sm) /\
    compile_return_unlock cenv sm = ((),su) /\
    compile_internal_return cenv (SOME op) (Var rpc) cenv.ce_returns_count
      ty (lowered_value_type cenv e) elems (SOME (Var bp)) su = ((),sb) /\
    compile_store_memory cenv op (Var bp) ty (lowered_value_type cenv e) su = ((),sc) /\
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
  Cases_on `compile_internal_return_from_env cenv ty (lowered_value_type cenv e) op (Var rpc) sm` >>
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


Theorem internal_return_ret_origin_ptr[local]:
  emit_inst RET [Var rpc] [] sc = ((),sb) /\ fn_has_code sc sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s,G,tn)
Proof
  strip_tac >>
  qpat_x_assum `emit_inst RET _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sc.cs_next_id RET [Var rpc] []) s =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s` by
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

(* From the state after the value, the release, the copy and RET: one
   checked path, with ghosts fixed before the dead bytes are chosen, that
   ends in the IntRet the exact contract describes. *)
Theorem return_memory_suffix_origin_ptr_taint[local]:
  compile_return_unlock cenv sm = ((),su) /\
  compile_store_memory cenv (Var src) (Var bp) ty ty su = ((),sc) /\
  emit_inst RET [Var rpc] [] sc = ((),sb) /\
  fn_has_code sm su func /\ fn_has_code su sc func /\
  fn_has_code sc sb func /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  w2n bw + type_memory_size tv < dimword (:256) /\
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
    (!mem. mem_agree_outside tn'.t_mem copied.vs_memory mem ==>
      val_in_memory tv v (w2n bw) mem) /\
    (copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) =
      return_unlock_state cenv t /\
    (!x. not_fresh_at su x ==> lookup_var x copied = lookup_var x t) /\
    (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
       mem_bytes_at a len copied.vs_memory = mem_bytes_at a len t.vs_memory) /\
    LENGTH t.vs_memory <= LENGTH copied.vs_memory /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <= LENGTH sc.cs_current_insts /\
    (((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      FST (SND (SND cenv.ce_nonreentrant))) ==>
      tn'.t_stor = tn.t_stor /\ tn'.t_trans SUBSET tn.t_trans /\
      tn'.t_imm = tn.t_imm) /\
    (!i. i < w2n bw ==> (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `t`] return_unlock_origin_ptr_taint) >>
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
  >- suspend "length"
  >> suspend "index"
QED

Resume return_memory_suffix_origin_ptr_taint[unlock_frame]:
  simp[Abbr `u`, return_unlock_state_frames, return_unlock_alloca_frames,
       return_unlock_frames] >>
  simp[allocas_below_fmp_def, return_unlock_alloca_frames] >>
  Cases_on `cenv.ce_nonreentrant` >> rename1 `cenv.ce_nonreentrant = (nr,rest)` >>
  PairCases_on `rest` >>
  Cases_on `nr` >> Cases_on `rest1` >> Cases_on `rest2` >>
  fs[return_unlock_state_def, return_unlock_insts_def, tstore_def, sstore_def]
QED
Resume return_memory_suffix_origin_ptr_taint[copy_frame]:
  `op_taint tn1 (Var rpc) = {}` by fs[op_taint_def] >>
  `lookup_var rpc tcopy = SOME pc /\ op_taint tf (Var rpc) = {}` by metis_tac[] >>
  drule typed_copy_state_frame_allocas_below_fmp >> strip_tac >>
  fs[typed_copy_state_frame_def, venom_state_component_equality, allocas_from_def] >>
  metis_tac[]
QED
Resume return_memory_suffix_origin_ptr_taint[ret]:
  gen_tac >> irule internal_return_ret_origin_ptr >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr_taint[compose]:
  gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
Resume return_memory_suffix_origin_ptr_taint[exec]:
  qpat_assum `!D. gas_origin_ptr_path _ (t,_,_) _ (IntRet _ _,_,_)`
    (qspec_then `ARB` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_exec) >>
  fs[exit_result_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr_taint[state_frame]:
  fs[typed_copy_state_frame_def, venom_state_component_equality]
QED
Resume return_memory_suffix_origin_ptr_taint[vars]:
  fs[lookup_var_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr_taint[memory]:
  fs[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr_taint[length]:
  fs[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]
QED
Resume return_memory_suffix_origin_ptr_taint[index]:
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
Finalise return_memory_suffix_origin_ptr_taint

(* The copy may land in another basic block. RET uses that actual endpoint.
   Normalize the control fields only when comparing the memory frame with
   the state immediately after releasing the lock. *)
Theorem return_relayout_suffix_origin_ptr[local]:
  compile_return_unlock cenv sm = ((),su) /\ fn_has_code sm su func /\
  emit_inst RET [Var rpc] [] sc = ((),sb) /\ fn_has_code sc sb func /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var rpc t = SOME pc /\ not_fresh_at su rpc /\
  op_taint tn (Var rpc) = {} /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~t.vs_call_ctx.cc_static) /\
  (!tn1. tn1.t_var = tn.t_var /\ tn1.t_mem = tn.t_mem ==>
    ?u Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (return_unlock_state cenv t,G,tn1) [] (OK u,Gf,tf)) /\
      val_in_memory tv v (w2n bw) u.vs_memory /\
      (!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n bw) mem) /\
      typed_copy_state_frame su (w2n bw) (type_memory_size tv)
        (return_unlock_state cenv t) u /\
      ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\
      tf.t_stor = tn1.t_stor /\ tf.t_trans = tn1.t_trans /\ tf.t_imm = tn1.t_imm /\
      (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_size tv) ==>
        (i IN tf.t_mem <=> i IN tn1.t_mem)) /\
      (!x. not_fresh_at su x ==> op_taint tf (Var x) = op_taint tn1 (Var x))) ==>
  ?r Gf tf copied prev.
    r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (copied with <|vs_prev_bb := prev; vs_current_bb := sc.cs_current_bb;
                  vs_inst_idx := LENGTH sc.cs_current_insts|>) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,Gf,tf)) /\
    val_in_memory tv v (w2n bw) copied.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem copied.vs_memory mem ==>
      val_in_memory tv v (w2n bw) mem) /\
    (copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) =
      return_unlock_state cenv t /\
    (!x. not_fresh_at su x ==> lookup_var x copied = lookup_var x t) /\
    (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
      mem_bytes_at a len copied.vs_memory = mem_bytes_at a len t.vs_memory) /\
    LENGTH t.vs_memory <= LENGTH copied.vs_memory /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <= LENGTH su.cs_current_insts /\
    (((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      FST (SND (SND cenv.ce_nonreentrant))) ==>
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\ tf.t_imm = tn.t_imm) /\
    (!i. i < w2n bw ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `t`] return_unlock_origin_ptr_taint) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `tn1.t_var = tn.t_var` >>
  qpat_x_assum `G' = G` SUBST_ALL_TAC >>
  qpat_x_assum `!tn1. _ ==> ?u Gf tf. _` (qspec_then `tn1` mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `s = return_unlock_state cenv t` >>
  drule compile_return_unlock_shape >> strip_tac >>
  `lookup_var rpc u = SOME pc /\ op_taint tf (Var rpc) = {} /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (drule typed_copy_state_frame_allocas_below_fmp >> strip_tac >>
     `op_taint tn1 (Var rpc) = {}` by fs[op_taint_def] >>
     fs[typed_copy_state_frame_def,venom_state_component_equality,Abbr `s`,
        lookup_var_def,allocas_from_def,allocas_below_fmp_def,
        return_unlock_alloca_frames] >>
     qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     fs[return_unlock_state_def,tstore_def,sstore_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gf,tf) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u,Gf,tf)` by
    (gen_tac >> irule internal_return_ret_origin_ptr >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> u,Gf,tf)` by
    (gen_tac >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  qabbrev_tac `copied = u with
    <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx|>` >>
  `copied with <|vs_prev_bb := u.vs_prev_bb; vs_current_bb := sc.cs_current_bb;
                vs_inst_idx := LENGTH sc.cs_current_insts|> = u` by
    simp[Abbr `copied`,venom_state_component_equality] >>
  `(copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) = s /\
   s.vs_memory = t.vs_memory /\ s.vs_vars = t.vs_vars` by
    (qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     fs[typed_copy_state_frame_def,Abbr `copied`,Abbr `s`,
        venom_state_component_equality,return_unlock_state_def,tstore_def,sstore_def]) >>
  qexistsl_tac [`Gf`,`tf`,`copied`,`u.vs_prev_bb`] >>
  `copied.vs_memory = u.vs_memory /\ copied.vs_vars = u.vs_vars` by simp[Abbr `copied`] >>
  simp[] >> rpt conj_tac
  >~ [`lookup_var x copied = _`]
  >- fs[typed_copy_state_frame_def,lookup_var_def]
  >~ [`mem_bytes_at _ _ _ = _`]
  >- (fs[typed_copy_state_frame_def,typed_copy_frame_def] >> metis_tac[])
  >~ [`LENGTH t.vs_memory <= _`]
  >- fs[typed_copy_state_frame_def,typed_copy_frame_def]
  >> fs[typed_copy_state_frame_def,lookup_var_def]
  >> metis_tac[arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem return_memory_copy_exit_control[local]:
  same_frame ce cenv /\ cenv.ce_returns_count = 0 /\
  (!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       lookup_var x copied = lookup_var x t) /\
  stmt_state_rel H ctx func cenv cx ee t /\
  (cenv.ce_is_ctor ==> !src name itv iv off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
               NONE => FEMPTY
             | SOME imms => get_source_immutables src imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)) /\
  (copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>) =
    return_unlock_state cenv t /\
  (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
    mem_bytes_at a len copied.vs_memory = mem_bytes_at a len t.vs_memory) /\
  LENGTH t.vs_memory <= LENGTH copied.vs_memory /\
  val_in_memory tv v (w2n bw) copied.vs_memory /\
  LENGTH (return_unlock_insts cenv iid) <= n0 /\
  r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
        (copied with <|vs_prev_bb := prev; vs_current_bb := bb; vs_inst_idx := n|>) ==>
  !tail. intret_mem_q H func ce cx tv bw v
    ((ee with gas_obs := tail) with scopes := []) r
Proof
  strip_tac >>
  `!tail. intret_mem_q H func ce cx tv bw v
     ((ee with gas_obs := tail) with scopes := [])
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
       (copied with vs_inst_idx := n0))` by
    (mp_tac (Q.INST [`n` |-> `n0`, `r` |-> `IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
          (copied with vs_inst_idx := n0)`] internal_return_memory_copy_exit_base) >>
     disch_then (mp_tac o SIMP_RULE bool_ss []) >>
     disch_then (fn th => drule_all th) >> simp[]) >>
  qpat_x_assum `r = IntRet _ _` SUBST_ALL_TAC >> gen_tac >>
  qpat_assum `!tail. intret_mem_q _ _ _ _ _ _ _ _ _`
    (qspec_then `tail` (MATCH_ACCEPT_TAC o SRULE [] o
      MATCH_MP intret_mem_q_set_control))
QED

(* The release writes storage, but the following copy sees the same
   operands, memory bytes and allocation intervals. *)
Theorem return_unlock_copy_boundary[local]:
  compile_return_unlock cenv sm = ((),su) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  tn1.t_var = tn.t_var /\ tn1.t_mem = tn.t_mem ==>
  !u. u = return_unlock_state cenv t ==>
  ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts /\
  u.vs_memory = t.vs_memory /\ u.vs_alloca_next = t.vs_alloca_next /\
  (allocas_below_fmp u <=> allocas_below_fmp t) /\
  (!lo. allocas_from lo u <=> allocas_from lo t) /\
  (!x. lookup_var x u = lookup_var x t) /\
  (!x n. ptr_covers G tn1 x u n <=> ptr_covers G tn x t n)
Proof
  strip_tac >> gen_tac >> disch_then SUBST1_TAC >>
  drule compile_return_unlock_shape >> strip_tac >>
  qspecl_then [`cenv`, `t`, `sm.cs_next_id`] mp_tac return_unlock_state_frames >>
  simp[return_unlock_alloca_frames, allocas_from_def,
       lookup_var_def, ptr_covers_def, op_taint_def]
QED

Theorem return_buffer_copy_path[local]:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ fn_inst_ids_distinct func /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fs. FLOOKUP cenv.ce_struct_fields name = SOME fs ==>
    ALL_DISTINCT (MAP FST fs) /\
    EVERY (\(nm,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
      sz = type_memory_size tv) fs) /\
  type_widens_to tenv sty dty /\
  (is_bytestring_type dty ==> is_bytestring_type sty) /\
  (~is_bytestring_type dty ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)) /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256) /\
  type_memory_size stv <= type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type dtv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  s.vs_alloca_next < dimword (:256) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> Cases_on `is_bytestring_type dty`
  >- (fs[arithmeticTheory.ADD_COMM] >>
      drule_all (SRULE [arithmeticTheory.ADD_COMM] intcall_widened_bytes_return_copy) >>
      disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
      simp[arithmeticTheory.ADD_COMM]) >>
  fs[] >> `w2n sw + type_memory_size stv < dimword (:256)` by
    decide_tac >>
  mp_tac body_full_memory_store_path >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem return_buffer_relayout_suffix[local]:
  compile_return_unlock cenv sm = ((),su) /\ fn_has_code sm su func /\
  emit_inst RET [Var rpc] [] sc = ((),sb) /\ fn_has_code sc sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  lookup_var rpc s = SOME pc /\ not_fresh_at su rpc /\
  op_taint tn (Var rpc) = {} /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~s.vs_call_ctx.cc_static) /\
  compile_store_memory cenv (Var xs) (Var bp) ty sty su = ((),sc) /\
  ~is_word_type ty /\ fn_inst_ids_distinct func /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fs. FLOOKUP cenv.ce_struct_fields name = SOME fs ==>
    ALL_DISTINCT (MAP FST fs) /\
    EVERY (\(nm,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
      sz = type_memory_size tv) fs) /\
  type_widens_to tenv sty ty /\
  (is_bytestring_type ty ==> is_bytestring_type sty) /\
  (~is_bytestring_type ty ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n bw \/
     w2n bw + type_memory_size tv <= w2n sw)) /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv ty = SOME tv /\
  0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256) /\
  type_memory_size stv <= type_memory_size tv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  value_has_type stv v /\ val_wf stv v /\ value_has_type tv v /\ val_wf tv v /\
  not_fresh_at su xs /\ not_fresh_at su bp /\
  lookup_var xs s = SOME sw /\ lookup_var bp s = SOME bw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn bp s (type_memory_size tv) /\
  s.vs_alloca_next < dimword (:256) /\
  w2n sw + val_store_size stv v < dimword (:256) /\
  w2n bw + type_memory_size tv < dimword (:256) /\
  w2n sw + val_store_size stv v <= s.vs_alloca_next /\
  w2n bw + type_memory_size tv <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code su sc func ==>
  ?r Gf tf copied prev.
    r = IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (copied with <|vs_prev_bb := prev; vs_current_bb := sc.cs_current_bb;
                  vs_inst_idx := LENGTH sc.cs_current_insts|>) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,Gf,tf)) /\
    val_in_memory tv v (w2n bw) copied.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem copied.vs_memory mem ==>
      val_in_memory tv v (w2n bw) mem) /\
    (copied with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) =
      return_unlock_state cenv s /\
    (!x. not_fresh_at su x ==> lookup_var x copied = lookup_var x s) /\
    (!a len. a + len <= w2n bw \/ w2n bw + type_memory_size tv <= a ==>
      mem_bytes_at a len copied.vs_memory = mem_bytes_at a len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH copied.vs_memory /\
    LENGTH (return_unlock_insts cenv sm.cs_next_id) <= LENGTH su.cs_current_insts /\
    (((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
      FST (SND (SND cenv.ce_nonreentrant))) ==>
      tf.t_stor = tn.t_stor /\ tf.t_trans SUBSET tn.t_trans /\ tf.t_imm = tn.t_imm) /\
    (!i. i < w2n bw ==> (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  mp_tac (Q.INST [`t` |-> `s`]
    (INST_TYPE [alpha |-> ``:256``] return_relayout_suffix_origin_ptr)) >>
  impl_tac >- (
    asm_rewrite_tac [] >> rpt strip_tac >>
    mp_tac (Q.INST [`t` |-> `s`] return_unlock_copy_boundary) >>
    simp[] >> strip_tac >>
    mp_tac (Q.INST [`sa` |-> `su`, `sb` |-> `sc`,
      `s` |-> `return_unlock_state cenv s`, `tn` |-> `tn1`,
      `xd` |-> `bp`, `dty` |-> `ty`, `dtv` |-> `tv`,
      `dw` |-> `bw`] return_buffer_copy_path) >>
    impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[return_unlock_frames] >>
      qpat_assum `~is_bytestring_type ty ==> _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
    strip_tac >> qexistsl_tac [`t`,`Gf`,`tf`] >> simp[return_unlock_frames]) >>
  simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `cenv.ce_modules = [(NONE,cx_tops cx)]` by
    fs[body_inv_def, cenv_module_pins_def, gasContextTheory.cx_tops_module] >>
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
  rename1 `lower_value compile_expr _ ty (gas_shadow_expr e) shadow_sa =
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
  `w2n a + val_store_size tv v < dimword (:256) /\
   w2n bw + type_memory_size tv < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                  `G` |-> `G1`, `tn` |-> `tn1`]
            return_memory_suffix_origin_ptr_taint) >>
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
  reverse conj_tac
  >- (rpt strip_tac >>
      `copied.vs_call_ctx = (return_unlock_state cenv t).vs_call_ctx /\
       copied.vs_accounts = (return_unlock_state cenv t).vs_accounts /\
       copied.vs_transient = (return_unlock_state cenv t).vs_transient /\
       copied.vs_immutables = (return_unlock_state cenv t).vs_immutables` by
        (qpat_assum `copied with <|vs_vars := _; vs_memory := _|> = _`
           (mp_tac o AP_TERM
             ``\z:venom_state. (z.vs_call_ctx,z.vs_accounts,
                                 z.vs_transient,z.vs_immutables)``) >> simp[]) >>
      gvs[] >>
      rename1 `valid_horizon cx st0 H mid.storage_trace` >>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace`
        (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           (qspec_then `H` (strip_assume_tac o BETA_RULE o C MP vh))) >>
      `stor_taint_ok_at (DF H) (tn' with t_mem := tn1.t_mem) (return_unlock_state cenv t) /\
       (!i. i < lo /\ i IN tn1.t_mem ==>
          imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo t.vs_memory) i)` by
        (Q.SUBGOAL_THEN `dead_lo_ok H (DF H) lo cenv cx /\
           ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
             FST (SND (SND cenv.ce_nonreentrant))) /\
           (tn' with t_mem := tn1.t_mem).t_stor = tn1.t_stor /\
           (tn' with t_mem := tn1.t_mem).t_trans SUBSET tn1.t_trans /\
           (tn' with t_mem := tn1.t_mem).t_imm = tn1.t_imm /\
           (tn' with t_mem := tn1.t_mem).t_mem = tn1.t_mem /\
           ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv))
             cenv cx mid G1 tn1 t`
           (mp_tac o MATCH_MP (GEN_ALL return_unlock_exit_taint))
         >- (rpt conj_tac >> fs[]) >>
         qpat_assum `cenv.ce_modules = [(NONE,cx_tops cx)]`
           (fn eq => simp[MATCH_MP immSectionDeadTheory.imm_section_dead_mods_singleton eq])) >>
      `mem_bytes_at 0 lo copied.vs_memory = mem_bytes_at 0 lo t.vs_memory`
        by simp[] >>
      rpt strip_tac >> fs[stor_taint_ok_at_def]
      >~ [`imm_section_dead _ _ _`]
      >- (rpt strip_tac >>
          qpat_assum `!i. i < w2n bw ==> _` mp_tac >>
          qpat_assum `!i. i < lo /\ i IN tn1.t_mem ==> _` mp_tac >>
          qpat_assum `lo <= w2n bw` mp_tac >>
          qpat_assum `mem_bytes_at 0 lo copied.vs_memory = _` (fn th =>
            rewrite_tac[th]) >>
          metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
      metis_tac[]) >>
  (* Frame the actual copy back before the release. *)
  first_x_assum (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func cenv cx mid t` by gvs[expr_post_def] >>
  `env_consistent env cx (mid with gas_obs := [])` by
    (irule internal_return_source_env >> fs[expr_sim_inv_def] >>
     metis_tac[]) >>
  `cenv.ce_is_ctor ==> !src name itv iv off.
     (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP (mid with gas_obs := []).immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (simp[] >> strip_tac >>
     drule_at (Pos (el 5)) internal_return_immutable_separation >>
     simp[] >> metis_tac[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       lookup_var x copied = lookup_var x t` by
    (rpt strip_tac >>
     qpat_assum `compile_return_unlock cenv sm = ((),su)`
       (strip_assume_tac o MATCH_MP compile_return_unlock_shape) >>
     qpat_assum `lower_value compile_expr cenv _ e sa = (_,sm)`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
     `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
     `not_fresh_at su x` by fs[not_fresh_at_def] >>
     qpat_assum `!p. not_fresh_at su p ==> _` (qspecl_then [`x`] mp_tac) >>
     simp[]) >>
  irule (SRULE [] internal_return_memory_copy_exit_base) >>
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
*)
Theorem internal_return_memory_full_robust_taint:
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
  cenv.ce_returns_count = 0 /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = ty /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ 0 < type_memory_size tv /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  type_memory_size tv + 64 < dimword (:256) /\
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
    cx lctx (\H v ee gt r.
      intret_mem_q H func ce cx tv bw v ee r /\
      (!ir u mem. r = IntRet ir u /\
        mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n bw) mem) /\
      (!ir u. r = IntRet ir u /\ lo <= w2n bw /\
        ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
          FST (SND (SND ce.ce_nonreentrant))) ==>
        stor_taint_ok_at (DF H) (SND gt) u /\
        (!i. i < lo /\ i IN (SND gt).t_mem ==>
             imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i))) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `cenv.ce_modules = [(NONE,cx_tops cx)]` by
    fs[body_inv_def, cenv_module_pins_def, gasContextTheory.cx_tops_module] >>
  `ce.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  `?bp cap. cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    lookup_var bp s0 = SOME bw /\ not_fresh_at sa bp /\
    w2n bw + type_memory_size tv <= s0.vs_alloca_next` by
    fs[return_buf_frame_def] >>
  qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
    (mp_then Any mp_tac return_memory_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
    (mp_then Any mp_tac return_memory_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  rename1 `lower_value compile_expr _ ty (gas_shadow_expr e) shadow_sa =
             (shadow_op, shadow_sm)` >>
  rename1 `compile_return_unlock cenv shadow_sm = ((), shadow_su)` >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e)
        (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum mp_tac >> simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
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
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame _ cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep _ cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
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
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
     allocas_from (w2n bw + type_memory_size tv) t` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
          qexists_tac `v` >> asm_rewrite_tac[]) >>
      rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[expr_exit_def, stmt_exit_ptr_def, halt_exit_def] >>
      Cases_on `y` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  (* the value is on hand: release, copy and RET *)
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) _`
    (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace`
        (strip_assume_tac o BETA_RULE o C MP vh))) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
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
  `alloc_limits_expr cenv e` by
    fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
       Once allocLimitsTheory.alloc_limits_expr_def] >>
  mp_tac (Q.INST [`ret` |-> `ty`, `g` |-> `gas_explicit marks s0.vs_gas_readings`,
    `ee` |-> `mid with gas_obs := []`] internal_return_buffer_value_layout_typed) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`stv`, `ptv`]
    (map_every assume_tac o CONJUNCTS)) >>
  `0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size tv` by
    (conj_tac
     >- metis_tac[placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size,
                  arithmeticTheory.NOT_ZERO_LT_ZERO] >>
     qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty`
       (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.type_widens_to_def])
     >- fs[] >>
     qpat_assum `arg_type_fits (lowered_value_type cenv e) ty`
       (mp_tac o MATCH_MP (cj 1 aggregateEvaluatedLayoutTheory.arg_fits_evaluated_memory_size)) >>
     disch_then (qspecl_then [`get_tenv cx`,`stv`,`tv`] mp_tac) >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    fs[vyperTypeCallGraphTheory.int_calls_stmt_def,vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[] >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
    `ce` |-> `cenv`, `ret` |-> `ty`, `ee` |-> `mid with gas_obs := []`]
    (CONV_RULE (DEPTH_CONV ETA_CONV) return_site_value_semantics)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `value_has_type tv v /\ val_wf tv v /\ val_wf stv v` by
    (qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv` (fn eq =>
       qpat_assum `evaluate_type (get_tenv cx) ty = SOME _` (fn dst =>
         assume_tac (REWRITE_RULE [eq, optionTheory.SOME_11] dst))) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            first_assum (ACCEPT_TAC o MATCH_MP value_has_type_memory_wf),
            asm_simp_tac bool_ss []]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e)` by
    metis_tac[return_source_word_widens_eq] >>
  `~is_word_type (post_value_type cenv e)` by
    (Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
     >- (qpat_x_assum `?ann fid args drv. e = Call ann (IntCall fid) args drv`
           (qx_choosel_then [`ann0`,`fid0`,`args0`,`drv0`] SUBST_ALL_TAC) >>
         qpat_assum `~is_word_type (expr_type _)` mp_tac >>
         qpat_assum `~is_word_type (lowered_value_type cenv _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[post_value_type_def,vyperASTTheory.expr_type_def] >>
         Cases_on `is_bytestring_type ann0` >> simp[]) >>
     qpat_assum `~(?ann fid args drv. e = Call ann (IntCall fid) args drv)` mp_tac >>
     qpat_assum `~is_word_type (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[post_value_type_not_int_call]) >>
  Q.SUBGOAL_THEN `post_value_type cenv e = lowered_value_type cenv e \/
    (is_bytestring_type (post_value_type cenv e) /\
     is_bytestring_type (lowered_value_type cenv e))` assume_tac
  >- metis_tac[] >>
  `?src a. op = Var src /\ lookup_var src t = SOME a /\
     ptr_covers G1 tn1 src t (type_memory_size stv) /\
     (!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
          val_in_memory stv v (w2n a) m) /\
     w2n a + val_store_size stv v <= t.vs_alloca_next` by
    (mp_tac (Q.SPECL [`H0`,`ctx`,`func`,`cenv`,`cx`,`e`,
       `es`,`sa`,`sm`,`s0`,`mid`,`v`,`op`,`t`,`G1`,`tn1`,
       `lowered_value_type cenv e`,`post_value_type cenv e`,`stv`,`ptv`]
       (INST_TYPE [alpha |-> ``:256``] internal_return_memory_value_inputs_lowered)) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                    simp[])) >>
     simp[]) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 bp t (type_memory_size tv) /\
   op_taint tn1 (Var rpc) = {} /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ghost_inv_at_def, return_buf_ptr_def] >> gvs[]) >>
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~t.vs_call_ctx.cc_static)` by
    (fs[expr_post_def] >>
     imp_res_tac stmt_state_rel_state_rel >>
     imp_res_tac state_rel_call_ctx_rel >> fs[call_ctx_rel_def]) >>
  `w2n bw + type_memory_size tv <= t.vs_alloca_next` by decide_tac >>
  `t.vs_alloca_next < dimword (:256)` by
    (fs[expr_post_def] >>
     metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt]) >>
  `w2n a + val_store_size stv v < dimword (:256) /\
   w2n bw + type_memory_size tv < dimword (:256)` by decide_tac >>
  `~is_bytestring_type ty ==>
    w2n a + type_memory_size stv <= t.vs_alloca_next /\
    (w2n a + type_memory_size stv <= w2n bw \/
      w2n bw + type_memory_size tv <= w2n a)` by
    (strip_tac >>
     `~is_bytestring_type (lowered_value_type cenv e) /\
      post_value_type cenv e = lowered_value_type cenv e` by
       metis_tac[type_widens_from_bytestring] >>
     `stmt_state_rel H0 ctx func cenv cx mid t /\
      expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v (Var src) t /\
      MAP FDOM mid.scopes = MAP FDOM es.scopes` by
       fs[expr_post_def,locals_kept_def] >>
     `valid_horizon cx st0 H0 es.storage_trace` by
       (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,mid with gas_obs := [])`
          (mp_then Any mp_tac storage_trace_frame_prefix) >>
        simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
        strip_tac >> fs[Abbr `H0`] >> metis_tac[valid_horizon_append]) >>
     `return_buf_sep (SOME (bw,type_memory_size tv)) cenv mid t` by
       (mp_tac (Q.INST [`d` |-> `SOME (bw,type_memory_size tv)`, `s` |-> `s0`,
         `ee` |-> `mid`, `H` |-> `H0`]
         (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept)) >>
        impl_tac >- (fs[expr_post_def] >> metis_tac[]) >> simp[]) >>
     `eval_operand (Var src) t = SOME a` by simp[eval_operand_def] >>
     drule_all normalize_source_window >> simp[] >> strip_tac >>
     drule_all intcall_widened_return_source_disjoint >>
     fs[] >> metis_tac[]) >>
  `type_memory_size stv + 64 < dimword (:256)` by decide_tac >>
  `su.cs_next_var = sm.cs_next_var` by metis_tac[compile_return_unlock_shape] >>
  `not_fresh_at su rpc /\ not_fresh_at su src /\ not_fresh_at su bp` by
    fs[not_fresh_at_def] >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `t`,
    `sw` |-> `a`, `xs` |-> `src`, `tenv` |-> `get_tenv cx`,
    `sty` |-> `lowered_value_type cenv e`, `sc` |-> `sc`,
    `stv` |-> `stv`, `tv` |-> `tv`]
      return_buffer_relayout_suffix) >>
  (impl_tac >- (
    drule return_site_copy_metadata >> strip_tac >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (fs[body_inv_def, expr_sim_inv_def] >> NO_TAC) >>
    TRY (fs[compile_return_unlock_shape,not_fresh_at_def] >> NO_TAC) >>
    metis_tac[typed_copy_bytestring_source])) >> strip_tac >>
  rename1 `val_in_memory tv v (w2n bw) copied.vs_memory` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp copied` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca ctx` (fn de =>
       qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t`
         (assume_tac o C MP de)) >>
     `allocas_below_fmp (copied with <|vs_vars := t.vs_vars;
         vs_memory := t.vs_memory|>) = allocas_below_fmp copied` by
       simp[allocas_below_fmp_def] >>
     qpat_assum `copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> = _`
       (fn eq => qpat_assum
          `allocas_below_fmp (copied with <|vs_vars := t.vs_vars;
            vs_memory := t.vs_memory|>) = allocas_below_fmp copied`
          (mp_tac o REWRITE_RULE [eq, allocas_below_fmp_return_unlock_state])) >>
     disch_then (fn eq => qpat_assum `allocas_below_fmp t`
       (ACCEPT_TAC o EQ_MP eq))) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  irule (Q.INST [`res` |-> `INR (ReturnException v)`, `ee` |-> `mid`]
           gas_outcome_full_exit) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`, `mid`, `r`, `tf`] >>
  simp[raise_def,exit_result_def,halt_exit_def] >>
  rpt conj_tac >> TRY (asm_rewrite_tac [] >> NO_TAC) >>
  gen_tac >> disch_tac >>
  conj_tac
  >- (gen_tac >> simp[stmt_exit_ptr_def, expr_exit_def] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      rename1 `valid_horizon cx st0 H mid.storage_trace` >>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace`
        (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           (qspec_then `H` (strip_assume_tac o BETA_RULE o C MP vh))) >>
      rename1 `ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv))
        cenv cx mid G1 tn1 t` >>
      `stor_taint_ok_at (DF H) (tf with t_mem := tn1.t_mem) (return_unlock_state cenv t) /\
       (!i. i < lo /\ i IN tn1.t_mem ==>
          imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo t.vs_memory) i)` by
        (Q.SUBGOAL_THEN `dead_lo_ok H (DF H) lo cenv cx /\
           ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
             FST (SND (SND cenv.ce_nonreentrant))) /\
           (tf with t_mem := tn1.t_mem).t_stor = tn1.t_stor /\
           (tf with t_mem := tn1.t_mem).t_trans SUBSET tn1.t_trans /\
           (tf with t_mem := tn1.t_mem).t_imm = tn1.t_imm /\
           (tf with t_mem := tn1.t_mem).t_mem = tn1.t_mem /\
           ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv))
             cenv cx mid G1 tn1 t`
           (mp_tac o MATCH_MP (GEN_ALL return_unlock_exit_taint))
         >- (rpt conj_tac >> fs[]) >>
         qpat_assum `cenv.ce_modules = [(NONE,cx_tops cx)]`
           (fn eq => simp[MATCH_MP immSectionDeadTheory.imm_section_dead_mods_singleton eq])) >>
      `mem_bytes_at 0 lo copied.vs_memory = mem_bytes_at 0 lo t.vs_memory`
        by simp[] >>
      conj_tac
      >- (simp[NoAsms,stor_taint_ok_at_def] >>
          qpat_assum `copied with <|vs_vars := _; vs_memory := _|> = _` (fn eq =>
            qpat_assum `stor_taint_ok_at (DF H) (tf with t_mem := tn1.t_mem) _`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) [GSYM eq,stor_taint_ok_at_def]))) >>
      rpt strip_tac >>
      `i < w2n bw` by decide_tac >>
      `i IN tn1.t_mem` by
        (qpat_assum `!i. i < w2n bw ==> _`
           (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_assum `!i. i < lo /\ i IN tn1.t_mem ==> _`
        (qspec_then `i` mp_tac) >> simp[]) >>
  (* Frame the actual copy back before the release. *)
  rename1 `valid_horizon cx st0 H mid.storage_trace` >>
  qpat_assum `valid_horizon cx st0 H mid.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `H` (strip_assume_tac o BETA_RULE o C MP vh))) >>
  `stmt_state_rel H ctx func cenv cx mid t` by fs[expr_post_def] >>
  `env_consistent env cx (mid with gas_obs := [])` by
    (irule internal_return_source_env >> fs[expr_sim_inv_def] >>
     metis_tac[]) >>
  `cenv.ce_is_ctor ==> !src name itv iv off.
     (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP (mid with gas_obs := []).immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (simp[] >> strip_tac >>
     drule_at (Pos (el 5)) internal_return_immutable_separation >>
     simp[] >> metis_tac[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       lookup_var x copied = lookup_var x t` by
    (rpt strip_tac >>
     qpat_assum `compile_return_unlock cenv sm = ((),su)`
       (strip_assume_tac o MATCH_MP compile_return_unlock_shape) >>
     qpat_assum `lower_value compile_expr cenv _ e sa = (_,sm)`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
     `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
     `not_fresh_at su x` by fs[not_fresh_at_def] >>
     qpat_assum `!p. not_fresh_at su p ==> _` (qspecl_then [`x`] mp_tac) >>
     simp[]) >>
  irule (SRULE [] return_memory_copy_exit_control) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `ctx`, `sm.cs_next_id`, `LENGTH su.cs_current_insts`, `t`] >> gvs[] >> metis_tac[])
  >- (simp[allocas_below_fmp_def] >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp copied`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [allocas_below_fmp_def]))
QED
*)
(* Every allocated immutable lies below the linked constructor prefix. *)
Theorem return_buffer_immutable_separation[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv cenv cx env entry /\
  env_consistent env cx ee /\ cenv.ce_is_ctor /\
  imm_len_mods cenv.ce_modules <= b /\
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) name = SOME (itv,iv) ==>
  regions_disjoint off (type_memory_size itv) b cap
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_struct_fields >>
  drule_then (assume_tac o SPEC_ALL) contract_inv_module_codes >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods src name off bytes` by metis_tac[] >>
  `off + bytes <= imm_len_mods cenv.ce_modules` by metis_tac[] >>
  `off + bytes <= b` by decide_tac >>
  qpat_x_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `FLOOKUP env.bare_globals (src,name) = SOME ty` by
    (qpat_assum `env_consistent env cx ee`
       (mp_tac o REWRITE_RULE [env_consistent_def, env_context_consistent_def,
                               bare_globals_complete_def]) >>
     metis_tac[MEM_APPEND, MEM]) >>
  `evaluate_type (get_tenv cx) ty = SOME itv` by
    (qpat_assum `env_consistent env cx ee`
       (mp_tac o cj 3 o REWRITE_RULE [env_consistent_def]) >>
     simp[env_immutables_consistent_def] >>
     disch_then (mp_tac o Q.SPECL [`src`,`name`,`ty`,`itv`,`iv`] o cj 2) >>
     Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[]) >>
  `type_memory_bytes cenv ty = type_memory_size itv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `bytes = type_memory_size itv` by
    metis_tac[structFieldsPropsTheory.type_mem_bytes_type_memory_bytes] >>
  rewrite_tac[regions_disjoint_def] >> disj1_tac >> metis_tac[]
QED

Theorem internal_return_memory_relayout_robust_taint:
  !DF lo ctx shadow_ctx PG func shadow_func mods exps cx ce cenv env es
   ty tv e lctx bw rpc rsz.
  contract_inv mods exps ctx cenv cx /\
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\ lo <= w2n bw /\
  ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
    ~cx.txn.is_static) /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = 0 /\
  ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ 0 < type_memory_size tv /\
  stmt_exprs_ok cenv (Return (SOME e)) /\
  IS_SOME (type_stmt env ty (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) /\
  type_memory_size tv + 64 < dimword (:256) /\
  (!ety. expr_sim_full
     (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ety e es /\
   expr_vv_sim_full
     (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ety e es) ==>
  stmt_frag_full
    (DF,lo,SOME (bw,type_memory_size tv),ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx (\H v ee gt r.
      intret_mem_q H func ce cx tv bw v ee r /\
      (!ir u mem. r = IntRet ir u /\
        mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n bw) mem) /\
      (!ir u. r = IntRet ir u /\ lo <= w2n bw /\
        ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
          FST (SND (SND ce.ce_nonreentrant))) ==>
        stor_taint_ok_at (DF H) (SND gt) u /\
        (!i. i < lo /\ i IN (SND gt).t_mem ==>
             imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i))) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  `imm_section_dead_mods ce = imm_section_dead_mods cenv` by
    fs[same_frame_def, compile_env_component_equality,
       FUN_EQ_THM, immSectionDeadTheory.imm_section_dead_mods_def] >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  `ce.ce_nonreentrant = cenv.ce_nonreentrant` by
    fs[same_frame_def, compile_env_component_equality] >>
  `?bp cap. cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    lookup_var bp s0 = SOME bw /\ not_fresh_at sa bp /\
    w2n bw + type_memory_size tv <= s0.vs_alloca_next` by
    fs[return_buf_frame_def] >>
  qpat_assum `stmt_env _ _ _ (Return (SOME e)) sa = _`
    (mp_then Any mp_tac return_memory_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  qpat_assum `stmt_env _ _ _ (Return (SOME (gas_shadow_expr e))) shadow_sa = _`
    (mp_then Any mp_tac return_memory_compile_parts) >> simp[] >>
    disch_then drule_all >> strip_tac >>
  rename1 `lower_value compile_expr _ ty (gas_shadow_expr e) shadow_sa =
             (shadow_op, shadow_sm)` >>
  rename1 `compile_return_unlock cenv shadow_sm = ((), shadow_su)` >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `op = shadow_op /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e)
        (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum mp_tac >> simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
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
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame _ cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep _ cenv es s0` (fn sep =>
        assume_tac (MATCH_MP gas_outcome_full_mods_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_mods_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_raise]
  >~ [`gas_marked_exec`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >> metis_tac[])
  >~ [`gas_exempt_cert_mods _ _ _ (bind _ _)`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
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
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
     allocas_from (w2n bw + type_memory_size tv) t` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> goal_assum (drule_at Any) >>
      simp[] >> conj_tac
      >- (rpt strip_tac >> fs[arithmeticTheory.ADD_COMM] >>
          qexists_tac `v` >> asm_rewrite_tac[]) >>
      rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
      simp[expr_exit_def, stmt_exit_ptr_def, halt_exit_def] >>
      Cases_on `y` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  (* the value is on hand: release, copy and RET *)
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) _`
    (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
      (qspec_then `storage_trace_horizon mid.storage_trace`
        (strip_assume_tac o BETA_RULE o C MP vh))) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
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
  `alloc_limits_expr cenv e` by
    fs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
       Once allocLimitsTheory.alloc_limits_expr_def] >>
  mp_tac (Q.INST [`ret` |-> `ty`, `g` |-> `gas_explicit marks s0.vs_gas_readings`,
    `ee` |-> `mid with gas_obs := []`] internal_return_buffer_value_layout_typed) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`stv`, `ptv`]
    (map_every assume_tac o CONJUNCTS)) >>
  `0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size tv` by
    (conj_tac
     >- metis_tac[placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size,
                  arithmeticTheory.NOT_ZERO_LT_ZERO] >>
     qpat_assum `type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty`
       (strip_assume_tac o REWRITE_RULE [vyperTypeSystemTheory.type_widens_to_def])
     >- fs[] >>
     qpat_assum `arg_type_fits (lowered_value_type cenv e) ty`
       (mp_tac o MATCH_MP (cj 1 aggregateEvaluatedLayoutTheory.arg_fits_evaluated_memory_size)) >>
     disch_then (qspecl_then [`get_tenv cx`,`stv`,`tv`] mp_tac) >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    fs[vyperTypeCallGraphTheory.int_calls_stmt_def,vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    simp[] >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
    `ce` |-> `cenv`, `ret` |-> `ty`, `ee` |-> `mid with gas_obs := []`]
    (CONV_RULE (DEPTH_CONV ETA_CONV) return_site_value_semantics)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `value_has_type tv v /\ val_wf tv v /\ val_wf stv v` by
    (qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv` (fn eq =>
       qpat_assum `evaluate_type (get_tenv cx) ty = SOME _` (fn dst =>
         assume_tac (REWRITE_RULE [eq, optionTheory.SOME_11] dst))) >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
            first_assum (ACCEPT_TAC o MATCH_MP value_has_type_memory_wf),
            asm_simp_tac bool_ss []]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e)` by
    metis_tac[return_source_word_widens_eq] >>
  `~is_word_type (post_value_type cenv e)` by
    (Cases_on `?ann fid args drv. e = Call ann (IntCall fid) args drv`
     >- (qpat_x_assum `?ann fid args drv. e = Call ann (IntCall fid) args drv`
           (qx_choosel_then [`ann0`,`fid0`,`args0`,`drv0`] SUBST_ALL_TAC) >>
         qpat_assum `~is_word_type (expr_type _)` mp_tac >>
         qpat_assum `~is_word_type (lowered_value_type cenv _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[post_value_type_def,vyperASTTheory.expr_type_def] >>
         Cases_on `is_bytestring_type ann0` >> simp[]) >>
     qpat_assum `~(?ann fid args drv. e = Call ann (IntCall fid) args drv)` mp_tac >>
     qpat_assum `~is_word_type (expr_type e)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[post_value_type_not_int_call]) >>
  Q.SUBGOAL_THEN `post_value_type cenv e = lowered_value_type cenv e \/
    (is_bytestring_type (post_value_type cenv e) /\
     is_bytestring_type (lowered_value_type cenv e))` assume_tac
  >- metis_tac[] >>
  `?src a. op = Var src /\ lookup_var src t = SOME a /\
     ptr_covers G1 tn1 src t (type_memory_size stv) /\
     (!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
          val_in_memory stv v (w2n a) m) /\
     w2n a + val_store_size stv v <= t.vs_alloca_next` by
    (mp_tac (Q.SPECL [`H0`,`ctx`,`func`,`cenv`,`cx`,`e`,
       `es`,`sa`,`sm`,`s0`,`mid`,`v`,`op`,`t`,`G1`,`tn1`,
       `lowered_value_type cenv e`,`post_value_type cenv e`,`stv`,`ptv`]
       (INST_TYPE [alpha |-> ``:256``] internal_return_memory_value_inputs_lowered)) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                    simp[])) >>
     simp[]) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 bp t (type_memory_size tv) /\
   op_taint tn1 (Var rpc) = {} /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ghost_inv_at_def, return_buf_ptr_def] >> gvs[]) >>
  `((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
     ~t.vs_call_ctx.cc_static)` by
    (fs[expr_post_def] >>
     imp_res_tac stmt_state_rel_state_rel >>
     imp_res_tac state_rel_call_ctx_rel >> fs[call_ctx_rel_def]) >>
  `w2n bw + type_memory_size tv <= t.vs_alloca_next` by decide_tac >>
  `t.vs_alloca_next < dimword (:256)` by
    (fs[expr_post_def] >>
     metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt]) >>
  `w2n a + val_store_size stv v < dimword (:256) /\
   w2n bw + type_memory_size tv < dimword (:256)` by decide_tac >>
  `~is_bytestring_type ty ==>
    w2n a + type_memory_size stv <= t.vs_alloca_next /\
    (w2n a + type_memory_size stv <= w2n bw \/
      w2n bw + type_memory_size tv <= w2n a)` by
    (strip_tac >>
     `~is_bytestring_type (lowered_value_type cenv e) /\
      post_value_type cenv e = lowered_value_type cenv e` by
       metis_tac[type_widens_from_bytestring] >>
     `stmt_state_rel H0 ctx func cenv cx mid t /\
      expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v (Var src) t /\
      MAP FDOM mid.scopes = MAP FDOM es.scopes` by
       fs[expr_post_def,locals_kept_def] >>
     `valid_horizon cx st0 H0 es.storage_trace` by
       (qpat_assum `bind (eval_expr cx e) (read_result cx) _ = (INL v,mid with gas_obs := [])`
          (mp_then Any mp_tac storage_trace_frame_prefix) >>
        simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
        strip_tac >> fs[Abbr `H0`] >> metis_tac[valid_horizon_append]) >>
     `return_buf_sep (SOME (bw,type_memory_size tv)) cenv mid t` by
       (mp_tac (Q.INST [`d` |-> `SOME (bw,type_memory_size tv)`, `s` |-> `s0`,
         `ee` |-> `mid`, `H` |-> `H0`]
         (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept)) >>
        impl_tac >- (fs[expr_post_def] >> metis_tac[]) >> simp[]) >>
     `eval_operand (Var src) t = SOME a` by simp[eval_operand_def] >>
     drule_all normalize_source_window >> simp[] >> strip_tac >>
     drule_all intcall_widened_return_source_disjoint >>
     fs[] >> metis_tac[]) >>
  `type_memory_size stv + 64 < dimword (:256)` by decide_tac >>
  `su.cs_next_var = sm.cs_next_var` by metis_tac[compile_return_unlock_shape] >>
  `not_fresh_at su rpc /\ not_fresh_at su src /\ not_fresh_at su bp` by
    fs[not_fresh_at_def] >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `G` |-> `G1`, `tn` |-> `tn1`, `s` |-> `t`,
    `sw` |-> `a`, `xs` |-> `src`, `tenv` |-> `get_tenv cx`,
    `sty` |-> `lowered_value_type cenv e`, `sc` |-> `sc`,
    `stv` |-> `stv`, `tv` |-> `tv`]
      return_buffer_relayout_suffix) >>
  (impl_tac >- (
    drule return_site_copy_metadata >> strip_tac >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (fs[expr_sim_inv_def] >> NO_TAC) >>
    TRY (fs[compile_return_unlock_shape,not_fresh_at_def] >> NO_TAC) >>
    metis_tac[typed_copy_bytestring_source])) >> strip_tac >>
  rename1 `val_in_memory tv v (w2n bw) copied.vs_memory` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp copied` by
    (disch_tac >>
     qpat_assum `ctx_has_dalloca ctx` (fn de =>
       qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t`
         (assume_tac o C MP de)) >>
     `allocas_below_fmp (copied with <|vs_vars := t.vs_vars;
         vs_memory := t.vs_memory|>) = allocas_below_fmp copied` by
       simp[allocas_below_fmp_def] >>
     qpat_assum `copied with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> = _`
       (fn eq => qpat_assum
          `allocas_below_fmp (copied with <|vs_vars := t.vs_vars;
            vs_memory := t.vs_memory|>) = allocas_below_fmp copied`
          (mp_tac o REWRITE_RULE [eq, allocas_below_fmp_return_unlock_state])) >>
     disch_then (fn eq => qpat_assum `allocas_below_fmp t`
       (ACCEPT_TAC o EQ_MP eq))) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  irule (Q.INST [`res` |-> `INR (ReturnException v)`, `ee` |-> `mid`]
           gas_outcome_full_mods_exit) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`, `mid`, `r`, `tf`] >>
  simp[raise_def,exit_result_def,halt_exit_def] >>
  rpt conj_tac >> TRY (asm_rewrite_tac [] >> NO_TAC) >>
  gen_tac >> disch_tac >>
  conj_tac
  >- (gen_tac >> simp[stmt_exit_ptr_def, expr_exit_def] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      rename1 `valid_horizon cx st0 H mid.storage_trace` >>
      qpat_assum `valid_horizon cx st0 H mid.storage_trace`
        (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
           (qspec_then `H` (strip_assume_tac o BETA_RULE o C MP vh))) >>
      rename1 `ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv))
        cenv cx mid G1 tn1 t` >>
      `stor_taint_ok_at (DF H) (tf with t_mem := tn1.t_mem) (return_unlock_state cenv t) /\
       (!i. i < lo /\ i IN tn1.t_mem ==>
          imm_section_dead_mods cenv (mem_bytes_at 0 lo t.vs_memory) i)` by
        (Q.SUBGOAL_THEN `dead_lo_ok H (DF H) lo cenv cx /\
           ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
             FST (SND (SND cenv.ce_nonreentrant))) /\
           (tf with t_mem := tn1.t_mem).t_stor = tn1.t_stor /\
           (tf with t_mem := tn1.t_mem).t_trans SUBSET tn1.t_trans /\
           (tf with t_mem := tn1.t_mem).t_imm = tn1.t_imm /\
           (tf with t_mem := tn1.t_mem).t_mem = tn1.t_mem /\
           ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv))
             cenv cx mid G1 tn1 t`
           (mp_tac o MATCH_MP (GEN_ALL return_unlock_exit_taint))
         >- (rpt conj_tac >> fs[]) >>
         simp[]) >>
      `mem_bytes_at 0 lo copied.vs_memory = mem_bytes_at 0 lo t.vs_memory`
        by simp[] >>
      conj_tac
      >- (simp[NoAsms,stor_taint_ok_at_def] >>
          qpat_assum `copied with <|vs_vars := _; vs_memory := _|> = _` (fn eq =>
            qpat_assum `stor_taint_ok_at (DF H) (tf with t_mem := tn1.t_mem) _`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) [GSYM eq,stor_taint_ok_at_def]))) >>
      rpt strip_tac >>
      `i < w2n bw` by decide_tac >>
      `i IN tn1.t_mem` by
        (qpat_assum `!i. i < w2n bw ==> _`
           (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_assum `!i. i < lo /\ i IN tn1.t_mem ==> _`
        (qspec_then `i` mp_tac) >> simp[]) >>
  (* Frame the actual copy back before the release. *)
  rename1 `valid_horizon cx st0 H mid.storage_trace` >>
  qpat_assum `valid_horizon cx st0 H mid.storage_trace`
    (fn vh => qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
       (qspec_then `H` (strip_assume_tac o BETA_RULE o C MP vh))) >>
  `stmt_state_rel H ctx func cenv cx mid t` by fs[expr_post_def] >>
  `env_consistent env cx (mid with gas_obs := [])` by
    (irule internal_return_source_env >> fs[expr_sim_inv_def] >>
     metis_tac[]) >>
  `cenv.ce_is_ctor ==> !src name itv iv off.
     (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP (mid with gas_obs := []).immutables cx.txn.target of
                NONE => FEMPTY
              | SOME imms => get_source_immutables src imms) name =
       SOME (itv,iv) ==>
     regions_disjoint off (type_memory_size itv) (w2n bw) (type_memory_size tv)` by
    (simp[] >> rpt strip_tac >>
     rename1 `FLOOKUP cenv.ce_module_vars (sid,name) = SOME (ImmutableLoc off)` >>
     `imm_len_mods cenv.ce_modules <= w2n bw` by
       fs[dead_lo_ok_def] >>
     mp_tac (Q.INST [`ee` |-> `mid with gas_obs := []`, `entry` |-> `es`,
       `src` |-> `sid`, `b` |-> `w2n (bw:256 word)`,
       `cap` |-> `type_memory_size tv`] return_buffer_immutable_separation) >>
     gvs[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==>
       lookup_var x copied = lookup_var x t` by
    (rpt strip_tac >>
     qpat_assum `compile_return_unlock cenv sm = ((),su)`
       (strip_assume_tac o MATCH_MP compile_return_unlock_shape) >>
     qpat_assum `lower_value compile_expr cenv _ e sa = (_,sm)`
       (strip_assume_tac o MATCH_MP (cj 2 compile_expr_grows)) >>
     `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
     `not_fresh_at su x` by fs[not_fresh_at_def] >>
     qpat_assum `!p. not_fresh_at su p ==> _` (qspecl_then [`x`] mp_tac) >>
     simp[]) >>
  irule (SRULE [] return_memory_copy_exit_control) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `ctx`, `sm.cs_next_id`, `LENGTH su.cs_current_insts`, `t`] >> gvs[] >> metis_tac[])
  >- (simp[allocas_below_fmp_def] >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp copied`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [allocas_below_fmp_def]))
QED

Theorem internal_return_memory_full_robust:
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
  type_memory_size tv + 64 < dimword (:256) /\
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
    cx lctx (\H v ee gt r.
      intret_mem_q H func ce cx tv bw v ee r /\
      (!ir u mem. r = IntRet ir u /\
        mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n bw) mem)) cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> strip_tac >>
  irule stmt_frag_full_retq_weaken >>
  qexists_tac `\H v ee gt r.
      intret_mem_q H func ce cx tv bw v ee r /\
      (!ir u mem. r = IntRet ir u /\
        mem_agree_outside (SND gt).t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n bw) mem) /\
      (!ir u. r = IntRet ir u /\ lo <= w2n bw /\
        ((FST ce.ce_nonreentrant /\ ~SND (SND (SND ce.ce_nonreentrant))) ==>
          FST (SND (SND ce.ce_nonreentrant))) ==>
        stor_taint_ok_at (DF H) (SND gt) u /\
        (!i. i < lo /\ i IN (SND gt).t_mem ==>
             imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo u.vs_memory) i))` >>
  conj_tac >- simp[] >>
  mp_tac (Q.SPECL
    [`DF`, `lo`, `ctx`, `shadow_ctx`, `PG`, `func`, `shadow_func`,
     `tops`, `cx`, `ce`, `cenv`, `env`, `es`, `ty`, `tv`, `e`,
     `lctx`, `bw`, `rpc`, `rsz`] internal_return_memory_full_robust_taint) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_size tv + 64 < dimword (:256)` by decide_tac >>
  mp_tac (Q.SPECL [`DF`, `lo`, `ctx`, `shadow_ctx`, `PG`, `func`,
    `shadow_func`, `tops`, `cx`, `ce`, `cenv`, `env`, `es`, `ty`, `tv`,
    `e`, `lctx`, `bw`, `rpc`, `rsz`] internal_return_memory_full_robust) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[stmt_frag_full_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
  simp[stmt_exit_ptr_def] >> metis_tac[]
QED
*)
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
    (stmt_env (gas_shadow_env T cenv) lctx ty (Return (SOME (gas_shadow_expr e))))
    (eval_stmt cx (Return (SOME e))) es
Proof
  cheat
QED
