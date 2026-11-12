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
  internalReturnImmutableTypes intCallReturnMem stmtSimReturn
  annAssignPtrMemorySource annAssignPtrDestination ptrSafetyTransport
  fragGasOriginPtrExec fragGasOriginPtr fragGasPathPtr gasPathPtrExec
  fragGasPathMem fragGasPath fragGasSeqMem fragExecMem fragExec
  bodyDeclMemoryCore bodyDeclCopyMemory exprSimBufferStore exprSimMemDefs
  exprSimProps exprSimHyps exprSimHypsDefs exprSimWordArgs returnValueTyped
  valueTypingMemoryProps tupleTargetStoreRun instMemFrontier valueCopy
  exprOperandVar stmtLoweringMono externalEntryShape
  bodySimFull bodySim bodyPtrDefs gasOutcomeFullCompose gasOutcomeFull
  gasShadowState gasShadow gasCount memSafeRun ptrSafeRun ptrDiscipline
  loweringPosts exprLoweringProps emitHelperProps emitHelper context
  compileEnv stmtLowering exprLowering freshWrites vyperTypeInvariants
  vyperState vyperInterpreter venomExecSemantics venomState venomInst
  list rich_list
Libs
  monadsyntax

Theorem internal_return_store_mem_ok[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >> gvs[]) >>
  `?w. eval_operand src s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by gvs[expr_val_rel_def] >>
  Cases_on `type_memory_size tv = 0`
  >- (`val_store_size tv v = 0` by
        (drule val_store_size_le >> simp[]) >>
      `~is_bytestring_type ty` by
        (strip_tac >> drule_all buffer_typed_bytestring_header >> simp[]) >>
      gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
          emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  `0 < val_store_size tv v` by metis_tac[val_store_size_pos, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `w2n w + val_store_size tv v <= s.vs_alloca_next` by
    (fs[expr_store_bound_def] >> gvs[]) >>
  irule body_typed_store_memory_mem_ok >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem internal_return_store_path_mem[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  w2n d + type_memory_size tv + 64 < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `?w. eval_operand src s = SOME w /\
       (if is_word_type ty then w = typed_val_to_w256 tv v
        else val_in_memory tv v (w2n w) s.vs_memory)` by
    gvs[expr_val_rel_def] >>
  `!x. src = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all compile_store_memory_run >> strip_tac >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  drule_all internal_return_store_mem_ok >> strip_tac >>
  drule tuple_local_copy_code_shape >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `sb.cs_current_insts = sa.cs_current_insts ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> gvs[]
QED


Theorem internal_ret_path_mem[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid RET ops []) /\
  step_inst_base (mk_inst iid RET ops []) s = IntRet ir t ==>
  gas_path_mem ctx func s 0 (IntRet ir t)
Proof
  strip_tac >> irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def] >>
  simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, mk_inst_def,
       mem_safe_step_non_invoke, below_frontier_no_ranges,
       inst_dload_in_section_def, exit_result_def]
QED

Theorem emit_internal_ret_path_mem[local]:
  emit_inst RET (ops ++ [Var rpc]) [] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operands ops s = SOME vals /\ lookup_var rpc s = SOME pc ==>
  gas_path_mem ctx func s 0
    (IntRet <|iret_values := vals; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) [])` by
    (drule fn_has_code_same_block >>
     disch_then (qspec_then `[mk_inst sa.cs_next_id RET (ops ++ [Var rpc]) []]`
       mp_tac) >> simp[] >> metis_tac[arithmeticTheory.ADD_CLAUSES]) >>
  irule internal_ret_path_mem >> simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `ops ++ [Var rpc]`] >>
  simp[] >> irule stmtSimReturnTheory.step_ret_values >> simp[] >> metis_tac[]
QED



Theorem internal_return_shadow_type[local]:
  lowered_value_type cenv (gas_shadow_expr e) = lowered_value_type cenv e
Proof
  Cases_on `e` >>
  simp[gasShadowTheory.gas_shadow_expr_def,
    exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]
  >- (Cases_on `b` >>
      simp[gasShadowTheory.gas_shadow_builtin_def,
        exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
      metis_tac[gasShadowTheory.gas_shadow_builtin_def,
        exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF])
  >- (Cases_on `t0` >>
      simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
        listTheory.MAP_MAP_o, combinTheory.o_DEF,
        gasShadowTheory.gas_shadow_expr_type] >>
      Cases_on `l` >> simp[gasShadowTheory.gas_shadow_expr_type, ETA_THM])
  >> Cases_on `c` >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]
QED

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

Theorem internal_return_buffer_ret_ptr[local]:
  emit_inst RET [Var rpc] [] sa = ((),sb) /\
  fn_has_code sa sb func /\ lookup_var rpc s = SOME pc /\
  op_taint tn (Var rpc) = {} /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s)
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `!fuel. step_inst fuel ctx (mk_inst sa.cs_next_id RET [Var rpc] []) s =
    IntRet <|iret_values := []; iret_adopt_fmp := NONE|> s` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     irule (step_ret_values |> Q.SPEC `sa.cs_next_id` |> Q.SPEC `[]` |> SRULE [mk_inst_def, eval_operands_def]) >>
     metis_tac[]) >>
  irule (cj 3 fragGasPathPtrTheory.gas_path_ptr_rules) >>
  simp[exit_result_def, fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
  qexists_tac `0` >>
  simp[gasCountTheory.gas_count_step_def, ptrSafeRunTheory.ptr_safe_step_def,
       ptrSafeRunTheory.ptr_inst_ok_def, mk_inst_def,
       ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       ptrDisciplineTheory.allocas_from_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
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
  `cs_extends sc sb'` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends sm su /\ cs_extends sm sb'` by metis_tac[cs_extends_trans] >>
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

Theorem stmt_state_rel_scopes_nil[local]:
  stmt_state_rel H ctx func cenv cx es s ==>
  stmt_state_rel H ctx func cenv cx (es with scopes := []) s
Proof
  rw[stmt_state_rel_def, state_rel_scopes_nil] >>
  fs[immutable_alloca_sep_def, immutable_decl_sep_def, local_region_def,
     lookup_scopes_def] >>
  metis_tac[]
QED

Theorem internal_return_memory_exit[local]:
  same_frame ce cenv /\
  intret_mem_q H func cenv cx tv bw v (ee with scopes := []) r ==>
  !tail. intret_mem_q H func ce cx tv bw v
    ((ee with gas_obs := tail) with scopes := []) r
Proof
  simp[intret_mem_q_def, intret_q_def] >> rpt strip_tac >>
  gvs[result_rel_def] >>
  `ce.ce_nonreentrant = cenv.ce_nonreentrant /\
   ce.ce_returns_count = cenv.ce_returns_count` by
    fs[same_frame_def, compile_env_component_equality] >>
  `return_unlock_state ce s = return_unlock_state cenv s` by
    simp[return_unlock_state_def] >>
  qexists_tac `s` >> simp[] >>
  qmatch_goalsub_abbrev_tac `state_rel H func ce cx es1 s` >>
  `es1 = (ee with scopes := []) with gas_obs := tail` by
    simp[Abbr `es1`, evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> simp[state_rel_gas_obs] >>
  drule_all constructor_exit_state_rel >> simp[]
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
  ~ctx_has_dalloca ctx /\ ~t.vs_call_ctx.cc_static /\
  allocas_from lo t /\ lo <= t.vs_alloca_next /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?r G' tn'. exit_result r /\
    (?fuel. run_from fuel ctx func t = r) /\
    !D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (t, G, tn) []
          (r, G', tn')
Proof
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `sm`, `s` |-> `t`] return_unlock_origin_ptr) >>
  impl_tac >- fs[] >> strip_tac >>
  rename1 `tn1.t_var = tn.t_var` >>
  qpat_x_assum `G' = G` SUBST_ALL_TAC >>
  drule compile_return_unlock_shape >> strip_tac >>
  qabbrev_tac `u = return_unlock_state cenv t` >>
  `u.vs_vars = t.vs_vars /\ u.vs_memory = t.vs_memory /\
   u.vs_alloca_next = t.vs_alloca_next /\ u.vs_allocas = t.vs_allocas /\
   ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
   u.vs_inst_idx = LENGTH su.cs_current_insts` by
    (fs[Abbr `u`, return_unlock_alloca_frames] >>
     qspecl_then [`cenv`, `t`, `sm.cs_next_id`] mp_tac
       return_unlock_state_frames >> fs[]) >>
  `!x. lookup_var x u = lookup_var x t` by fs[lookup_var_def] >>
  `!x k. ptr_covers G tn1 x u k <=> ptr_covers G tn x t k` by
    fs[ptr_covers_def, op_taint_def] >>
  `!m. mem_agree_outside tn1.t_mem u.vs_memory m <=>
       mem_agree_outside tn.t_mem t.vs_memory m` by fs[] >>
  `not_fresh_at su src /\ not_fresh_at su bp /\ not_fresh_at su rpc` by
    fs[not_fresh_at_def] >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[allocas_from_def] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  `mload (w2n a) u = mload (w2n a) t` by fs[mload_def] >>
  (* the window the copy reads and writes *)
  `?len k. k < dimword (:256) /\ k <= type_memory_size tv /\
     (if is_bytestring_type ty then
        k = 32 + 32 * ((len + 31) DIV 32) /\ mload (w2n a) u = n2w len /\
        (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn1.t_mem)
      else k = type_memory_bytes cenv ty) /\ val_footprint tv v <= k` by
    (Cases_on `is_bytestring_type ty`
     >- (qspecl_then [`get_tenv cx`, `ty`, `ty`, `tv`, `tv`, `v`, `w2n a`,
                      `t`, `tn`] mp_tac annassign_bytestring_window_ptr >>
         impl_tac >- fs[] >> strip_tac >>
         qexistsl_tac [`len`, `32 + 32 * ((len + 31) DIV 32)`] >>
         fs[]) >>
     qexistsl_tac [`0`, `type_memory_size tv`] >> fs[]) >>
  `!x. ptr_covers G tn x t (type_memory_size tv) ==> ptr_covers G tn x t k` by
    (rw[ptr_covers_def] >> qexistsl_tac [`w`, `b`, `sz'`] >> simp[] >>
     decide_tac) >>
  `ptr_covers G tn1 src u k /\ ptr_covers G tn1 bp u k` by fs[] >>
  qabbrev_tac `D0 = <| d_stor := K (K {}); d_trans := K (K {});
                       d_imm := K {}; d_ret := K {} |>` >>
  qspecl_then [`D0`, `ctx`, `func`, `PG`, `G`, `tn1`, `u`, `su`, `sc`, `cenv`,
               `ty`, `ty`, `src`, `bp`, `a`, `bw`, `len`, `k`, `tv`, `v`]
    mp_tac annassign_store_memory_path_ptr >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  `lookup_var rpc sf = SOME pc /\ op_taint tnf (Var rpc) = {}` by
    (qpat_assum `!p. not_fresh_at su p ==> _` (qspec_then `rpc` mp_tac) >>
     fs[op_taint_def]) >>
  `gas_path_ptr D0 0 ctx func PG Gf tnf sf 0 Gf tnf
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf)` by
    (irule internal_return_buffer_ret_ptr >> metis_tac[]) >>
  `gas_path_ptr D0 0 ctx func PG G tn1 u 0 Gf tnf
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf)` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_0] >>
  (* the memory checks of the same steps *)
  `expr_val_rel cx ty v (Var src) u /\ expr_store_bound cx ty v (Var src) u /\
   eval_operand (Var bp) u = SOME bw` by
    (fs[expr_val_rel_def, expr_store_bound_def, eval_operand_def] >>
     metis_tac[]) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `src` |-> `Var src`, `dst` |-> `Var bp`,
                  `sa` |-> `su`, `sb` |-> `sc`, `s` |-> `u`, `d` |-> `bw`]
            internal_return_store_path_mem) >>
  impl_tac >- (fs[] >> rw[] >> fs[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts su sc) u = OK t'` >>
  `t'.vs_current_bb = u.vs_current_bb /\ t'.vs_halted = u.vs_halted` by
    (qpat_x_assum `t' with <|vs_vars := _; vs_memory := _|> = u`
       (mp_tac o AP_TERM ``\z:venom_state. (z.vs_current_bb, z.vs_halted)``) >>
     simp[]) >>
  qabbrev_tac `t2 = t' with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `lookup_var rpc t2 = SOME pc` by
    (fs[Abbr `t2`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  mp_tac (Q.INST [`ops` |-> `[]`, `sa` |-> `sc`, `s` |-> `t2`, `vals` |-> `[]`]
            emit_internal_ret_path_mem) >>
  impl_tac >- fs[Abbr `t2`, eval_operands_def] >> strip_tac >>
  `gas_path_mem ctx func u 0
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t2)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_0] >>
  (* one deterministic run *)
  `?f1. run_from f1 ctx func u =
        IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t2` by
    (qpat_assum `gas_path_mem ctx func u 0 (IntRet _ _)`
       (mp_tac o MATCH_MP gas_path_mem_exec) >>
     simp[exit_result_def] >> metis_tac[]) >>
  `?f2. run_from f2 ctx func u =
        IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf` by
    (qpat_assum `gas_path_ptr D0 0 ctx func PG G tn1 u 0 Gf tnf _`
       (mp_tac o MATCH_MP gas_path_ptr_exec) >>
     simp[exit_result_def] >> metis_tac[]) >>
  `IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t2 =
   IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf` by
    (`(!e. IntRet <|iret_values := []; iret_adopt_fmp := NONE|> t2 <> Error e) /\
      (!e. IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf <> Error e)` by
       simp[] >>
     `f1 <= f2 \/ f2 <= f1` by decide_tac >>
     metis_tac[gas_run_from_fuel_mono]) >>
  `t2 = sf` by fs[] >>
  qpat_x_assum `t2 = sf` SUBST_ALL_TAC >>
  `!D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (u, G, tn1) []
         (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf, Gf, tnf)` by
    (gen_tac >> irule gas_zero_paths_joint >> simp[exit_result_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule gas_path_ptr_zero_to_lo >> qexists_tac `D0` >>
     fs[Abbr `D0`]) >>
  `!D. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (t, G, tn) []
         (IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf, Gf, tnf)` by
    (gen_tac >>
     mp_tac (Q.SPECL [`(D, lo, explicit, ctx, func, PG)`, `(t, G, tn)`, `[]`,
                      `(OK u, G, tn1)`] gas_origin_ptr_path_append) >>
     impl_tac >- fs[] >>
     disch_then (qspecl_then [`u`, `G`, `tn1`, `[]`,
       `IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf`, `Gf`, `tnf`]
       mp_tac) >>
     fs[]) >>
  qexistsl_tac [`IntRet <|iret_values := []; iret_adopt_fmp := NONE|> sf`,
                `Gf`, `tnf`] >>
  simp[exit_result_def] >>
  qpat_assum `!D. gas_origin_ptr_path _ (t, _, _) _ _`
    (qspec_then `D0` assume_tac) >>
  drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> metis_tac[]
QED

Theorem internal_return_memory_full:
  !DF lo ctx shadow_ctx PG func shadow_func tops cx ce cenv env es
   ty tv e lctx bw rpc rsz.
  body_inv tops ctx cenv cx /\ cenv.ce_module = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  same_frame ce cenv /\ expr_sim_inv cenv cx env es /\
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
  `?bp cap. cenv.ce_return_buf = SOME (PtrVar (Var bp) cap) /\
    lookup_var bp s0 = SOME bw /\ not_fresh_at sa bp /\
    w2n bw + type_memory_size tv <= s0.vs_alloca_next` by
    fs[return_buf_frame_def] >>
  `lowered_value_type cenv e = ty /\
   lowered_value_type cenv (gas_shadow_expr e) = ty` by
    fs[internal_return_shadow_type] >>
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
  impl_tac >- simp[] >> strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_outcome_full_bind_all >>
  qexists_tac `\H res mid G1 tn1 t. ?v. res = INL v /\
     expr_post H ctx func cenv cx e es sa sm s0 mid v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     ghost_inv_at (DF H) lo (SOME (bw,type_memory_size tv)) cenv cx mid
       G1 tn1 t /\
     ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
     (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted` >>
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
  >~ [`gas_outcome_full _ _ _ _ (bind (eval_expr _ _) _)`]
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> fs[] >>
      Cases_on `res` >> fs[expr_exit_def, stmt_exit_ptr_def]) >>
  (* the value is on hand: release, copy and RET *)
  rpt strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
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
     ptr_covers G1 tn1 src t (type_memory_bytes cenv (lowered_value_type cenv e)) /\
     (!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
          val_in_memory tv v (w2n a) m)` by
    (mp_tac (Q.INST [`H` |-> `H0`] (Q.SPECL
       [`ctx`, `func`, `cenv`, `cx`, `e`, `es`, `sa`, `sm`, `s0`, `mid`, `v`,
        `op`, `t`, `G1`, `tn1`, `tv`, `ty`, `tv`]
       annassign_memory_rhs_layout_ptr)) >>
     impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >> simp[]) >>
  qpat_x_assum `op = Var src` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 bp t (type_memory_size tv) /\
   op_taint tn1 (Var rpc) = {} /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (fs[ghost_inv_at_def, return_buf_ptr_def] >> gvs[]) >>
  `~t.vs_call_ctx.cc_static /\ expr_val_rel cx ty v (Var src) t` by
    fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  `w2n bw + type_memory_size tv <= t.vs_alloca_next` by decide_tac >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                  `G` |-> `G1`, `tn` |-> `tn1`]
            return_memory_suffix_origin_ptr) >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  irule (Q.INST [`res` |-> `INR (ReturnException v)`, `ee` |-> `mid`]
           gas_outcome_full_exit) >>
  TRY (conj_tac >- (fs[] >> NO_TAC)) >>
  qexistsl_tac [`G'`, `r`, `tn'`] >>
  qpat_assum `~t.vs_halted` (fn th => simp[th, raise_def]) >>
  rpt strip_tac
  >- (first_x_assum irule >> simp[] >>
      fs[dead_lo_ok_def]) >>
  simp[stmt_exit_ptr_def] >>
  (* the exact contract: the base fragment's run is this run *)
  first_x_assum (drule_then strip_assume_tac) >>
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
  mp_tac (Q.INST [`es` |-> `mid with gas_obs := []`, `sa` |-> `sm`]
    (SPEC_ALL compile_internal_return_memory_frag)) >>
  impl_tac
  >- (simp[] >> fs[] >> metis_tac[]) >>
  simp[frag_exec_def] >>
  disch_then (qspecl_then [`func`, `t`] mp_tac) >>
  impl_tac
  >- (fs[expr_post_def, eval_operand_def] >>
      irule stmt_state_rel_scopes_nil >> simp[]) >>
  strip_tac >>
  `r' = r` by
    (qpat_x_assum `run_from fuel ctx func t = r` mp_tac >>
     qpat_x_assum `run_from fuel' ctx func t = r'` mp_tac >>
     rpt strip_tac >>
     `!e. r <> Error e /\ r' <> Error e` by
       metis_tac[exit_result_not_error] >>
     Cases_on `fuel <= fuel'` >>
     metis_tac[gas_run_from_fuel_mono, arithmeticTheory.NOT_LESS_EQUAL,
               arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  gvs[] >>
  drule_all internal_return_memory_exit >>
  disch_then (qspec_then `tail` mp_tac) >>
  simp[]
QED
