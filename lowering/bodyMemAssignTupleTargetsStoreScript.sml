(* The tuple store boundary retains the byte frame deliberately hidden by the
   single-assignment boundary.  Only the unread suffix needs this frame. *)
Theory bodyMemAssignTupleTargetsStore
Ancestors
  bodyMemAssignLocalMem bodyDeclMemoryCounted bodyDeclMemoryCore
  bodyDeclCopyMemory valueCopy exprLoweringProps compileEnv loweringStateRelDefs finite_map
  venomState venomExecSemantics loweringSlice stmtSimProps bodyMemoryDefs
  stmtSimDeclMem stmtSimAssignMem exprSimProps exprSimBufferStore
  valueEncoding valueEncodingDefs venomMemDefs tupleMemoryFrame tupleMemoryLayout
  vyperLookup list loweringPosts bodyMemAssignTupleTargetsFacts
  bodyMemAssignLocalWord tupleTargetStoreRun tupleTargetStoreProps
  instMemFrontier emitHelperProps memSafeRun venomInst freshWrites
  valueEncodingProps stmtSimDeclStore stmtSimAssignStore allocaFootprint
  storageStoreFrame stmtSimAssignStorage emitHelper context stmtLowering
  bodyMemEmitOpFrame fragGasMode fragGasPathMem ASCIInumbers stmtLoweringMono fragExec stmtSimAssignAttrStorage
  vyperInterpreter vyperTyping vyperState tupleAssignParts tupleLocalStoreRun


(* The local memory copy, run memory-safely: it keeps the pointer relation
   and, at every horizon, the state relation. *)
Theorem tuple_local_memory_store_path_mem:
  !ctx func cenv cx es s id p sz pre env entry rest v src ty sa sb sw d.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME entry.type /\
    value_has_type entry.type v /\ val_wf entry.type v /\
    val_in_memory entry.type v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size entry.type /\
    type_memory_size entry.type + 64 < dimword (:256) /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + val_store_size entry.type v <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?dw t.
      lookup_var p s = SOME dw /\
      gas_path_mem ctx func s 0 (OK t) /\
      (!H. stmt_state_rel H ctx func cenv cx es s ==>
           stmt_state_rel H ctx func cenv cx
             (es with scopes :=
               pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t) /\
      local_ptrs_rel func cenv
        (pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_call_ctx = s.vs_call_ctx /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size entry.type <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all tuple_local_copy_exec >>
  disch_then (qx_choosel_then [`dw`, `u`] strip_assume_tac) >>
  drule tuple_local_copy_code_shape >> strip_tac >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `w2n dw + type_memory_size entry.type <= s.vs_alloca_next` by
    (qpat_x_assum `local_ptrs_rel _ _ es.scopes s`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac) >>
  `type_memory_size entry.type < dimword (:256)` by decide_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (drule compile_store_memory_run_size_bound_with_capacity >>
     disch_then (qspecl_then [`s`, `get_tenv cx`, `entry.type`, `v`, `sw`, `dw`]
       mp_tac) >>
     impl_tac >- simp[] >> strip_tac >> simp[]) >>
  `!x. src = Var x \/ Var p = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> gvs[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`dw`, `get_tenv cx`, `entry.type`, `v`, `sw`] >>
     simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  `return_buf_frame d cenv sb (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
     fs[return_buf_frame_def, lookup_var_def]) >>
  `!x. not_fresh_at sa x ==>
       lookup_var x (u with vs_inst_idx := LENGTH sb.cs_current_insts) =
       lookup_var x s` by
    (rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s`
       (qspec_then `x` mp_tac) >> simp[lookup_var_def]) >>
  qexistsl_tac [`dw`, `u with vs_inst_idx := LENGTH sb.cs_current_insts`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      first_x_assum (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (REWRITE_TAC[localPtrsPropsTheory.local_ptrs_rel_inst_idx] >>
      first_assum ACCEPT_TAC) >>
  simp[]
QED

(* Consume the store's byte frame at the S1 suffix abstraction boundary.
   Unlike full tuple preservation, this permits writes to a containing local. *)
Theorem tuple_store_unread_suffix_frontier:
  !ctx func ce cx es s t b sz dest dst dsz addr off elem vs tvs written.
    stmt_state_rel H ctx func ce cx es s /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region ce es.scopes s name b sz)) /\
    local_region ce es.scopes s dest dst dsz /\
    b <= addr /\
    addr + off + elem + type_memory_size_list tvs <= b + sz /\
    written <= elem /\ written <= dsz /\
    (!a len. a + len <= dst \/ dst + written <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    tuple_in_memory vs tvs (addr + off + elem) s.vs_memory /\
    tuple_val_wf vs tvs /\ s.vs_alloca_next <= t.vs_alloca_next ==>
    tuple_in_memory vs tvs (addr + off + elem) t.vs_memory /\
    addr + off + elem + type_memory_size_list tvs <= t.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv s /\ local_ptrs_rel func ce es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `b + sz <= s.vs_alloca_next` by
    (irule tuple_container_frontier >> goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all tuple_in_memory_unread_suffix >> strip_tac >> simp[] >> decide_tac
QED


(* Framed word-store boundary: the general local-word assignment interface
   intentionally hides the byte frame needed by a later tuple element. *)
Theorem tuple_local_word_store_path_mem:
  !ctx func cenv cx es s id p sz pre env entry rest v tv op sa sb d.
    emit_void MSTORE [Var p; op] sa = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    alloca_history func s /\
    return_buf_frame d cenv sa s /\
    find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    store_lays_out tv entry.type v ==>
    ?t dw. gas_path_mem ctx func s 0 (OK t) /\
      (!H. stmt_state_rel H ctx func cenv cx es s ==>
           stmt_state_rel H ctx func cenv cx
             (es with scopes := pre ++
               (env |+ (id,entry with <|value := v; popped := []|>))::rest) t) /\
      local_ptrs_rel func cenv
        (pre ++ (env |+ (id,entry with <|value := v; popped := []|>))::rest) t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ return_buf_frame d cenv sb t /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_call_ctx = s.vs_call_ctx /\
      (!x. lookup_var x t = lookup_var x s) /\ lookup_var p s = SOME dw /\
      (!a len. a + len <= w2n dw \/ w2n dw + 32 <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w /\ w2n w + sz <= s.vs_alloca_next /\
       type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ es.scopes s`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  `type_memory_size entry.type = 32` by fs[store_lays_out_def] >>
  `w2n w + 32 <= s.vs_alloca_next` by decide_tac >>
  `!H. stmt_state_rel H ctx func cenv cx es s ==>
       stmt_state_rel H ctx func cenv cx
         (es with scopes := pre ++
           (env |+ (id,entry with <|value := v; popped := []|>))::rest)
         (mstore (w2n w) (typed_val_to_w256 tv v) s)` by
    (rpt strip_tac >> irule stmt_state_rel_write_local_store >>
     simp[] >> metis_tac[]) >>
  `local_ptrs_rel func cenv
     (pre ++ (env |+ (id,entry with <|value := v; popped := []|>))::rest)
     (mstore (w2n w) (typed_val_to_w256 tv v) s)` by
    (irule local_ptrs_rel_write_local_store >> simp[] >> metis_tac[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = mstore (w2n w) (typed_val_to_w256 tv v) s` >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    (`step_inst_base (mk_inst sa.cs_next_id MSTORE [Var p; op] []) s = OK u` by
       (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule emit_mstore_mem_ok >> disch_then irule >>
     qexists_tac `w` >> simp[eval_operand_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `sa` >> simp[is_terminator_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `sa`] >> simp[is_terminator_def]) >>
  `return_buf_frame d cenv sb u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >>
     simp[Abbr `u`, lookup_var_def, mstore_def]) >>
  `!a len. a + len <= w2n w \/ w2n w + 32 <= a ==>
    mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `u`] >>
     irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  `return_buf_frame d cenv sb
    (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (Cases_on `d` >- fs[return_buf_frame_def] >>
     rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
     fs[return_buf_frame_def, lookup_var_def]) >>
  `u.vs_call_ctx = s.vs_call_ctx` by simp[Abbr `u`, mstore_def, LET_THM] >>
  qexistsl_tac [`u with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      first_x_assum (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (REWRITE_TAC[localPtrsPropsTheory.local_ptrs_rel_inst_idx] >>
      first_assum ACCEPT_TAC) >>
  simp[Abbr `u`, lookup_var_def, mstore_def] >> fs[mstore_def]
QED

Theorem tuple_target_local_head_path_mem:
  !ctx func cenv cx es es' s id ty tv v op st sf d.
    compile_tuple_store_all cenv [ty] [BaseTarget (NameTarget id)] [op] st = ((),sf) /\
    assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),es') /\
    tuple_target_aligned cenv cx (BaseTarget (NameTarget id)) ty tv /\
    tuple_target_layout es.scopes (BaseTarget (NameTarget id)) ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword (:256) /\
       w2n w + type_memory_size tv <= s.vs_alloca_next) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    fn_has_code st sf func /\
    fn_inst_ids_distinct func /\ alloca_history func s /\
    return_buf_frame d cenv st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t idp sz entry dw.
      (!H. stmt_state_rel H ctx func cenv cx es s ==>
           stmt_state_rel H ctx func cenv cx es' t) /\
      local_ptrs_rel func cenv es'.scopes t /\
      es'.storage_trace = es.storage_trace /\
      es'.accounts = es.accounts /\ es'.tStorage = es.tStorage /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ return_buf_frame d cenv sf t /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_call_ctx = s.vs_call_ctx /\
      lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var idp) sz) /\
      lookup_var idp s = SOME dw /\
      (!a len. a + len <= w2n dw \/
         w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[tuple_target_aligned_local, tuple_target_layout_local] >>
  drule_all tuple_target_local_assignment >> strip_tac >>
  drule_all tuple_store_local_singleton_code >> strip_tac >>
  Cases_on `is_word_type ty`
  >- (gvs[] >> drule_all tuple_local_word_store_path_mem >> strip_tac >>
      qexistsl_tac [`t`, `p`, `sz`, `entry`, `dw`] >> simp[] >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  gvs[] >>
  `val_store_size entry.type v <= type_memory_size entry.type` by
    metis_tac[val_store_size_le] >>
  `w2n w + val_store_size entry.type v <= s.vs_alloca_next` by decide_tac >>
  `not_fresh_at st p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all tuple_local_memory_store_path_mem >>
  disch_then (qx_choosel_then [`dw`, `t`] strip_assume_tac) >>
  qexistsl_tac [`t`, `p`, `sz`, `entry`, `dw`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem tuple_storage_store_head_path_mem:
  !ctx func cenv s tr slot w op dst st st' d.
    compile_store_at_loc cenv.ce_imm_alloca dst op
      (SOME (if tr then LocTransient else LocStorage)) st = ((), st') /\
    eval_operand dst s = SOME slot /\
    eval_operand op s = SOME w /\
    ~s.vs_call_ctx.cc_static /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\ return_buf_frame d cenv st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. t = ((if tr then tstore slot w s else sstore slot w s)
             with vs_inst_idx := LENGTH st'.cs_current_insts) /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        t.vs_call_ctx = s.vs_call_ctx /\
        gas_path_mem ctx func s 0 (OK t) /\
        alloca_history func t /\ return_buf_frame d cenv st' t
Proof
  rpt gen_tac >> strip_tac >>
  `emit_void (if tr then TSTORE else SSTORE) [dst; op] st = ((),st')` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  qabbrev_tac `u = if tr then tstore slot w s else sstore slot w s` >>
  `run_inst_seq (emitted_insts st st') s = OK u` by
    (`step_inst_base (mk_inst st.cs_next_id (if tr then TSTORE else SSTORE)
        [dst;op] []) s = OK u` by
      (Cases_on `tr` >>
       simp[Abbr `u`, step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def]) >>
     simp[run_inst_seq_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (drule emit_void_mem_ok >> disch_then irule >> Cases_on `tr` >>
     simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[is_terminator_def] >>
     qexists_tac `st` >> simp[is_terminator_def]) >>
  `alloca_history func (u with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[is_terminator_def] >>
     qexistsl_tac [`s`, `st`] >> Cases_on `tr` >> simp[is_terminator_def]) >>
  `return_buf_frame d cenv st' (u with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `st`] >>
     Cases_on `tr` >> simp[Abbr `u`, lookup_var_def, tstore_def, sstore_def]) >>
  qexists_tac `u with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  Cases_on `tr` >> fs[Abbr `u`, tstore_def, sstore_def, lookup_var_def, LET_THM]
QED

Theorem tuple_field_add_frame_path_mem:
  !ctx func cenv s st st' dst slot off d.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst,st') /\
    local_ptrs_reserved cenv st /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\ return_buf_frame d cenv st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t. (!H cx es. stmt_state_rel H ctx func cenv cx es s ==>
                   stmt_state_rel H ctx func cenv cx es t) /\
        eval_operand dst t = SOME (slot + n2w off) /\
        t.vs_labels = s.vs_labels /\ t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
        t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        t.vs_call_ctx = s.vs_call_ctx /\
        gas_path_mem ctx func s 0 (OK t) /\
        alloca_history func t /\ return_buf_frame d cenv st' t
Proof
  rpt strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (drule emit_op_mem_ok >> disch_then irule >>
     simp[below_frontier_no_ranges, mk_inst_def]) >>
  `dst = Var (STRING #"%" (toString st.cs_next_var))` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `emitted_insts st st' =
     [mk_inst st.cs_next_id ADD [Lit slot; Lit (n2w off)]
        [STRING #"%" (toString st.cs_next_var)]]` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `st.cs_next_var <= st'.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `same_blocks st st' /\
   st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    (drule emit_op_extends >> simp[]) >>
  `step_inst_base (mk_inst st.cs_next_id ADD [Lit slot; Lit (n2w off)]
      [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s)` by
    simp[mk_inst_def, step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def] >>
  `run_inst_seq (emitted_insts st st') s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s)` by
    gvs[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_path_mem ctx func s 0
     (OK (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s
          with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   ~(update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s).vs_halted /\
   (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s).vs_current_bb =
     st'.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `st` >> simp[]) >>
  `alloca_history func
     (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s
      with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `st`] >> simp[mk_inst_def, is_terminator_def]) >>
  `!scopes. not_local_ptr cenv scopes (STRING #"%" (toString st.cs_next_var))` by
    (gen_tac >> irule local_ptrs_reserved_fresh >> qexists_tac `st` >> simp[]) >>
  `!rp. not_fresh_at st rp ==>
     lookup_var rp (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s
                    with vs_inst_idx := LENGTH st'.cs_current_insts) =
     lookup_var rp s` by
    (rpt strip_tac >>
     `rp <> STRING #"%" (toString st.cs_next_var)` by
       (qpat_x_assum `not_fresh_at _ _` (mp_tac o REWRITE_RULE [not_fresh_at_def]) >>
        disch_then (qspec_then `st.cs_next_var` mp_tac) >> simp[]) >>
     rw[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> gvs[]) >>
  `return_buf_frame d cenv st'
     (update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s
      with vs_inst_idx := LENGTH st'.cs_current_insts)` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `st`] >>
     simp[update_var_def]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (slot + n2w off) s
                with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >> simp[]) >>
  fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem tuple_field_storage_head_path_mem:
  !ctx func cenv s tr slot off w op dst st sp sf d.
    emit_op ADD [Lit slot; Lit (n2w off)] st = (dst, sp) /\
    compile_store_at_loc cenv.ce_imm_alloca dst op
      (SOME (if tr then LocTransient else LocStorage)) sp = ((), sf) /\
    local_ptrs_reserved cenv st /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at st x) /\
    ~s.vs_call_ctx.cc_static /\
    fn_has_code st sf func /\ fn_inst_ids_distinct func /\
    alloca_inv s /\ alloca_history func s /\ return_buf_frame d cenv st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?mid t.
      (!H cx es. stmt_state_rel H ctx func cenv cx es s ==>
                 stmt_state_rel H ctx func cenv cx es mid) /\
      t = ((if tr then tstore (slot + n2w off) w mid
            else sstore (slot + n2w off) w mid)
           with vs_inst_idx := LENGTH sf.cs_current_insts) /\
      t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_call_ctx = s.vs_call_ctx /\
      gas_path_mem ctx func s 0 (OK t) /\
      alloca_history func t /\ return_buf_frame d cenv sf t
Proof
  rpt strip_tac >>
  `cs_extends st sp /\ cs_extends sp sf` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def] >>
     metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  `fn_has_code st sp func /\ fn_has_code sp sf func` by
    metis_tac[fn_has_code_split] >>
  drule_all tuple_field_add_frame_path_mem >>
  disch_then (qx_choose_then `mid` (map_every assume_tac o CONJUNCTS)) >>
  `eval_operand op mid = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `~mid.vs_call_ctx.cc_static` by gvs[] >>
  `alloca_inv mid` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
     asm_rewrite_tac[]) >>
  drule_all tuple_storage_store_head_path_mem >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`mid`, `t`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `t = _` kall_tac >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (irule (gas_path_mem_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexists_tac `mid` >> conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem tuple_target_nonlocal_head_path_mem:
  !ctx func cenv cx es es' s g ty tv v op st sf d.
    compile_tuple_store_all cenv [ty] [g] [op] st = ((),sf) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\
    (!id. g <> BaseTarget (NameTarget id)) /\ value_has_type tv v /\
    eval_operand op s = SOME (typed_val_to_w256 tv v) /\
    local_ptrs_reserved cenv st /\ (!x. op = Var x ==> not_fresh_at st x) /\
    ~s.vs_call_ctx.cc_static /\ fn_has_code st sf func /\
    fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_history func s /\
    return_buf_frame d cenv st s /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    es'.scopes = es.scopes /\
    ?t. (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
                 stmt_state_rel H ctx func cenv cx es s /\
                 storage_well_formed_on cx es (FST H) ==>
                 stmt_state_rel H ctx func cenv cx es' t /\
                 storage_well_formed_on cx es' (FST H)) /\
        t.vs_memory = s.vs_memory /\
        ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
        t.vs_inst_idx = LENGTH sf.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
        t.vs_call_ctx = s.vs_call_ctx /\
        gas_path_mem ctx func s 0 (OK t) /\
        alloca_history func t /\ return_buf_frame d cenv sf t
Proof
  rpt gen_tac >> simp[tuple_target_aligned_def] >> strip_tac >> gvs[]
  >- suspend "toplevel" >>
  suspend "field"
QED

Resume tuple_target_nonlocal_head_path_mem[toplevel]:
  drule_all tuple_target_toplevel_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tuple_target_storage_assignment >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >>
  disch_then (qspec_then `st` assume_tac) >> gvs[] >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  drule_all encode_value_word_typed >> strip_tac >>
  `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all tuple_storage_store_head_path_mem >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (drule vyperScopePreservationTheory.write_storage_slot_scopes >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- suspend "toplevel_rel" >>
  qpat_x_assum `t = _` kall_tac >> simp[]
QED

Resume tuple_target_nonlocal_head_path_mem[toplevel_rel]:
  rpt gen_tac >> strip_tac >>
  `type_slot_size tv = 1` by
    metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  conj_tac
  >- (qpat_x_assum `t = _` SUBST1_TAC >> simp[stmt_state_rel_inst_idx] >>
      irule tuple_storage_root_word_rel >>
      qpat_assum `write_storage_slot _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `valid_horizon _ _ _ _` (irule_at Any) >>
      simp[] >> rpt strip_tac >>
      metis_tac[accountsRelPropsTheory.storage_dead_update_word_region]) >>
  irule tuple_target_storage_write_wf >>
  qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `write_storage_slot _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `valid_horizon _ _ _ _` (irule_at Any) >>
  simp[]
QED

Resume tuple_target_nonlocal_head_path_mem[field]:
  drule_all tuple_target_field_place >>
  disch_then (qspec_then `es` assume_tac) >>
  drule_all tuple_target_storage_assignment >> strip_tac >>
  Cases_on `emit_op ADD [Lit (n2w k); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))] st` >>
  rename1 `emit_op ADD _ st = (dst,sp)` >>
  drule_all tuple_target_field_pointer >> strip_tac >>
  drule_all tuple_store_word_step >> strip_tac >>
  qpat_x_assum `compile_tuple_store_all _ [_] [_] [_] _ = _` kall_tac >>
  gvs[compile_tuple_store_all_def, comp_return_def] >>
  drule_all encode_value_word_typed >> strip_tac >>
  drule_all tuple_field_storage_head_path_mem >>
  disch_then (qx_choosel_then [`mid`, `t`] (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (drule vyperScopePreservationTheory.write_storage_slot_scopes >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- suspend "field_rel" >>
  qpat_x_assum `t = _` kall_tac >> simp[]
QED

Resume tuple_target_nonlocal_head_path_mem[field_rel]:
  rpt gen_tac >> strip_tac >>
  `type_slot_size tv = 1` by
    metis_tac[exprSimUnwrapTheory.word_type_slot_size] >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `stmt_state_rel H ctx func cenv cx es mid` by
    (qpat_x_assum `!H cx es. stmt_state_rel H _ _ _ cx es s ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `t = _` SUBST1_TAC >> simp[stmt_state_rel_inst_idx] >>
      irule tuple_storage_root_word_rel >>
      qpat_assum `write_storage_slot _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `valid_horizon _ _ _ _` (irule_at Any) >>
      simp[] >> rpt strip_tac >>
      metis_tac[accountsRelPropsTheory.storage_dead_update_struct_word_field]) >>
  irule tuple_target_storage_write_wf >>
  qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `write_storage_slot _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `valid_horizon _ _ _ _` (irule_at Any) >>
  simp[]
QED

Finalise tuple_target_nonlocal_head_path_mem

Theorem tuple_target_store_head_path_mem:
  !ctx func cenv cx es es' s g ty tv v op sa sb d.
    compile_tuple_store_all cenv [ty] [g] [op] sa = ((),sb) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\ tuple_target_layout es.scopes g ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword (:256) /\
       w2n w + type_memory_size tv <= s.vs_alloca_next) /\
    local_ptrs_reserved cenv sa /\ (!x. op = Var x ==> not_fresh_at sa x) /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    ~s.vs_call_ctx.cc_static /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
                 stmt_state_rel H ctx func cenv cx es s /\
                 storage_well_formed_on cx es (FST H) ==>
                 stmt_state_rel H ctx func cenv cx es' t /\
                 storage_well_formed_on cx es' (FST H)) /\
      local_ptrs_rel func cenv es'.scopes t /\ alloca_inv t /\
      ~t.vs_call_ctx.cc_static /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ return_buf_frame d cenv sb t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
           OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)) /\
      (t.vs_memory = s.vs_memory \/ ?id p sz entry dw.
        g = BaseTarget (NameTarget id) /\ lookup_scopes id es.scopes = SOME entry /\
        FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME dw /\
        (!a len. a + len <= w2n dw \/
          w2n dw + (if is_word_type ty then 32 else type_memory_size tv) <= a ==>
          mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)) /\
      gas_path_mem ctx func s 0 (OK t)
Proof
  rpt strip_tac >> drule_all tuple_target_assignment_scope_frame >> strip_tac >>
  Cases_on `?id. g = BaseTarget (NameTarget id)`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      drule_all tuple_target_local_head_path_mem >>
      disch_then (qx_choosel_then [`t`, `idp`, `sz`, `entry`, `dw`]
        (map_every assume_tac o CONJUNCTS)) >>
      qexists_tac `t` >> conj_tac >- suspend "local_rel" >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac
      >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
          asm_rewrite_tac[]) >>
      rpt conj_tac
      >~ [`t.vs_memory = s.vs_memory`]
      >- (disj2_tac >> qexistsl_tac [`id`, `idp`, `sz`, `entry`, `dw`] >>
          asm_rewrite_tac[]) >>
      gvs[]) >>
  `is_word_type ty` by metis_tac[tuple_target_aligned_nonlocal_word] >>
  gvs[] >> drule_all tuple_target_nonlocal_head_path_mem >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))) >>
  `local_ptrs_rel func cenv es'.scopes t` by
    (qpat_assum `es'.scopes = es.scopes` SUBST1_TAC >>
     irule localPtrsPropsTheory.local_ptrs_rel_frame >> qexists_tac `s` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (rpt strip_tac >> qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
         fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     gvs[]) >>
  `alloca_inv t` by
    (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
     asm_rewrite_tac[]) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt conj_tac >> gvs[]
QED

Resume tuple_target_store_head_path_mem[local_rel]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `!H. stmt_state_rel H _ _ _ _ _ s ==> _` irule >>
      first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx es' (FST H) <=> storage_well_formed_on cx es (FST H)` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >>
     asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED

Finalise tuple_target_store_head_path_mem

(* Single store transports only the unread suffix, not the consumed bytes. *)
Theorem tuple_target_store_tail_path_mem:
  !ctx func cenv cx es es' s g ty tv tvs v vs op sa sb d b sz addr.
    compile_tuple_store_all cenv [ty] [g] [op] sa = ((),sb) /\
    assign_tuple_targets cx g v es = (INL (),es') /\
    tuple_target_aligned cenv cx g ty tv /\ tuple_target_layout es.scopes g ty tv v /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
     else ?w. eval_operand op s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory /\
       type_memory_size tv + 64 < dimword (:256) /\
       w2n w + type_memory_size tv <= s.vs_alloca_next) /\
    local_ptrs_reserved cenv sa /\ (!x. op = Var x ==> not_fresh_at sa x) /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    ~s.vs_call_ctx.cc_static /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es.scopes s name b sz)) /\
    b <= addr /\ addr + type_memory_size_list (tv::tvs) <= b + sz /\
    b + sz <= s.vs_alloca_next /\
    (is_word_type ty ==> type_memory_size tv = 32) /\
    tuple_in_memory (v::vs) (tv::tvs) addr s.vs_memory /\
    tuple_val_wf (v::vs) (tv::tvs) ==>
    ?t. (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
                 stmt_state_rel H ctx func cenv cx es s /\
                 storage_well_formed_on cx es (FST H) ==>
                 stmt_state_rel H ctx func cenv cx es' t /\
                 storage_well_formed_on cx es' (FST H)) /\
      local_ptrs_rel func cenv es'.scopes t /\ alloca_inv t /\
      ~t.vs_call_ctx.cc_static /\
      gas_path_mem ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ return_buf_frame d cenv sb t /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
      MAP FDOM es.scopes = MAP FDOM es'.scopes /\
      (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
           OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)) /\
      b <= addr + type_memory_size tv /\
      addr + type_memory_size tv + type_memory_size_list tvs <= b + sz /\
      b + sz <= t.vs_alloca_next /\
      ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
       (?name. local_region cenv es'.scopes t name b sz)) /\
      tuple_in_memory vs tvs (addr + type_memory_size tv) t.vs_memory /\
      tuple_val_wf vs tvs
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all tuple_target_store_head_path_mem >>
  disch_then (qx_choose_then `t` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  drule_all tuple_target_store_memory_tail >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `b + sz <= t.vs_alloca_next` by decide_tac >>
  qexists_tac `t` >> simp[]
QED

(* Counted twin of S1 tuple_store_targets_path.  The memory branch carries
   just the current unread suffix and its bounded backing container. *)
Theorem tuple_store_targets_path_mem:
  !gs m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' d.
    compile_tuple_store_all cenv tys gs ops st = ((),st') /\
    assign_tuple_target_list cx gs vs es = (INL (),es') /\
    LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
    LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
    (~m ==> EVERY is_word_type tys) /\
    EVERY (\op. ?x. op = Var x) ops /\
    EVERY (\op. !x. op = Var x ==> not_fresh_at st x) ops /\
    local_ptrs_reserved cenv st /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
    (!i. i < LENGTH gs ==>
       ?w. eval_operand (EL i ops) s = SOME w /\
         (if is_word_type (EL i tys) then
            w = typed_val_to_w256 (EL i tvs) (EL i vs)
          else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs)))) /\
    (!i. i < LENGTH gs ==>
       tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
       tuple_target_layout es.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
       type_memory_size (EL i tvs) + 64 < dimword(:256)) /\
    (m ==> (!i. i < LENGTH tys ==>
          evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
          (is_word_type (EL i tys) ==> type_memory_size (EL i tvs) = 32)) /\
       b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
       b + sz <= s.vs_alloca_next /\
       ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
        (?name. local_region cenv es.scopes s name b sz)) /\
       tuple_in_memory vs tvs addr s.vs_memory) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_history func s /\ return_buf_frame d cenv st s /\ ~s.vs_halted /\
    s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    local_ptrs_rel func cenv es.scopes s /\ alloca_inv s /\
    ~s.vs_call_ctx.cc_static /\ ~cx.txn.is_static ==>
    (gs <> [] \/ ~block_is_terminated st ==> ~block_is_terminated st') /\
    ?t. (!st0 H. valid_horizon cx st0 H es'.storage_trace /\
                 stmt_state_rel H ctx func cenv cx es s /\
                 storage_well_formed_on cx es (FST H) ==>
                 stmt_state_rel H ctx func cenv cx es' t /\
                 storage_well_formed_on cx es' (FST H)) /\ ~t.vs_halted /\
        t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
        (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
        (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
        alloca_history func t /\ return_buf_frame d cenv st' t /\
        s.vs_alloca_next <= t.vs_alloca_next /\ gas_path_mem ctx func s 0 (OK t)
Proof
  Induct
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      gvs[compile_tuple_store_all_def, comp_return_def, Once evaluate_def,
          return_def] >> qexists_tac `s` >> simp[] >>
      irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `tys` >- fs[] >> Cases_on `tvs` >- fs[] >>
  Cases_on `vs` >- fs[] >> Cases_on `ops` >- fs[] >>
  rename1 `compile_tuple_store_all cenv (ty::tys1) _ (op::ops1) st = _` >>
  rename1 `assign_tuple_target_list cx _ (v::vs1) es = _` >>
  rename1 `tuple_val_wf (v::vs1) (tv::tvs1)` >>
  qpat_x_assum `!m tys tvs vs ops addr b sz ctx func cenv cx es es' s st st' d. _`
    (mk_asm "ih") >>
  qpat_assum `!i. i < LENGTH (h::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `value_has_type tv v /\ val_wf tv v` by
    (qpat_x_assum `ih :- _` kall_tac >>
     fs[value_has_type_def, val_wf_def]) >>
  drule_all tuple_target_list_cons_success >> strip_tac >>
  drule_all tuple_target_aligned_compiler >> strip_tac >>
  drule tuple_compiler_target_base >>
  disch_then (qx_choose_then `bt` SUBST_ALL_TAC) >>
  drule tuple_store_base_cons >> strip_tac >>
  suspend "head_setup"
QED

Resume tuple_store_targets_path_mem[head_setup]:
  qpat_assum `compile_tuple_store_all _ [_] [_] [_] _ = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  qpat_assum `compile_tuple_store_all _ tys1 gs ops1 sm = _`
    (mp_then Any strip_assume_tac tuple_target_stores_growth) >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    metis_tac[fn_has_code_split] >>
  `if is_word_type ty then eval_operand op s = SOME (typed_val_to_w256 tv v)
   else ?w. eval_operand op s = SOME w /\
     val_in_memory tv v (w2n w) s.vs_memory /\
     type_memory_size tv + 64 < dimword(:256) /\
     w2n w + type_memory_size tv <= s.vs_alloca_next` by
    suspend "head_operand" >>
  `!x. op = Var x ==> not_fresh_at st x` by fs[] >>
  drule_all tuple_target_store_head_path_mem >>
  disch_then (qx_choose_then `s1` (map_every assume_tac o CONJUNCTS)) >>
  suspend "tail"
QED

Resume tuple_store_targets_path_mem[head_operand]:
  qpat_x_assum `ih :- _` kall_tac >>
  qpat_assum `!i. i < LENGTH (_::gs) ==> ?w. _`
    (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  Cases_on `is_word_type ty` >- fs[] >>
  `m` by fs[] >>
  `type_memory_size tv + 64 < dimword(:256)` by
    (qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
      (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `m ==> _` mp_tac >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_size_list (tv::tvs1) =
   type_memory_size tv + type_memory_size_list tvs1` by
    simp[type_memory_size_def] >>
  `w2n w + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  gns[val_in_memory_def, type_memory_size_def] >>
  qexists_tac `w` >> simp[]
QED

Resume tuple_store_targets_path_mem[tail]:
  asm_x "ih" drule >> disch_then drule >>
  disch_then (qspecl_then [`m`, `tvs1`, `addr + type_memory_size tv`, `b`,
    `sz`, `ctx`, `func`, `s1`] mp_tac) >>
  disch_then (qspec_then `d` mp_tac) >>
  (impl_tac >- suspend "tail_premises") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "compose"
QED

Resume tuple_store_targets_path_mem[tail_premises]:
  rpt conj_tac
  >- fs[] >- fs[] >- fs[] >- fs[] >- fs[] >- fs[]
  >- suspend "tail_fresh"
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[])
  >- fs[value_has_type_def]
  >- fs[val_wf_def]
  >- suspend "tail_operands"
  >- suspend "tail_layout"
  >- suspend "tail_sizes"
  >- suspend "tail_memory"
  >> asm_rewrite_tac []
QED

Resume tuple_store_targets_path_mem[tail_fresh]:
  fs[EVERY_MEM] >> rpt strip_tac >>
  irule not_fresh_at_mono >> qexists_tac `st` >> simp[] >> metis_tac[]
QED

Resume tuple_store_targets_path_mem[tail_operands]:
  gen_tac >> strip_tac >>
  `LENGTH ops1 = LENGTH gs` by fs[] >>
  drule (Q.SPEC `T` tuple_store_operands_tail) >>
  disch_then (qspecl_then [`st`, `s`, `s1`] mp_tac) >>
  disch_then irule >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  qexistsl_tac [`BaseTarget bt`, `op`, `ty`, `v`] >> asm_rewrite_tac []
QED

Resume tuple_store_targets_path_mem[tail_layout]:
  drule tuple_target_layout_transport >> disch_tac >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (BaseTarget bt::gs) ==> tuple_target_aligned _ _ _ _ _ /\ _`
    (qspec_then `SUC i` mp_tac) >> simp[] >>
  `i < LENGTH vs1` by fs[] >> simp[]
QED

Resume tuple_store_targets_path_mem[tail_sizes]:
  rpt strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) /\ _ ==> _`
    (qspec_then `SUC i` mp_tac) >> simp[]
QED

Resume tuple_store_targets_path_mem[tail_memory]:
  strip_tac >>
  qpat_x_assum `m ==> _` mp_tac >>
  (impl_tac >- asm_rewrite_tac []) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_word_type ty ==> type_memory_size tv = 32` by
    (qpat_assum `!i. _ ==> evaluate_type _ _ = _ /\ _`
      (qspec_then `0` mp_tac) >> simp_tac (srw_ss()) [] >>
     strip_tac >> asm_rewrite_tac []) >>
  drule_all tuple_target_store_memory_tail >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b + sz <= s1.vs_alloca_next` by decide_tac >>
  asm_rewrite_tac [] >>
  gen_tac >> strip_tac >>
  `i < LENGTH vs1` by fs[] >>
  qpat_x_assum `!i. i < LENGTH (ty::tys1) ==> _`
    (qspec_then `SUC i` mp_tac) >> simp[]
QED

Resume tuple_store_targets_path_mem[compose]:
  `~block_is_terminated sm` by
    (drule_all tuple_store_singleton_open >> simp[]) >>
  conj_tac >- simp[] >>
  qpat_x_assum `?t. (!st0 H. _) /\ _`
    (qx_choose_then `sf` (map_every assume_tac o CONJUNCTS)) >>
  qexists_tac `sf` >> conj_tac >- suspend "compose_rel" >>
  `s.vs_alloca_next <= sf.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at st x ==> lookup_var x sf = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
     metis_tac[]) >>
  `!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
            FLOOKUP sf.vs_allocas aid = SOME bs` by metis_tac[] >>
  `gas_path_mem ctx func s 0 (OK sf)` by
    (irule (gas_path_mem_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     first_assum (irule_at Any) >> simp[]) >>
  simp[]
QED

Resume tuple_store_targets_path_mem[compose_rel]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es1.storage_trace` by
    (irule vyperStorageFootprintTheory.valid_horizon_frame >>
     qpat_assum `assign_tuple_target_list _ gs vs1 es1 = _` (irule_at Any) >>
     fs[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es1 s1 /\
   storage_well_formed_on cx es1 (FST H)` by
    (qpat_x_assum `!st0 H. valid_horizon _ _ H es1.storage_trace /\ _ ==> _` irule >>
     qexists_tac `st0` >> asm_rewrite_tac[]) >>
  qpat_x_assum `!st0 H. valid_horizon _ _ H es'.storage_trace /\ _ ==> _` irule >>
  qexists_tac `st0` >> asm_rewrite_tac[]
QED

Finalise tuple_store_targets_path_mem
