(* The tuple store boundary retains the byte frame deliberately hidden by the
   single-assignment boundary.  Only the unread suffix needs this frame. *)
Theory bodyMemAssignTupleTargetsStore
Ancestors
  bodyMemAssignLocalMem bodyDeclMemoryCounted bodyDeclMemoryCore
  bodyDeclCopyMemory valueCopy exprLoweringProps compileEnv finite_map
  venomState venomExecSemantics loweringSlice stmtSimProps bodyMemoryDefs
  stmtSimDeclMem stmtSimAssignMem exprSimProps exprSimBufferStore
  valueEncoding venomMemDefs tupleMemoryFrame tupleMemoryLayout
  vyperLookup list loweringPosts bodyMemAssignTupleTargetsFacts

Theorem tuple_local_memory_store_path_mem:
  !ctx func cenv cx es s id p sz pre env entry rest v tyv src ty sa sb sw d.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    entry.type = tyv /\ value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + val_store_size tyv v <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t dw. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      lookup_var p s = SOME dw /\
      (!a len. a + len <= w2n dw \/ w2n dw + type_memory_size tyv <= a ==>
         mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?w. lookup_var p s = SOME w /\ w2n w + sz <= s.vs_alloca_next /\
       type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `tyv`, `v`, `sw`, `w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
     (es with scopes :=
       pre ++ (env |+ (id, entry with <|value := v; popped := []|>)) :: rest) t` by
    (irule local_memory_write_frame >> simp[] >>
     qexistsl_tac [`s`, `sa`, `w`] >> simp[] >>
     conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`w`, `get_tenv cx`, `tyv`, `v`, `sw`] >> simp[] >>
     conj_tac >- metis_tac[] >> gvs[] >> decide_tac) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[compile_store_memory_same_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx] >> conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* Consume the store's byte frame at the S1 suffix abstraction boundary.
   Unlike full tuple preservation, this permits writes to a containing local. *)
Theorem tuple_store_unread_suffix_frontier:
  !ctx func ce cx es s t b sz dest dst dsz addr off elem vs tvs written.
    stmt_state_rel ctx func ce cx es s /\
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
