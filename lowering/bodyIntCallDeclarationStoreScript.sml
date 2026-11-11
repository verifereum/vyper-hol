(* Initialize and activate a declared memory local at the RHS's actual landing. *)
Theory bodyIntCallDeclarationStore
Ancestors
  bodyIntCallDeclarationRegions bodyIntCallProtectedBuffer bodyIntCallLocalLanding
  stmtSimDeclStore valueCopy localMemoryStorePath localPtrsProps intCallFrame
  compileEnv exprLoweringProps exprSimDefs loweringPosts valueEncoding
  venomState venomInst venomExecSemantics finite_map list vyperState
  entrySinkExtraction exprSimCopy tupleMemoryFrame fragGasPath fragGasMode fragExec fragGasSeq instIdxIndep rich_list

Theorem declared_local_activate:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  type_memory_size tv <= sz /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory ==>
  stmt_state_rel ctx func ce cx
    (es with scopes := (sc |+ (id,
      <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) s
Proof
  strip_tac >> irule stmt_state_rel_declare_memory >>
  simp[] >> conj_tac >- fs[stmt_state_rel_def, state_rel_def] >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  qexistsl_tac [`s`, `w`] >> gvs[]
QED

Theorem protected_declared_local_store_run:
  compile_store_memory ce src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  expr_val_rel cx ty v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv <= sz /\ type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\ (!b n. P b n ==> b + n <= lo) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func ce cx
      (es with scopes := (sc |+ (id,
        <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) t /\
    (!b n. P b n ==> mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op t = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule allocated_region_state_frame >>
     qexistsl_tac [`w2n w`, `inst`, `s`, `sa`, `sz`] >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
         goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
         qexistsl_tac [`ce`, `name`, `p`, `es.scopes`, `s`] >>
         fs[stmt_state_rel_def, state_rel_def]) >>
     rpt strip_tac >> first_x_assum irule >> fs[regions_disjoint_def] >> decide_tac) >>
  `lo <= w2n w` by (fs[allocas_above_def] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule declared_local_activate >> simp[] >>
      goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
      gvs[venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      `b + n <= lo` by simp[] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, venom_state_component_equality]) >>
  gvs[venom_state_component_equality]
QED

Theorem protected_declared_local_store_path:
  compile_store_memory ce src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
  expr_val_rel cx ty v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv <= sz /\ type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce es.scopes p /\ lookup_var p s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\ (!b n. P b n ==> b + n <= lo) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!name b n. local_region ce es.scopes s name b n ==> authorized name b n) /\
  (!b. lo <= b ==> authorized id b sz) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx
      (es with scopes := (sc |+ (id,
        <|assignable := a; type := tv; value := v; popped := []|>)) :: rest) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\
    (!name b n. local_region ce
      ((sc |+ (id,<|assignable := a; type := tv; value := v; popped := []|>)) :: rest)
      u name b n ==> authorized name b n)
Proof
  strip_tac >> drule_all protected_declared_local_store_run >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (drule compile_store_memory_no_gas >> simp[]) >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `gas_path ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_all tuple_run_inst_seq_gas_path >> simp[]) >>
  drule gas_path_normal >> strip_tac >>
  `!name b n. local_region ce (sc :: rest) t name b n ==>
     authorized name b n` by
    (rpt strip_tac >> first_x_assum irule >>
     drule_all copy_buffer_local_region_frame >>
     disch_then (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `!name b n. local_region ce
     ((sc |+ (id,<|assignable := a; type := tv; value := v; popped := []|>)) :: rest)
     t name b n ==> authorized name b n` by
    (rpt gen_tac >> strip_tac >>
     drule local_region_scope_declare_cases >> strip_tac
     >- (gvs[local_region_def] >>
         qpat_x_assum `!b. lo <= b ==> authorized id b _` irule >>
         fs[allocas_above_def] >> metis_tac[]) >>
     first_x_assum irule >> goal_assum (drule_at Any)) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
       same_blocks_def, allocas_above_def, local_region_def, lookup_var_def] >>
  gvs[same_blocks_def, allocas_above_def, local_region_def, lookup_var_def] >>
  metis_tac[]
QED

(* RHS allocations may extend the map; the store suffix need not freeze the RHS. *)
Theorem protected_path_resources_compose:
  gas_marked_path F ctx func s0 m (OK s) /\
  gas_marked_path F ctx func s n (OK u) /\
  (!b len. P b len ==> mem_bytes_at b len s.vs_memory = mem_bytes_at b len memory_origin.vs_memory) /\
  (!b len. P b len ==> mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!op. reserved op ==> eval_operand op s = eval_operand op operand_origin) /\
  (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
  (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
               FLOOKUP s.vs_allocas aid = SOME entry) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP u.vs_allocas aid = SOME entry) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next ==>
  gas_marked_path F ctx func s0 (m+n) (OK u) /\
  (!b len. P b len ==> mem_bytes_at b len u.vs_memory = mem_bytes_at b len memory_origin.vs_memory) /\
  (!op. reserved op ==> eval_operand op u = eval_operand op operand_origin) /\
  (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
               FLOOKUP u.vs_allocas aid = SOME entry) /\
  s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> conj_tac
  >- (irule gas_marked_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  rpt conj_tac >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
