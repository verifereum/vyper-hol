(* Initialize and activate a declared memory local at the RHS's actual landing. *)
Theory bodyIntCallDeclarationStore
Ancestors
  bodyIntCallDeclarationRegions bodyIntCallProtectedBuffer bodyIntCallLocalLanding
  stmtSimDeclStore valueCopy localMemoryStorePath localPtrsProps intCallFrame
  compileEnv exprLoweringProps exprSimDefs loweringPosts valueEncoding
  venomState venomInst venomExecSemantics finite_map list vyperState

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
