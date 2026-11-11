(* Same-endpoint semantics and resources for an existing local memory store. *)
Theory bodyIntCallLocalLanding
Ancestors
  localMemoryStorePath bodyIntCallProtectedReturn exprSimCopy tupleMemoryFrame
  stmtSimAssignStore exprSimDefs fragGasSeq fragGasMode localPtrsProps
  vyperLookup finite_map pred_set rich_list venomState compileEnv loweringStateRelDefs exprLoweringProps
  fragExec exprLowering emitHelperProps venomInst venomExecSemantics
  valueEncoding vyperState vyperInterpreter loweringPosts valueCopy list instIdxIndep

Theorem local_store_semantic_landing:
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ local_ptrs_reserved cenv sa /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!b n. b + n <= w2n w \/ w2n w + type_memory_size entry.type <= b ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  val_wf entry.type v /\ val_in_memory entry.type v (w2n w) t.vs_memory ==>
  stmt_state_rel ctx func cenv cx
    (es with scopes := pre ++
      (env |+ (id,entry with <|value := v; popped := []|>)) :: rest) t
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `local_region cenv es.scopes s id (w2n w) sz` by simp[local_region_def] >>
  `t.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule local_copy_immutables >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexists_tac `type_memory_size entry.type` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  irule stmt_state_rel_write_local >>
  goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  simp[] >> qexistsl_tac [`s`, `w`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  gvs[venom_state_component_equality]
QED

Theorem protected_local_memory_store_run:
  compile_store_memory cenv src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  expr_val_rel cx ty v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tyv /\ entry.type = tyv /\
  value_has_type tyv v /\ val_wf tyv v /\
  type_memory_bytes cenv ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\
  (!dw b n. lookup_var p s = SOME dw /\ P b n ==>
    regions_disjoint b n (w2n dw) (type_memory_size tyv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id,entry with <|value := v; popped := []|>)) :: rest) t /\
    (!b n. P b n ==> mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op t = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `eval_operand (Var p) s = SOME dw` by simp[eval_operand_def] >>
  `!x. Var p = Var x ==> not_fresh_at sa x` by simp[] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  first_x_assum drule >> strip_tac >>
  drule_all compile_store_memory_run_size_bound_with_capacity >> strip_tac >>
  simp[] >>
  conj_tac
  >- (irule local_store_semantic_landing >>
      goal_assum (drule_at (Pat `find_containing_scope _ _ = _`)) >>
      simp[] >> qexistsl_tac [`s`, `sa`, `dw`] >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
      gvs[venom_state_component_equality]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ _ = _` irule >>
      qpat_x_assum `!dw b n. _ ==> regions_disjoint _ _ _ _` drule_all >>
      simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, venom_state_component_equality]) >>
  gvs[venom_state_component_equality]
QED

Theorem protected_local_memory_store_path:
  compile_store_memory cenv src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  expr_val_rel cx ty v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tyv /\ entry.type = tyv /\
  value_has_type tyv v /\ val_wf tyv v /\
  type_memory_bytes cenv ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dw b n. lookup_var p s = SOME dw /\ P b n ==>
    regions_disjoint b n (w2n dw) (type_memory_size tyv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    (!name b n. local_region cenv
      (pre ++ (env |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      u name b n <=> local_region cenv es.scopes s name b n)
Proof
  strip_tac >> drule_all protected_local_memory_store_run >> strip_tac >>
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
  `MAP FDOM (pre ++ (env |+ (id,entry with <|value := v; popped := []|>)) :: rest) =
    MAP FDOM es.scopes` by
    (drule find_containing_scope_structure >> strip_tac >>
     simp[MAP_APPEND, FDOM_FUPDATE] >>
     fs[FLOOKUP_DEF, pred_setTheory.ABSORPTION]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >> gvs[same_blocks_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_op_inst_idx] >>
  rpt gen_tac >>
  drule_all local_region_scopes_domain >>
  disch_then (fn th => rewrite_tac[th]) >>
  irule copy_buffer_local_region_frame >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  simp[lookup_var_def] >> rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at _ x ==> _` drule >> simp[lookup_var_def]
QED

(* An arbitrary RHS prefix supplies semantics and resources at the very same s. *)
Theorem protected_local_memory_store_prefix:
  gas_marked_path F ctx func s0 m (OK s) /\
  (!b n. P b n ==> mem_bytes_at b n s.vs_memory = mem_bytes_at b n s0.vs_memory) /\
  (!op. reserved op ==> eval_operand op s = eval_operand op s0) /\
  s.vs_allocas = s0.vs_allocas /\ s.vs_alloca_next = s0.vs_alloca_next /\
  (!name b n. local_region cenv es.scopes s name b n <=>
    local_region cenv scopes0 s0 name b n) /\
  compile_store_memory cenv src (Var p) ty ty sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  expr_val_rel cx ty v src s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tyv /\ entry.type = tyv /\
  value_has_type tyv v /\ val_wf tyv v /\
  type_memory_bytes cenv ty = type_memory_size tyv /\
  type_memory_size tyv + 64 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre,env,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dw b n. lookup_var p s = SOME dw /\ P b n ==>
    regions_disjoint b n (w2n dw) (type_memory_size tyv)) /\
  (!op x. reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_marked_path F ctx func s0 m (OK u) /\
    stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (env |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!b n. P b n ==> mem_bytes_at b n u.vs_memory = mem_bytes_at b n s0.vs_memory) /\
    (!op. reserved op ==> eval_operand op u = eval_operand op s0) /\
    u.vs_allocas = s0.vs_allocas /\ u.vs_alloca_next = s0.vs_alloca_next /\
    (!name b n. local_region cenv
      (pre ++ (env |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      u name b n <=> local_region cenv scopes0 s0 name b n)
Proof
  strip_tac >> drule_all protected_local_memory_store_path >> strip_tac >>
  `gas_marked_path F ctx func s0 (m + 0) (OK u)` by
    (irule gas_marked_path_then >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `u` >> fs[]
QED
