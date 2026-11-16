(* Declaration allocation is the canonical buffer allocation at its fresh-name entry. *)
Theory bodyFullAnnAssignReserve
Ancestors
  bodyFullMemoryFrames stmtSimDecl bodyPtrDefs exprLoweringProps
  stmtLowering compileEnv emitHelper emitHelperProps
  venomInst venomState finite_map stmtSimProps context

Theorem ghost_inv_at_declare_local_entry:
  declare_local cenv id ty st = (c,st1) /\ cenv.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ghost_inv_at D lo d c cx es G tn s
Proof
  strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  `c.ce_return_buf = cenv.ce_return_buf /\
   c.ce_return_pc = cenv.ce_return_pc /\
   c.ce_imm_alloca = cenv.ce_imm_alloca` by
    (qpat_x_assum `c with <| ce_vars := _; ce_var_type := _;
                           ce_dynarray_capacity := _ |> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  fs[ghost_inv_at_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `name = id` >> gvs[] >>
      qpat_x_assum `!name entry p sz. _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >> simp[]) >>
  simp[] >> Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def]
QED

Theorem declare_local_alloc_buffer:
  declare_local cenv id typ sa = (c,st) /\ cenv.ce_alloca_locals /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ)) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] st = ((),sA) ==>
  compile_alloc_buffer (type_memory_bytes cenv typ) sa =
    (<|buf_operand := Var p; buf_size := type_memory_bytes cenv typ|>,sA)
Proof
  strip_tac >> drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  gvs[compile_alloc_buffer_def, emit_op_def, fresh_var_def,
      comp_bind_def, comp_return_def, comp_ignore_bind_def,
      emit_inst_def, fresh_id_def]
QED

Theorem body_full_declared_alloc_path:
  declare_local cenv id typ sa = (c,st) /\ cenv.ce_alloca_locals /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes cenv typ)) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] st = ((),sA) /\
  lookup_scopes id es.scopes = NONE /\ FLOOKUP cenv.ce_vars id = NONE /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_has_code sa sA func /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  type_memory_bytes cenv typ < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u b G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,G1,tn1)) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
      stmt_state_rel H' ctx func c cx es u) /\
    (!D d. ghost_inv_at D lo d cenv cx es G tn s ==>
      ghost_inv_at D lo d c cx es G1 tn1 u) /\
    ~u.vs_halted /\ u.vs_current_bb = sA.cs_current_bb /\
    u.vs_inst_idx = LENGTH sA.cs_current_insts /\
    local_ptrs_reserved c sA /\ st.cs_next_id = sa.cs_next_id /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,type_memory_bytes cenv typ) /\
    lo <= b /\ b + type_memory_bytes cenv typ < dimword (:256) /\
    lookup_var p u = SOME (n2w b) /\
    ptr_covers G1 tn1 p u (type_memory_bytes cenv typ) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint b (type_memory_bytes cenv typ) a len) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint b (type_memory_bytes cenv typ) a len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at sa x /\ ptr_covers G tn x s cap ==>
      ptr_covers G1 tn1 x u cap) /\
    not_fresh_at sA p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sA x) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
    u.vs_accounts = s.vs_accounts /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    (!i. ~(b <= i /\ i < b + type_memory_bytes cenv typ) ==>
      (i IN tn1.t_mem <=> i IN tn.t_mem)) /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm
Proof
  strip_tac >> drule_all declare_local_alloc_buffer >> strip_tac >>
  drule_all body_full_alloc_buffer_path >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`] strip_assume_tac) >>
  gvs[] >>
  qexistsl_tac [`u`,`b`,`G1`,`tn1`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule stmt_state_rel_declare_local_entry >>
      qpat_assum `declare_local _ _ _ _ = _` (irule_at Any) >>
      simp[] >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule ghost_inv_at_declare_local_entry >> metis_tac[]) >>
  `local_ptrs_reserved c st` by metis_tac[declare_local_reserved] >>
  `st.cs_next_var <= sA.cs_next_var` by
    (drule emit_inst_extends >> simp[]) >>
  `local_ptrs_reserved c sA` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

