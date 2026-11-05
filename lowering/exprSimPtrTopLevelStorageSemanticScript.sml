(* Same-endpoint semantic interface for completed storage copies. *)
Theory exprSimPtrTopLevelStorageSemantic
Ancestors
  exprSimPtrTopLevelStorageEnsure exprSimCopy exprSimStorageCopy
  exprLoweringProps compileEnv valueEncoding loweringPosts

Theorem toplevel_copy_prefix_state_rel:
  stmt_state_rel ctx fn cenv cx es u /\
  local_ptrs_reserved cenv st /\
  copy_prefix loc a b n u n t /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x u) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,32*n) /\
  (!name lb len. local_region cenv es.scopes u name lb len ==>
    regions_disjoint b (32*n) lb len) ==>
  stmt_state_rel ctx fn cenv cx es t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`b`, `inst`, `u`, `st`, `32*n`] >>
  gvs[copy_prefix_def, regions_disjoint_def] >> metis_tac[]
QED

(* The semantic transport consumes the very endpoint chosen by Ensure. *)
Theorem toplevel_storage_ensure_ptr_post_effects:
  vv_post ctx fn cenv cx e es sa sm s0 es' (Value v) vv s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (loc = LocStorage \/ loc = LocTransient) /\
  storage_holds cx (loc = LocTransient) (expr_type e) (Value v) a es' s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  n = type_slot_size tv /\ type_memory_size tv <= nb /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx fn cenv cx e es sa sb s0 es' v op t /\
    ?u w.
      stmt_state_rel ctx fn cenv cx es' u /\ u.vs_memory = s.vs_memory /\
      lookup_var p u = SOME w /\ lookup_var p t = SOME w /\
      copy_prefix loc a (w2n w) n u n t /\ copy_static t = copy_static u /\
      (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
      tnf.t_mem SUBSET toplevel_copy_taint_bound loc a (w2n w) tn n /\
      (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) nb b len) /\
      (!name b len. local_region cenv es'.scopes u name b len ==>
        regions_disjoint (w2n w) nb b len) /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
      t.vs_transient = s.vs_transient /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
      sm.cs_next_id < sb.cs_next_id /\
      LENGTH u.vs_memory <= LENGTH t.vs_memory /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,nb) /\
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = sm.cs_next_id)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx fn cenv cx es' s` by fs[vv_post_def] >>
  drule_all toplevel_storage_ensure_ptr_semantic_effects >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `storage_holds cx (loc = LocTransient) (expr_type e) (Value v) a es' u` by
    gvs[storage_holds_def, venomStateTheory.contract_storage_def,
      venomStateTheory.contract_transient_def] >>
  `loc = if loc = LocTransient then LocTransient else LocStorage` by metis_tac[] >>
  `val_wf tv v /\ val_in_memory tv v (w2n w) t.vs_memory /\
    val_footprint tv v <= type_memory_size tv` by
    (irule copy_buffer_storage_contents >>
     rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x u` by
    metis_tac[] >>
  `expr_post ctx fn cenv cx e es sa sb s0 es' v op t` by
    (irule copy_buffer_post_transport >>
     simp[] >>
     qrefinel [`_`, `sm`, `_`, `_`, `nb`] >>
     rpt (goal_assum (drule_at Any)) >>
     gvs[copy_prefix_def, venomStateTheory.eval_operand_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`, `p`] >> simp[] >>
  qexists_tac `u` >> simp[] >> metis_tac[]
QED

Theorem toplevel_storage_ensure_ptr_post:
  vv_post ctx fn cenv cx e es sa sm s0 es' (Value v) vv s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (loc = LocStorage \/ loc = LocTransient) /\
  storage_holds cx (loc = LocTransient) (expr_type e) (Value v) a es' s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  n = type_slot_size tv /\ type_memory_size tv <= nb /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sm = (op,sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx fn cenv cx e es sa sb s0 es' v op t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_storage_ensure_ptr_post_effects >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `Gf`, `tnf`, `p`] >> simp[]
QED
