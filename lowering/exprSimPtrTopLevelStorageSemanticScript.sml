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
  qexistsl_tac [`t`, `Gf`, `tnf`, `p`] >> simp[] >>
  irule copy_buffer_post_transport >>
  simp[] >>
  qrefinel [`_`, `sm`, `_`, `_`, `nb`] >>
  rpt (goal_assum (drule_at Any)) >>
  gvs[copy_prefix_def, venomStateTheory.eval_operand_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
