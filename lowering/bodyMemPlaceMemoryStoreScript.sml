(* Counted writes of empty values into computed memory places. *)
Theory bodyMemPlaceMemoryStore
Ancestors
  augAssignPlaceWordStoreMemory placeStore stmtLowering loweringPosts
  bodyDeclMemoryCore exprSimProps exprLoweringProps fragGasMode venomState

Theorem place_store_empty_memory_run_mem:
  compile_store_at_loc imm dst_op (Lit 0w) (SOME LocMemory) sa = ((),sb) /\
  eval_operand dst_op s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  (!x. dst_op = Var x ==> not_fresh_at sa x) /\
  has_length_word dty /\ evaluate_type (get_tenv cx) dty = SOME dtv /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
  (!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (default_value dtv) ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\
  w2n w + 32 <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ff (mstore (w2n w) 0w s)` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[])
     >- (irule place_store_empty_memory_state >>
     goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ dty = _`)) >> simp[]) >>
     gvs[place_ptr_rel_def]) >>
  `emit_void MSTORE [dst_op; Lit 0w] sa = ((),sb)` by
    gvs[compile_store_at_loc_def] >>
  `gas_marked_path T ctx func s 0
     (OK ((mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func
     ((mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   (!x. lookup_var x (mstore (w2n w) 0w s) = lookup_var x s) /\
   (mstore (w2n w) 0w s).vs_allocas = s.vs_allocas /\
   (mstore (w2n w) 0w s).vs_alloca_next = s.vs_alloca_next /\
   ~(mstore (w2n w) 0w s).vs_halted /\
   (mstore (w2n w) 0w s).vs_current_bb = sb.cs_current_bb` by
    (irule place_store_emit_run_mem >> simp[] >>
     qexistsl_tac [`dst_op`, `LocMemory`, `Lit 0w`, `sa`] >>
     simp[eval_operand_def]) >>
  qexists_tac `(mstore (w2n w) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED
