(* Store correctness and byte preservation share a single execution witness. *)
Theory tuplePlaceFramedStore
Ancestors
  tuplePlaceStore placeStore abiValueEncoding valueEncodingProps
  vyperInterpreter vyperState vyperValue vyperTypeSystem
  venomState venomExecSemantics loweringPosts exprSimHypsDefs
  stmtSimDefs exprSimProps emitHelper exprLoweringProps compileEnv

Theorem tuple_place_word_run_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op dty dtv v sa sb a n.
    emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; op] sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    is_word_type dty /\ expr_val_rel cx dty v op s /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 dtv v)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w (typed_val_to_w256 dtv v) s
                  | LocTransient => tstore w (typed_val_to_w256 dtv v) s
                  | _ => mstore (w2n w) (typed_val_to_w256 dtv v) s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
     drule_all place_store_word_backend_state >> Cases_on `b` >> gvs[]) >>
  `(loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
   (loc = LocMemory \/ ~s.vs_call_ctx.cc_static)` by
    (Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     `~cx.txn.is_static` by
       (Cases_on `cx.txn.is_static` >>
        fs[write_place_def, write_storage_slot_def, check_not_static_def,
           vyperStateTheory.bind_def, ignore_bind_def, assert_def, check_def,
           raise_def, vyperStateTheory.return_def]) >>
     fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
     Cases_on `b` >> gvs[]) >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qpat_assum `emit_void _ _ _ = _` (irule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `mem_bytes_at a n u.vs_memory = mem_bytes_at a n s.vs_memory` by
    (Cases_on `loc = LocMemory`
     >- (gvs[Abbr `u`] >> irule mstore_mem_bytes_at_disjoint >>
         drule_all abi_word_type_size >> simp[]) >>
     gvs[Abbr `u`, sstore_def, tstore_def]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def]
QED
