Theory assignPlaceEmptyStore
Ancestors
  loweringStateRelDefs
  placeStore placeMemoryLiveRegion stmtSimDefs loweringPosts exprSimHypsDefs
  stmtLowering exprLowering compileEnv vyperInterpreter vyperState
  vyperScopePreservation venomState venomExecSemantics valueEncodingProps
  abiDecodeStaticProps exprLoweringProps vyperStorage compileEnv

Theorem assign_place_empty_store_framed:
  !ctx func cenv cx env ee ff s p w loc imm dst_op dty dtv sa sb es0 sa0 s0.
    compile_store_at_loc imm dst_op (Lit 0w) (SOME loc) sa = ((), sb) /\
    loc <> LocCode /\ loc <> LocCalldata /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
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
    write_place cx p (default_value dtv) ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    alloca_frame cenv es0 sa0 s0 cenv ee s ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_frame cenv es0 sa0 s0 cenv ff t
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = (case loc of LocStorage => sstore w 0w s
                  | LocTransient => tstore w 0w s
                  | _ => mstore (w2n w) 0w s)` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, Abbr `u`, slot_loc_def] >>
         drule_all place_store_empty_backend_state >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         `loc = LocMemory` by fs[place_ptr_rel_def] >>
         gvs[Abbr `u`] >> irule place_store_empty_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[])
     >> gvs[place_ptr_rel_def]) >>
  `(loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
   (loc = LocMemory \/ ~s.vs_call_ctx.cc_static)` by
    (Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     `~cx.txn.is_static` by
       (Cases_on `cx.txn.is_static` >>
        fs[write_place_def, write_storage_slot_def, check_not_static_def,
           bind_def, ignore_bind_def, assert_def, check_def, raise_def, return_def]) >>
     fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
     Cases_on `b` >> gvs[]) >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                         | _ => MSTORE) [dst_op; Lit 0w] sa = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_store_at_loc_def]) >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qpat_assum `emit_void _ _ _ = _` (irule_at Any) >> simp[] >>
     simp[eval_operand_def]) >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[write_place_scopes_dom] >>
  `alloca_frame cenv es0 sa0 s0 cenv ff u` by
    (Cases_on `loc = LocMemory`
     >- (gvs[] >> drule_all memory_place_live_region >> strip_tac >>
         `32 <= type_memory_size dtv` by
           (drule place_store_empty_representation >>
            disch_then (qspecl_then [`get_tenv cx`, `dtv`, `0`,
              `(mstore 0 0w s).vs_memory`] mp_tac) >>
            simp[mstore_mem_word_at_same]) >>
         irule alloca_frame_region_write >>
         qpat_assum `local_region _ _ _ _ _ _` (irule_at Any) >>
         simp[Abbr `u`] >> rpt strip_tac >>
         irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
     `!n b z. local_region cenv ff.scopes u n b z ==>
                 local_region cenv ee.scopes s n b z` by
       (rpt strip_tac >> irule local_region_kept >>
        qpat_assum `stmt_state_rel _ _ _ _ ee s` (irule_at Any) >>
        qpat_assum `local_ptrs_reserved _ _` (irule_at Any) >>
        qpat_assum `local_region _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
     gvs[alloca_frame_def, Abbr `u`, tstore_def] >> metis_tac[]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qpat_assum `!x. lookup_var x u = lookup_var x s`
    (assume_tac o REWRITE_RULE [lookup_var_def]) >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  qpat_x_assum `alloca_frame _ _ _ _ _ ff u` mp_tac >>
  simp[alloca_frame_def, local_region_def, lookup_var_def]
QED
