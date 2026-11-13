(* Aggregate store correctness and old-allocation frame at one endpoint. *)
Theory tuplePlaceValueFrame
Ancestors
  tuplePlaceFramedStore tuplePlaceMemoryFrame tuplePlaceValueStorageFrame
  tuplePlaceDynFrame placeStoreMemory placeMemoryStoreEffect vyperTypeArgFits
  placeMemoryStateRebuild placeStore tuplePlaceStore exprSimProps
  abiValueEncoding valueEncodingProps exprLoweringProps
  stmtLowering exprLowering compileEnv loweringPosts stmtSimDefs venomState
  vyperInterpreter vyperState vyperValue vyperTypeSystem exprSimHypsDefs

Theorem tuple_place_value_run_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
       | _ => NONE) (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
       evaluate_type (get_tenv cx) dty = SOME dtv ==>
       type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n sw \/ sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
       w2n sw + type_memory_size stv <= s.vs_alloca_next /\
       !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
         w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==> !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    (loc <> LocMemory /\ dty <> sty /\
     ~(is_bytestring_type dty /\ is_bytestring_type sty) ==> type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!aid b len a n dtv. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
        evaluate_type (get_tenv cx) dty = SOME dtv /\
        (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = LocMemory`
  >- suspend "memory" >>
  Q.SUBGOAL_THEN `loc = LocStorage \/ loc = LocTransient` assume_tac
  >- (Cases_on `p` >> gvs[place_ptr_rel_def] >>
      rename1 `slot_loc tr` >> Cases_on `tr` >> gvs[slot_loc_def]) >>
  `dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
   type_alloc_ok cenv dty` by metis_tac[] >>
  Cases_on `?et n. dty = ArrayT et (Dynamic n)`
  >- (drule_all tuple_place_value_dyn_run_frame >> strip_tac >>
      qexists_tac `t` >> simp[] >> metis_tac[]) >>
  `!et n. dty <> ArrayT et (Dynamic n)` by metis_tac[] >>
  drule_all tuple_place_value_storage_run_frame >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

Resume tuple_place_value_run_frame[memory]:
  Cases_on `is_word_type dty`
  >- suspend "memory_word" >>
  drule_all tuple_place_memory_forward_frame >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_stmt_state >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ t.vs_memory`)) >>
     qexistsl_tac [`dty`, `ee`, `env`, `p`, `r`, `s`, `sa`] >>
     gvs[] >> conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!aid b len a n. _ ==> mem_bytes_at _ _ _ = _` irule >>
  metis_tac[]
QED

Resume tuple_place_value_run_frame[memory_word]:
  `sty = dty` by metis_tac[type_widens_to_word] >> gvs[] >>
  `emit_void MSTORE [dst_op; op] sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `eval_operand op s = SOME (typed_val_to_w256 stv v)` by fs[expr_val_rel_def] >>
  qabbrev_tac `u = mstore (w2n w) (typed_val_to_w256 stv v) s` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         unabbrev_all_tac >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[]) >>
     gvs[place_ptr_rel_def, slot_loc_def]) >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qexistsl_tac [`dst_op`, `LocMemory`, `op`, `sa`, `w`,
                    `typed_val_to_w256 stv v`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >>
  rpt strip_tac >> gvs[] >> simp[Abbr `u`] >>
  irule mstore_mem_bytes_at_disjoint >>
  drule_all abi_word_type_size >> simp[]
QED

Finalise tuple_place_value_run_frame
