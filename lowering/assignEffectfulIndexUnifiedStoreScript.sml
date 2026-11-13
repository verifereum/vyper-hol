Theory assignEffectfulIndexUnifiedStore
Ancestors
  assignEffectfulIndexOwnedStore assignEffectfulIndexBytesStore
  placeRelayoutMemoryRun exprSimProps vyperTypeArgFits compileEnv
  tuplePlaceStep assignEffectfulIndexSnapshotFrame loweringPosts freshWrites
  aggregateEvaluatedLayout exprLoweringProps venomMemDefs valueEncodingTyping
  tuplePlaceSnapshot exprSimHyps

Theorem assign_effectful_snapshot_unified_store_ready:
  target_post ctx func cenv cx ee ss st u mid (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ val_wf stv v /\
  eval_operand (vv_operand snap) u = SOME sw /\
  (!x. vv_operand snap = Var x ==> not_fresh_at ss x) /\
  (!l. vv_operand snap <> Label l) /\
  ss.cs_next_var <= st.cs_next_var /\ ss.cs_next_id <= st.cs_next_id /\
  (if is_word_type (lowered_value_type cenv e) then
     vv_location snap = NONE /\ sw = typed_val_to_w256 stv v
   else vv_location snap = SOME LocMemory /\
     val_in_memory stv v (w2n sw) u.vs_memory /\
     ?aid sz. aid < ss.cs_next_id /\
       FLOOKUP u.vs_allocas aid = SOME (w2n sw,sz) /\
       type_memory_size stv <= sz /\
       (!n b len. local_region cenv ee.scopes u n b len ==>
         w2n sw + sz <= b \/ b+len <= w2n sw)) /\
  compile_assign_value cenv dst loc (vv_operand snap) (is_word_type dty)
    (vv_location snap) dty (lowered_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE)
    (type_memory_bytes cenv dty) st = ((),sf) /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
  expr_sim_inv cenv cx env mid /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv st /\ storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id mid.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  (loc = LocMemory ==> w2n dw + type_memory_size dtv < dimword (:256)) /\
  (loc = LocMemory ==> 0 < type_memory_size dtv) /\
  (loc = LocMemory /\ (is_word_type (lowered_value_type cenv e) \/
    dty = lowered_value_type cenv e) ==>
    type_memory_size dtv + 64 < dimword (:256)) /\
  (loc = LocMemory /\ ~is_word_type (lowered_value_type cenv e) ==>
    0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256)) /\
  eval_operand dst s = SOME dw /\
  0 < type_slot_size dtv /\
  (loc <> LocMemory /\ dty <> lowered_value_type cenv e /\
    ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
    type_alloc_ok cenv dty) /\
  write_place cx p v mid = (INL (),ff) /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at st x ==> lookup_var x z = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    ~z.vs_halted /\ z.vs_current_bb = sf.cs_current_bb /\
    z.vs_inst_idx = LENGTH sf.cs_current_insts /\
    alloca_frame cenv mid st s cenv ff z
Proof
  strip_tac >>
  Cases_on `loc = LocMemory /\
    ~(is_word_type (lowered_value_type cenv e) \/ dty = lowered_value_type cenv e)`
  >- suspend "widening" >>
  irule assign_effectful_snapshot_owned_store_ready >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`dtv`, `dw`, `stv`, `sw`, `v`] >> simp[] >>
  Cases_on `loc = LocMemory` >> gvs[arithmeticTheory.ADD_COMM]
QED

Resume assign_effectful_snapshot_unified_store_ready[widening]:
  gvs[] >>
  Cases_on `is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)`
  >- (irule assign_effectful_snapshot_bytes_store_ready >> simp[] >>
      conj_tac >- metis_tac[] >>
      goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexistsl_tac [`dtv`, `dw`, `e`, `snap`, `stv`, `sw`, `v`] >>
      gvs[arithmeticTheory.ADD_COMM] >>
      qexistsl_tac [`aid`, `sz`] >> simp[arithmeticTheory.ADD_COMM] >>
      metis_tac[]) >>
  suspend "relayout"
QED

Resume assign_effectful_snapshot_unified_store_ready[relayout]:
  `~is_word_type dty` by
    metis_tac[arg_type_fits_word_type, vyperTypeSystemTheory.type_widens_to_def] >>
  `~is_bytestring_type dty` by
    metis_tac[arg_type_fits_bytestring_source, vyperTypeSystemTheory.type_widens_to_def] >>
  `eval_operand (vv_operand snap) s = SOME sw` by
    metis_tac[tuple_place_target_operand] >>
  `val_in_memory stv v (w2n sw) s.vs_memory` by
    metis_tac[assign_effectful_target_snapshot_value, arithmeticTheory.ADD_COMM] >>
  `stmt_state_rel ctx func cenv cx mid s /\
   place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
   (!x. dst = Var x ==> not_fresh_at st x)` by gvs[target_post_def] >>
  `!x. vv_operand snap = Var x ==> not_fresh_at st x` by
    metis_tac[not_fresh_at_mono] >>
  `value_has_type dtv v` by
    (drule_all type_widens_to_value_has_type >> simp[]) >>
  `val_wf dtv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (`?aid sz. aid < ss.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (w2n sw,sz) /\
       type_memory_size stv <= sz` by
       (gvs[target_post_def] >> metis_tac[]) >>
     `alloca_next_valid s /\ alloca_room ctx func s` by
       gvs[stmt_state_rel_def, alloca_inv_def] >>
     `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
     fs[alloca_next_valid_def] >> res_tac >> decide_tac) >>
  fs[] >> irule place_relayout_memory_run >> simp[] >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  simp[val_footprint_le]
QED
Finalise assign_effectful_snapshot_unified_store_ready
