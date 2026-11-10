Theory assignPlaceStoreReady
Ancestors
  assignPlaceProvenance assignPlaceSourceBounds assignPlaceMemoryCopy assignPlaceBytesStore
  placeRelayoutMemoryRun exprSimHyps annassignRelayoutSource
  exprSimTypedAlloc valueTypingMemoryProps loweringPosts stmtSimDefs
  stmtLowering compileEnv words placeStore assignPlaceStaging

(* The differing-layout memory branch consumes current-state provenance,
   not a capacity-sized ownership claim about the original RHS allocation. *)
Theorem assign_place_relayout_from_provenance:
  compile_assign_value cenv dst LocMemory src F src_loc dty sty info bytes
    sa = ((),sb) /\
  (src_loc = NONE \/ src_loc = SOME LocMemory) /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ sty <> dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  expr_sim_inv cenv cx env ee /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ 0 < type_memory_size stv /\
  expr_val_rel cx sty v src s /\
  expr_val_at cenv cx sty si sj ee v src s /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (irule nonbytes_expr_val_at_bound >> metis_tac[]) >>
  `type_memory_size stv = 0 \/
   w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by
    (irule nonbytes_expr_val_at_memory_separation >> metis_tac[]) >>
  `value_has_type dtv v` by
    (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
     strip_tac >> gvs[]) >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[value_has_type_memory_wf] >>
  `type_memory_bytes cenv sty = type_memory_size stv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  gvs[] >> irule place_relayout_memory_run >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`p`, `v`] >> simp[]
QED

(* Store-only continuation: unwrap and target framing belong to the caller. *)
Theorem assign_place_store_from_expr_post:
  compile_assign_value cenv dst loc src (is_word_type dty) src_loc dty
    (post_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32,
             type_memory_bytes cenv et) | _ => NONE)
    (type_memory_bytes cenv dty) su = ((),sb) /\
  expr_post ctx func cenv cx e es sa su s0 ee v src s /\
  expr_sim_inv cenv cx env ee /\
  type_widens_to (get_tenv cx) (post_value_type cenv e) dty /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\
  loc <> LocCode /\ loc <> LocCalldata /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type dty) /\
  storage_place_region cx p /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv su /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee su s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[expr_post_def] >>
  Cases_on `loc = LocMemory`
  >- (Cases_on `~is_word_type (post_value_type cenv e) /\
        ~is_bytestring_type (post_value_type cenv e) /\
        ~is_word_type dty /\ ~is_bytestring_type dty /\
        post_value_type cenv e <> dty /\
        (src_loc = NONE \/ src_loc = SOME LocMemory) /\
        0 < type_memory_size stv`
      >- suspend "relayout_memory" >>
      suspend "remaining_memory") >>
  `loc = LocStorage \/ loc = LocTransient` by
    (Cases_on `loc` >> gvs[]) >>
  Cases_on `is_bytestring_type (post_value_type cenv e) /\ is_bytestring_type dty`
  >- suspend "bytes_storage" >>
  Cases_on `is_word_type dty`
  >- suspend "word_storage" >>
  suspend "aggregate_storage"
QED

Resume assign_place_store_from_expr_post[bytes_storage]:
  gvs[] >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory stv v (w2n sw) s.vs_memory` by
    gvs[expr_val_rel_def, valueCopyBytesTheory.is_bytestring_word_type] >>
  `w2n sw + val_footprint stv v < dimword (:256)` by
    (irule expr_val_at_bound >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     simp[valueCopyBytesTheory.is_bytestring_word_type] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!et n. dty <> ArrayT et (Dynamic n)` by
    (Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def]) >>
  `(case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes cenv et + 31) DIV 32,
            type_memory_bytes cenv et) | _ => NONE) = NONE` by
    (Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def]) >>
  fs[] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    alloca_frame cenv ee su s cenv ff t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule assign_place_bytes_storage_run >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[]
QED

Resume assign_place_store_from_expr_post[word_storage]:
  `post_value_type cenv e = dty` by
    metis_tac[compileEnvTheory.type_widens_to_word] >>
  fs[] >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
                        | _ => MSTORE) [dst;src] su = ((),sb)` by
    (Cases_on `loc` >> gvs[compile_assign_value_def,
        comp_return_def, comp_bind_def]) >>
  gs[] >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (loc = LocStorage \/ loc = LocTransient ==> t.vs_memory = s.vs_memory)` by
    (irule place_store_word_run >> simp[] >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `expr_val_rel _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >> simp[] >>
     metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  irule alloca_frame_of_mem_frame >> simp[] >>
  goal_assum (drule_at Any)
QED

Resume assign_place_store_from_expr_post[relayout_memory]:
  gvs[] >>
  irule assign_place_relayout_from_provenance >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED
