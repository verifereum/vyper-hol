Theory assignPlaceRelayoutProvenance
Ancestors
  assignPlaceProvenance assignPlaceSourceBounds assignPlaceMemoryCopy assignPlaceBytesStore
  placeRelayoutMemoryRun exprSimHyps annassignRelayoutSource
  exprSimTypedAlloc valueTypingMemoryProps loweringPosts stmtSimDefs
  stmtLowering compileEnv words placeStore assignPlaceStaging

Theorem assign_place_relayout_from_provenance:
  compile_assign_value cenv dst LocMemory src F src_loc dty sty bytes
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
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`p`, `v`] >> simp[]
QED
