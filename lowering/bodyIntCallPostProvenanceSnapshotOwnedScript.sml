(* A nonword snapshot reuses the materialization execution certificate.
   Alignment and all source/execution prerequisites remain explicit. *)
Theory bodyIntCallPostProvenanceSnapshotOwned
Ancestors abiEncodeMaterialize exprLowering compileEnv context

Theorem compile_snapshot_vv_owned_sim:
  compile_snapshot_vv ce T vv sm = (saved,sb) /\
  vv_type vv = lowered_value_type ce e /\
  ~is_word_type (vv_type vv) /\
  expr_body_pre ce cx env e es_pre /\
  vv_post ctx func ce cx e es sa sm s0 es' tvv vv r /\
  stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  read_result cx tvv es' = (INL v,es') /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
         ~is_word_type (post_value_type ce e) ==>
         type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
         type_memory_size tvt < 2 ** 64) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) ==>
  frag_exec ctx sm sb (\s. s = r)
    (\s. stmt_state_rel ctx func ce cx es' s /\
      wb_frame ce es es' sa s0 s /\
      expr_val_rel cx (lowered_value_type ce e) v (vv_operand saved) s /\
      expr_val_at ce cx (lowered_value_type ce e) sa sb es' v
        (vv_operand saved) s /\
      sm.cs_next_id < sb.cs_next_id /\
      ?w. eval_operand (vv_operand saved) s = SOME w /\
        FLOOKUP s.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
        val_in_memory tv v (w2n w) s.vs_memory /\
        (!name b len. local_region ce es'.scopes s name b len ==>
           w2n w + type_memory_size tv <= b \/ b + len <= w2n w)) R
Proof
  strip_tac >>
  Cases_on `compile_materialize_vv ce (lowered_value_type ce e) vv sm` >>
  gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def,
      vv_operand_def, mk_ptr_def] >>
  drule compile_materialize_vv_owned_sim >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED
