(* A positioned nonword snapshot retains the materialization path's owner.
   All source, layout and positioned-entry prerequisites remain explicit. *)
Theory bodyIntCallPostProvenanceSnapshotPath
Ancestors exprSimAbiEncodeArgsMaterializePath exprLowering compileEnv context

Theorem compile_snapshot_vv_owned_path:
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
  type_memory_size tv + 64 < dimword (:256) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func r 0 (OK t) /\
      materialize_owned_post ctx func ce cx e es sa sm sb s0 es' v
        (vv_operand saved) tv t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `compile_materialize_vv ce (lowered_value_type ce e) vv sm` >>
  gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def,
      vv_operand_def, mk_ptr_def] >>
  irule compile_materialize_vv_owned_path >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
