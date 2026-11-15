(* Snapshot entry facts are discharged at the successful base endpoint. *)
Theory bodyIntCallPostProvenanceCapturedEntry
Ancestors
  bodyIntCallPostProvenanceSnapshotPath bodyIntCallCompilerTags bodyIntCallArgType
  bodyPtrSubscriptSeamArrayMemoryRepresented exprSimSource exprSimHyps
  exprOperandVar exprLoweringProps loweringStateRelDefs
  vyperEvalExprPreservesScopesDom valueTypingMemoryProps
  exprSimAbiEncodeArgsMaterializePath exprSimProps
  loweringPosts compileEnv context vyperState words

Theorem intcall_captured_snapshot_entry:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  expr_type e = ArrayT et bd /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  compile_expr ce ty e sa = (vv,sm) /\
  compile_snapshot_vv ce T vv sm = (saved,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw vv r /\
  stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?tv t. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    gas_marked_path F ctx func r 0 (OK t) /\
    materialize_owned_post ctx func ce cx e es sa sm sb s0 ee v
      (vv_operand saved) tv t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[effect_free_post_value_type] >>
  `lowered_value_type ce e = expr_type e` by metis_tac[array_lowered_value_type] >>
  `vv_type vv = expr_type e` by
    (drule intcall_compile_expr_tag >> disch_then (qspecl_then [`ty`,`sa`,`ce`] mp_tac) >> simp[]) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt v` by metis_tac[] >>
  `val_wf tvt v` by metis_tac[value_has_type_memory_wf] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 1 compile_expr_grows] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by metis_tac[eval_expr_preserves_scopes_dom] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `type_memory_bytes ce (expr_type e) = type_memory_size tvt /\
   type_memory_size tvt < 2 ** 64` by metis_tac[expr_body_pre_copy_ok] >>
  `type_memory_size tvt + 64 < dimword (:256)` by
    (qpat_x_assum `type_memory_size tvt < 2 ** 64` mp_tac >>
     simp[dimword_def] >> decide_tac) >>
  qexists_tac `tvt` >> simp[] >>
  irule compile_snapshot_vv_owned_path >> goal_assum (drule_at Any) >>
  gvs[] >> metis_tac[]
QED
