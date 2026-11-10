(* Destination-indexed endpoints for selected conditional arms. *)
Theory bodyIfExpDestinationEndpoint
Ancestors
  bodyIfExpAggregateEndpoint bodyIfExpNormalizationSuffix bodyIfExpWidenedTyping
  bodyIfExpSelectedEndpoint bodyIfExpMemory exprSimIfExp exprLowering

Theorem ifexp_compiled_arm_assign_phi[local]:
  ~is_word_type dty /\ ~is_bytestring_type dty /\ sty <> dty /\
  ~same_memory_layout ce sty dty /\
  (?src. unwrap_value ce vv = compileEnv$comp_return src) /\
  compile_ifexp_arm ce dty sty vv sa = (op,sb) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sc) /\
  fn_has_code sb sc func ==>
  !buf sm. compile_alloc_buffer (type_memory_bytes ce dty) sa = (buf,sm) ==>
    emitted_blocks sm sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, contextTheory.compile_store_memory_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  irule ifexp_typed_normalization_assign_exit_phi >>
  metis_tac[]
QED

Theorem ifexp_compiled_aggregate_assign_phi:
  compile_expr ce ty e se = (vv,sa) /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
  ~is_word_type (lowered_value_type ce e) /\
  lowered_value_type ce e <> expr_type e /\
  ~same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  emit_inst ASSIGN [op] [rv] sb = ((),sc) /\
  fn_has_code sb sc func ==>
  !buf sm. compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) ==>
    emitted_blocks sm sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `?src. unwrap_value ce vv = compileEnv$comp_return src` by
    (irule ifexp_different_type_unwrap_pure >> metis_tac[]) >>
  metis_tac[ifexp_compiled_arm_assign_phi]
QED

Theorem ifexp_compiled_same_layout_endpoint:
  compile_expr ce ty e se = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  lowered_value_type ce e <> expr_type e /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  post_value_type ce e = lowered_value_type ce e /\
  same_memory_layout ce (lowered_value_type ce e) (expr_type e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
  0 < type_memory_size stv /\ value_has_type dtv v /\ val_wf dtv v /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx func ce cx e es origin sa s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee raw vv s ==>
  sb = sa /\
  expr_post ctx func ce cx (IfExp (expr_type e) c a b) es origin sb s0 ee v op s /\
  vv_store_bound cx (expr_type e) (expr_type e) ee raw
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `?src sw. unwrap_value ce vv = compileEnv$comp_return src /\
     src = vv_operand vv /\
     expr_post ctx func ce cx e es origin sa s0 ee v src s /\
     eval_operand src s = SOME sw /\
     w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (irule bodyIfExpCompiledAggregateTheory.ifexp_compiled_aggregate_source >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[compile_ifexp_arm_def, compileEnvTheory.comp_return_def] >>
  conj_tac
  >- (irule ifexp_post_annotated >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `val_store_size dtv v <= type_memory_size dtv` by
    (irule exprSimPropsTheory.val_store_size_le >> simp[]) >>
  simp[exprSimMemDefsTheory.vv_store_bound_def, contextTheory.mk_ptr_def] >>
  rpt strip_tac >> gvs[] >>
  `type_memory_size dtv <= type_memory_size stv` by
    (`type_memory_size dtv = type_memory_size stv` by
       (fs[contextTheory.same_memory_layout_def] >> metis_tac[]) >> simp[]) >>
  decide_tac
QED
