Theory bodyPtrMakeArrayExternalCaller
Ancestors
  bodyPtrMakeArrayExternalSize exprReasonOperand exprLoweringProps exprLowering
  context compileEnv vyperAST list bodyPtrMakeArrayConsumerPost exprCallBounds
  vyperTypeStatePreservation valueEncodingTyping exprSimProps

Theorem external_located_lowered_type:
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  lowered_value_type cenv e = expr_type e
Proof
  Cases_on `e` >> simp[lowered_value_type_def, expr_type_def]
  >~ [`Literal ann lit`]
  >- (simp[Once compile_expr_def] >> strip_tac >>
      drule reason_compile_literal >> simp[reason_result_shape_def])
  >~ [`Call ann target args default_ret`]
  >- (simp[Once compile_expr_def] >> strip_tac >>
      drule reason_compile_call >> simp[reason_result_shape_def])
  >~ [`Builtin ann bi args`]
  >- (Cases_on `bi` >> simp[lowered_value_type_def, expr_type_def] >>
      pure_rewrite_tac[Once compile_expr_raw_def] >> strip_tac >>
      drule reason_compile_expr_builtin_shape_classify >>
      strip_tac >> gvs[reason_result_shape_def] >>
      gvs[builtin_child_callback_def, invalid_expr_call_def, expr_type_def,
        AllCaseEqs()] >>
      qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
      pure_rewrite_tac[Once compile_expr_raw_def] >> strip_tac >>
      drule_at (Pos last) reason_builtin_fresh >>
      simp[reason_result_shape_def]) >>
  rename1 `TypeBuiltin ann tb rt args` >>
  Cases_on `tb` >> simp[lowered_value_type_def, expr_type_def] >>
  simp[Once compile_expr_def] >>
  simp[Once compile_type_builtin_dispatch_component_eq] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[base_ptr_def, mk_ptr_def, AllCaseEqs()] >>
  gvs[oneline as_ptr_val_def, AllCaseEqs(), mk_ptr_def]
QED

Theorem external_located_post_type:
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >> drule_all external_located_lowered_type >>
  disch_then (ACCEPT_TAC o MATCH_MP loweringPostsTheory.post_value_type_lowered)
QED

Theorem external_located_buffer_size:
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  p.ptr_location <> LocMemory /\
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv
Proof
  strip_tac >> drule_all external_located_lowered_type >>
  drule_all external_unwrap_source_size >> strip_tac >> gvs[]
QED

Theorem external_storage_value_bounds:
  vv_post ctx fn cenv cx e es sa sb s0 es' raw (LocatedValue ty p) s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  read_result cx raw es' = (INL v,es') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  post_value_type cenv e = expr_type e ==>
  val_wf tv v /\ val_footprint tv v <= type_memory_size tv
Proof
  strip_tac >> drule_all make_array_storage_consumer_read >> strip_tac >>
  gvs[] >>
  `value_has_type tv v` by metis_tac[cj 1 decode_value_well_typed] >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  simp[val_footprint_le]
QED

(* Original sa is the child's start; sn is the allocation/unwrap start after
   the destination ADD. These facts discharge endpoint continuation ordering
   and reservation; incoming return-pointer oldness transports by the last
   conjunct. Scope equality comes directly from eval_expr_preserves_scopes_dom
   on the successful child evaluation, unchanged by the target-only ADD. *)
Theorem external_consumer_compile_frame:
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  local_ptrs_reserved cenv sa ==>
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  local_ptrs_reserved cenv sn /\ copy_old_operand sn p.ptr_operand /\
  (!x. not_fresh_at sa x ==> not_fresh_at sn x)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`, `ty`, `e`, `sa`] mp_tac (cj 1 compile_expr_ci_mono) >> simp[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`ADD`, `[buf; Lit (n2w off)]`, `sm`] mp_tac ci_mono_emit_op >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
    sm.cs_next_var <= sn.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[] >> conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  simp[exprSimCopyTheory.copy_old_operand_def] >> rpt strip_tac >>
  `not_fresh_at sm x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >>
     simp[vv_operand_def] >> disch_then irule >> metis_tac[local_ptrs_reserved_next_var]) >>
  fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem external_located_unwrap_sizes:
  compile_expr cenv ty e sa = (LocatedValue t p,sm) /\
  vv_post ctx fn cenv cx e es sa sn s0 es' raw (LocatedValue t p) s /\
  p.ptr_location <> LocMemory /\
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ~is_word_type (expr_type e) ==>
  t = expr_type e /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_bytes cenv t /\
  type_memory_bytes cenv t = type_memory_size tv /\
  (type_memory_bytes cenv t + 31) DIV 32 = type_slot_size tv /\
  32 * type_slot_size tv = type_memory_size tv /\
  type_memory_bytes cenv t < dimword(:256)
Proof
  strip_tac >>
  drule_all external_located_lowered_type >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_lowered >> first_assum ACCEPT_TAC) >>
  `t = expr_type e` by fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def] >>
  drule_all external_unwrap_source_size >> strip_tac >> gvs[]
QED
