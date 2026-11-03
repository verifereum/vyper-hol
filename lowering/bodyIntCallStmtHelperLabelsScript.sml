(* Expression closure and compiler interfaces for internal statement bodies. *)
Theory bodyIntCallStmtHelperLabels
Ancestors
  bodyIntCallSupportedExprLabels bodyIntCallMaterialLabels
  stmtLowering moduleLowering supportedStmts supportedStmtTraverse compileEnv supportedExprs list supportedTargets
  bodyIntCallLabelFrame bodyIntCallLabelReservations bodyIntCallContextLabels
  emitHelper bodyIntCallExprLabels exprLowering

Theorem declare_local_return_pc:
  declare_local ce id ty st = (ce',out) ==>
  ce'.ce_return_pc = ce.ce_return_pc
Proof
  simp[declare_local_def, comp_bind_def, comp_return_def] >>
  Cases_on `ce.ce_alloca_locals` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem declare_stmt_local_return_pc:
  declare_stmt_local ce s st = (ce',out) ==>
  ce'.ce_return_pc = ce.ce_return_pc
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def] >>
  metis_tac[declare_local_return_pc]
QED

Theorem materialize_internal_params_return_pc:
  !ps ce st ce' out.
    materialize_internal_params ce ps st = (ce',out) ==>
    ce'.ce_return_pc = ce.ce_return_pc
Proof
  Induct >> simp[materialize_internal_params_def, comp_return_def] >>
  rpt gen_tac >> Cases_on `h` >> rename1 `(name,pr)::ps` >>
  Cases_on `pr` >> rename1 `(name,is_stack,param_op)::ps` >>
  simp[materialize_internal_params_def] >>
  Cases_on `is_stack`
  >- (Cases_on `FLOOKUP ce.ce_vars name` >> simp[]
      >- metis_tac[] >>
      rename1 `FLOOKUP ce.ce_vars name = SOME loc` >> Cases_on `loc` >>
      simp[comp_bind_def, comp_ignore_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem supported_expr_structural_closure:
  supported_expr tops e /\ ~expr_has_internal_call e ==>
  (supported_pure_expr tops e \/ supported_place_expr tops e \/
   supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
  ~expr_has_internal_call e
Proof
  simp[supported_expr_def] >> metis_tac[]
QED

Theorem supported_stmt_rhs_expr:
  (s = Expr e \/ s = Return (SOME e) \/
   (?id ty. s = AnnAssign id ty e) \/ (?target. s = Assign target e) \/
   (?ty target op. s = AugAssign ty target op e) \/
   (?target. s = Append target e)) /\
  supported_stmt tops bindings s /\
  ~supported_stmt_expr_exists expr_internal_call_root s ==>
  supported_expr tops e /\ ~expr_has_internal_call e
Proof
  strip_tac >> gvs[supported_stmt_def, supported_assignment_def,
    supported_stmt_expr_exists_def, supportedExprTraverseTheory.supported_expr_exists_def,
    supportedExprTraverseTheory.expr_has_internal_call_def, supported_expr_def] >>
  metis_tac[]
QED

Theorem supported_stmt_condition_expr:
  (s = If e yes no \/ s = Assert e reason) /\
  supported_stmt tops bindings s ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  strip_tac >> gvs[supported_stmt_def] >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]
QED

Theorem supported_string_reason_expr:
  supported_string_reason tops e ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  Cases_on `e` >> simp[supported_string_reason_def]
  >~ [`Literal ty lit`] >- (Cases_on `lit` >> simp[supported_string_reason_def,
       supported_pure_expr_def,
       supportedExprTraverseTheory.expr_has_internal_call_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_internal_call_root_def]) >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]
QED

Theorem supported_iterator_range_exprs:
  supported_iterator tops ty (Range a b) n ==>
  supported_pure_expr tops a /\ supported_pure_expr tops b /\
  ~expr_has_internal_call a /\ ~expr_has_internal_call b
Proof
  strip_tac >>
  `supported_pure_expr tops a /\ supported_pure_expr tops b` suffices_by
    metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call] >>
  qpat_x_assum `supported_iterator _ _ _ _` mp_tac >>
  simp[supported_iterator_def] >>
  Cases_on `a` >> simp[supported_pure_expr_def] >>
  Cases_on `b` >> simp[supported_pure_expr_def, AllCaseEqs()]
QED

Theorem supported_iterator_array_expr:
  supported_iterator tops ty (Array e) n ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  Cases_on `e` >> simp[supported_iterator_def] >>
  rename1 `Name aty name` >> Cases_on `aty` >> simp[] >>
  rename1 `ArrayT elem bound` >> Cases_on `bound` >>
  simp[supported_pure_expr_def] >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call,
    supported_pure_expr_def]
QED

Theorem supported_assert_reason_expr:
  supported_stmt tops bindings (Assert c (AssertReason e)) ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  simp[supported_stmt_def, supported_assert_reason_def] >>
  metis_tac[supported_string_reason_expr]
QED

Theorem supported_raise_reason_expr:
  supported_stmt tops bindings (Raise (RaiseReason e)) ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  simp[supported_stmt_def, supported_raise_reason_def] >>
  metis_tac[supported_string_reason_expr]
QED

Theorem supported_log_member_expr:
  supported_stmt tops bindings (Log id es) /\ MEM e es ==>
  supported_pure_expr tops e /\ ~expr_has_internal_call e
Proof
  simp[supported_stmt_def, supported_log_def, supported_pure_exprs_every, EVERY_MEM] >>
  metis_tac[supportedExprTraverseTheory.supported_pure_no_internal_call]
QED

Theorem supported_target_subscript_expr:
  supported_target tops bindings (SubscriptTarget target_base key) /\
  ~supportedExprTraverse$target_has_internal_call (SubscriptTarget target_base key) ==>
  supported_expr tops key /\ ~expr_has_internal_call key
Proof
  Cases_on `target_base` >>
  simp[supported_target_def, supportedExprTraverseTheory.target_has_internal_call_def,
    supportedExprTraverseTheory.supported_expr_exists_def,
    supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Theorem supported_target_info_subscript_expr:
  supportedTargets$supported_target_info tops bindings (SubscriptTarget target_base key) = SOME pt /\
  ~supportedExprTraverse$target_has_internal_call (SubscriptTarget target_base key) ==>
  supported_expr tops key /\ ~expr_has_internal_call key /\
  ?target_base_pt. supportedTargets$supported_target_info tops bindings target_base = SOME target_base_pt
Proof
  simp[supportedTargetsTheory.supported_target_info_def,
    supportedExprTraverseTheory.target_has_internal_call_def,
    supportedExprTraverseTheory.supported_expr_exists_def,
    supportedExprTraverseTheory.expr_has_internal_call_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem supported_target_info_attribute_target_base:
  supportedTargets$supported_target_info tops bindings (AttributeTarget target_base fname) = SOME pt ==>
  ?target_base_pt. supportedTargets$supported_target_info tops bindings target_base = SOME target_base_pt
Proof
  simp[supportedTargetsTheory.supported_target_info_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem compiler_block_tail_declare_local:
  compiler_block_tail (declare_local ce id ty)
Proof
  rewrite_tac[declare_local_def] >> BETA_TAC >>
  Cases_on `ce.ce_alloca_locals` >> simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_declare_local:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (declare_local ce id ty) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[declare_local_def] >> BETA_TAC >>
  Cases_on `ce.ce_alloca_locals` >> simp[compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_declare_stmt_local:
  compiler_block_tail (declare_stmt_local ce s)
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, compiler_block_tail_declare_local,
    compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_declare_stmt_local:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (declare_stmt_local ce s) (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, compiler_label_hoare_declare_local,
    compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_emit_local_alloca:
  compiler_block_tail (emit_local_alloca ce id)
Proof
  rewrite_tac[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_block_tail_primitives] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[compiler_block_tail_primitives] >>
  rename1 `FLOOKUP _ _ = SOME (PtrVar ptr_op mem_sz)` >> Cases_on `ptr_op` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_emit_local_alloca:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (emit_local_alloca ce id) (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[emit_local_alloca_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME (PtrVar ptr_op mem_sz)` >> Cases_on `ptr_op` >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_internal_return:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_internal_return ce valop rpc nreturns ret_ty src_ty tys buf)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_internal_return_label_bounds]
QED

Theorem compiler_label_hoare_internal_return_from_env:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_internal_return_from_env ce ty src_ty valop rpc)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_internal_return_from_env_label_bounds]
QED

Theorem compiler_block_tail_log_eval_all:
  !es. EVERY (\e. supported_expr tops e /\ ~expr_has_internal_call e) es ==>
    compiler_block_tail (compile_log_eval_all ce es)
Proof
  Induct >> simp[compile_log_eval_all_def, compiler_block_tail_primitives] >>
  rpt strip_tac >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_lower_value >>
      irule compiler_block_tail_supported_expr >>
      metis_tac[supported_expr_structural_closure]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_log_eval_all:
  !es. EVERY (\e. supported_expr tops e /\ ~expr_has_internal_call e) es ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_log_eval_all ce es)
      (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> simp[compile_log_eval_all_def, compiler_label_hoare_typed_primitives] >>
  rpt strip_tac >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_lower_value >>
      irule compiler_label_hoare_supported_expr >>
      metis_tac[supported_expr_structural_closure]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_alloc_buffer:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_alloc_buffer sz) (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_alloc_buffer_label_bounds]
QED

Theorem compiler_block_tail_revert_with_reason:
  compiler_block_tail (compile_revert_with_reason ce vv ty sz)
Proof
  rewrite_tac[compile_revert_with_reason_def, comp_ignore_bind_def, LET_THM] >>
  BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_unwrap_value] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_revert_with_reason:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_revert_with_reason ce vv ty sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_revert_with_reason_def, comp_ignore_bind_def, LET_THM] >>
  BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_typed_primitives,
               compiler_label_hoare_context_primitives, compiler_label_hoare_alloc_buffer,
               compiler_label_hoare_unwrap_value] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_context_primitives]
QED

Theorem compiler_block_tail_log_store_data:
  !ops buf off. compiler_block_tail (compile_log_store_data ce ops buf off)
Proof
  Induct >> simp[compile_log_store_data_def, compiler_block_tail_primitives] >>
  rpt gen_tac >> rewrite_tac[compile_log_store_data_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[compiler_block_tail_primitives,
        compiler_block_tail_store_bytestring]) >> simp[]
QED

Theorem compiler_label_hoare_log_store_data:
  !ops buf off. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_log_store_data ce ops buf off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> simp[compile_log_store_data_def, compiler_label_hoare_typed_primitives] >>
  rpt gen_tac >> rewrite_tac[compile_log_store_data_def, LET_THM, comp_ignore_bind_def] >>
  BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_context_primitives] >> gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives]) >> simp[]
QED

Theorem compiler_label_hoare_encode_log_topic:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_encode_log_topic src is_bs)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_encode_log_topic_label_bounds]
QED

Theorem compiler_block_tail_log_topic_ops:
  !ops. compiler_block_tail (compile_log_topic_ops ops)
Proof
  Induct >> simp[compile_log_topic_ops_def, compiler_block_tail_primitives] >>
  gen_tac >> irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_context_accessors] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_log_topic_ops:
  !ops. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_log_topic_ops ops)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> simp[compile_log_topic_ops_def, compiler_label_hoare_typed_primitives] >>
  gen_tac >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_encode_log_topic] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_range_bound_checks:
  compiler_block_tail (compile_range_bound_checks start last rounds bound signed)
Proof
  rewrite_tac[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  Cases_on `signed` >> simp[] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_range_bound_checks:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_range_bound_checks start last rounds bound signed)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_range_bound_checks_def, comp_ignore_bind_def] >>
  Cases_on `signed` >> simp[] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_iter_elem_copy:
  compiler_block_tail (compile_iter_elem_copy ce src dst sz loc slots ty elem_ty)
Proof
  rewrite_tac[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[compiler_block_tail_primitives,
    compiler_block_tail_store_memory] >>
  Cases_on `loc` >> simp[compiler_block_tail_primitives,
    compiler_block_tail_imm_copy_to_memory, compiler_block_tail_copy_memory] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, compiler_block_tail_slot_to_memory]
QED

Theorem compiler_label_hoare_iter_copy_primitives:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_slot_to_memory src dst sz loc)
    (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_imm_copy_to_memory ctor imm src dst sz off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  conj_tac >> irule compiler_label_hoare_preserves_reservation
  >- metis_tac[compile_slot_to_memory_label_bounds] >>
  metis_tac[compile_imm_copy_to_memory_label_bounds]
QED

Theorem compiler_label_hoare_iter_elem_copy:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_iter_elem_copy ce src dst sz loc slots ty elem_ty)
    (\r out. compiler_label_reservation origin pending out)
Proof
  rewrite_tac[compile_iter_elem_copy_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives,
    compiler_label_hoare_store_memory] >>
  Cases_on `loc` >> simp[compiler_label_hoare_typed_primitives,
    compiler_label_hoare_iter_copy_primitives] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_context_primitives,
    compiler_label_hoare_iter_copy_primitives]
QED

Theorem compiler_block_tail_tuple_load_all:
  !tys off. compiler_block_tail (compile_tuple_load_all ce src tys off)
Proof
  Induct >> simp[compile_tuple_load_all_def, compiler_block_tail_primitives] >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_context_accessors] >>
       gen_tac >> BETA_TAC) >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_load_memory:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_load_memory src prim)
    (\r out. compiler_label_reservation origin pending out)
Proof
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_load_memory_label_bounds]
QED

Theorem compiler_label_hoare_tuple_load_all:
  !tys off. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_tuple_load_all ce src tys off)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> simp[compile_tuple_load_all_def, compiler_label_hoare_typed_primitives] >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_load_memory, compiler_label_hoare_typed_primitives] >>
       gen_tac >> BETA_TAC) >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_reason_message:
  supported_pure_expr tops e /\ ~expr_has_internal_call e ==>
  compiler_block_tail (compile_reason_message ce e)
Proof
  strip_tac >>
  `!ty. compiler_block_tail (compile_expr ce ty e)` by
    metis_tac[compiler_block_tail_supported_expr] >>
  Cases_on `e` >> simp[compile_reason_message_def] >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> simp[compile_reason_message_def] >>
  rename1 `Literal (BaseT bt) lit` >> Cases_on `bt` >> simp[compile_reason_message_def] >>
  Cases_on `lit` >> simp[compile_reason_message_def] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_bytelike_literal, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_reason_message:
  supported_pure_expr tops e /\ ~expr_has_internal_call e ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_reason_message ce e)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `!ty. compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_expr ce ty e) (\r out. compiler_label_reservation origin pending out)` by
    metis_tac[compiler_label_hoare_supported_expr] >>
  Cases_on `e` >> simp[compile_reason_message_def] >>
  rename1 `Literal ty lit` >> Cases_on `ty` >> simp[compile_reason_message_def] >>
  rename1 `Literal (BaseT bt) lit` >> Cases_on `bt` >> simp[compile_reason_message_def] >>
  Cases_on `lit` >> simp[compile_reason_message_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_bytelike_literal, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_store_at_loc:
  compiler_block_tail (compile_store_at_loc imm dst value loc)
Proof
  Cases_on `loc` >> simp[compile_store_at_loc_def, compiler_block_tail_primitives] >>
  rename1 `SOME location` >> Cases_on `location` >>
  simp[compile_store_at_loc_def, compiler_block_tail_primitives,
    compiler_block_tail_immutable_primitives]
QED

Theorem compiler_label_hoare_store_at_loc:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_store_at_loc imm dst value loc)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `loc` >> simp[compile_store_at_loc_def, compiler_label_hoare_typed_primitives] >>
  rename1 `SOME location` >> Cases_on `location` >>
  simp[compile_store_at_loc_def, compiler_label_hoare_typed_primitives,
    compiler_label_hoare_immutable_primitives]
QED
