(* Expression closure and compiler interfaces for internal statement bodies. *)
Theory bodyIntCallStmtHelperLabels
Ancestors
  bodyIntCallSupportedExprLabels bodyIntCallMaterialLabels
  stmtLowering moduleLowering supportedStmts supportedStmtTraverse compileEnv supportedExprs list supportedTargets
  bodyIntCallLabelFrame bodyIntCallLabelReservations bodyIntCallContextLabels
  emitHelper bodyIntCallExprLabels bodyIntCallExprBodyLabels exprLowering
  bodyIntCallAbiLabels

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

Theorem compiler_label_hoare_declare_local_result:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (declare_local ce id ty)
    (\bce out. bce.ce_return_pc = ce.ce_return_pc /\
      compiler_label_reservation origin pending out)
Proof
  ho_match_mp_tac compiler_label_hoare_result >>
  simp[compiler_label_hoare_declare_local] >>
  metis_tac[declare_local_return_pc]
QED

Theorem compiler_label_hoare_declare_local_bind:
  (!bce. bce.ce_return_pc = ce.ce_return_pc ==>
    compiler_label_hoare (compiler_label_reservation origin pending) (k bce) R) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (comp_bind (declare_local ce id ty) k) R
Proof
  strip_tac >> irule compiler_label_hoare_bind >>
  qexists_tac `\bce out. bce.ce_return_pc = ce.ce_return_pc /\
    compiler_label_reservation origin pending out` >>
  simp[compiler_label_hoare_declare_local_result] >> gen_tac >>
  irule compiler_label_hoare_pure_pre >> simp[]
QED

Theorem compiler_block_tail_declare_local_bind:
  (!bce. bce.ce_return_pc = ce.ce_return_pc ==> compiler_block_tail (k bce)) ==>
  compiler_block_tail (comp_bind (declare_local ce id ty) k)
Proof
  strip_tac >> irule compiler_block_tail_bind_result >>
  reverse conj_tac >- simp[compiler_block_tail_declare_local] >>
  qexists_tac `\bce. bce.ce_return_pc = ce.ce_return_pc` >>
  simp[compiler_block_tail_declare_local] >> metis_tac[declare_local_return_pc]
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

Theorem compiler_label_hoare_declare_stmt_local_result:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (declare_stmt_local ce s)
    (\bce out. bce.ce_return_pc = ce.ce_return_pc /\
      compiler_label_reservation origin pending out)
Proof
  ho_match_mp_tac compiler_label_hoare_result >>
  simp[compiler_label_hoare_declare_stmt_local] >>
  metis_tac[declare_stmt_local_return_pc]
QED

Theorem compiler_block_tail_declare_stmt_local_bind:
  (!bce. bce.ce_return_pc = ce.ce_return_pc ==> compiler_block_tail (k bce)) ==>
  compiler_block_tail (comp_bind (declare_stmt_local ce s) k)
Proof
  strip_tac >> irule compiler_block_tail_bind_result >>
  reverse conj_tac >- simp[compiler_block_tail_declare_stmt_local] >>
  qexists_tac `\bce. bce.ce_return_pc = ce.ce_return_pc` >>
  simp[compiler_block_tail_declare_stmt_local] >>
  metis_tac[declare_stmt_local_return_pc]
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


Theorem compiler_block_tail_assign_normalize:
  compiler_block_tail
    (if b then comp_bind (compile_alloc_buffer sz) (\a.
       comp_ignore_bind (compile_store_memory_typed ce a.buf_operand ty value sty)
         (comp_return a.buf_operand)) else comp_return value)
Proof
  Cases_on `b` >> simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_alloc_buffer] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_ignore_bind >>
  simp[compiler_block_tail_typed_copy, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_assign_normalize:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (if b then comp_bind (compile_alloc_buffer sz) (\a.
       comp_ignore_bind (compile_store_memory_typed ce a.buf_operand ty value sty)
         (comp_return a.buf_operand)) else comp_return value)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `b` >> simp[compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_alloc_buffer] >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_preserves_reservation >>
      metis_tac[compile_store_memory_typed_label_bounds]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_assign_memory:
  compiler_block_tail (compile_assign_value ce dst LocMemory value prim src_loc ty sty da sz)
Proof
  Cases_on `prim` >> simp[compile_assign_value_def, compiler_block_tail_primitives] >>
  Cases_on `src_loc = SOME LocMemory` >>
  simp[compiler_block_tail_store_memory, LET_THM] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_alloc_buffer] >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_copy_memory, compiler_block_tail_store_memory]
QED

Theorem compiler_label_hoare_assign_memory:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_assign_value ce dst LocMemory value prim src_loc ty sty da sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  `!src dst ty sty. compiler_label_hoare (compiler_label_reservation origin pending)
     (compile_store_memory ce src dst ty sty)
     (\r out. compiler_label_reservation origin pending out)` by
    (rpt gen_tac >> irule compiler_label_hoare_preserves_reservation >>
     metis_tac[compile_store_memory_label_bounds]) >>
  Cases_on `prim` >> simp[compile_assign_value_def, compiler_label_hoare_typed_primitives] >>
  Cases_on `src_loc = SOME LocMemory` >> simp[LET_THM] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_alloc_buffer] >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_typed_primitives] >>
  gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_preserves_reservation >>
      metis_tac[compile_copy_memory_label_bounds]) >> simp[]
QED

Theorem compiler_block_tail_assign_storage:
  compiler_block_tail (compile_assign_value ce dst LocStorage value prim src_loc ty sty da sz)
Proof
  simp[Once compile_assign_value_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- MATCH_ACCEPT_TAC compiler_block_tail_assign_normalize >>
  gen_tac >> BETA_TAC >> Cases_on `prim` >> simp[compiler_block_tail_primitives] >>
  Cases_on `da` >> simp[compiler_block_tail_dynarray_to_storage] 
  >- (Cases_on `sz <= 32` >> simp[] >> rewrite_tac[comp_ignore_bind_def] >>
      irule compiler_block_tail_bind >>
      simp[compiler_block_tail_primitives, compiler_block_tail_storage_transfers]) >>
  split_pair_case_tac >> simp[compiler_block_tail_dynarray_to_storage]
QED

Theorem compiler_label_hoare_assign_storage:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_assign_value ce dst LocStorage value prim src_loc ty sty da sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[Once compile_assign_value_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- MATCH_ACCEPT_TAC compiler_label_hoare_assign_normalize >>
  gen_tac >> BETA_TAC >> Cases_on `prim` >> simp[compiler_label_hoare_typed_primitives] >>
  Cases_on `da`
  >- (simp[] >> Cases_on `sz <= 32` >> simp[] >> rewrite_tac[comp_ignore_bind_def]
      >- (irule compiler_label_hoare_preserving_bind >>
          simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]) >>
      irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- (irule compiler_label_hoare_preserves_reservation >>
          metis_tac[compile_memory_to_storage_label_bounds]) >>
      simp[compiler_label_hoare_typed_primitives]) >>
  simp[] >> split_pair_case_tac >> simp[] >>
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_dynarray_to_storage_label_bounds]
QED

Theorem compiler_block_tail_assign_transient:
  compiler_block_tail (compile_assign_value ce dst LocTransient value prim src_loc ty sty da sz)
Proof
  simp[Once compile_assign_value_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- MATCH_ACCEPT_TAC compiler_block_tail_assign_normalize >>
  gen_tac >> BETA_TAC >> Cases_on `prim` >> simp[compiler_block_tail_primitives] >>
  Cases_on `da` >> simp[compiler_block_tail_dynarray_to_storage]
  >- (Cases_on `sz <= 32` >> simp[] >> rewrite_tac[comp_ignore_bind_def] >>
      irule compiler_block_tail_bind >>
      simp[compiler_block_tail_primitives, compiler_block_tail_storage_transfers]) >>
  split_pair_case_tac >> simp[compiler_block_tail_dynarray_to_storage]
QED

Theorem compiler_label_hoare_assign_transient:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_assign_value ce dst LocTransient value prim src_loc ty sty da sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[Once compile_assign_value_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- MATCH_ACCEPT_TAC compiler_label_hoare_assign_normalize >>
  gen_tac >> BETA_TAC >> Cases_on `prim` >> simp[compiler_label_hoare_typed_primitives] >>
  Cases_on `da`
  >- (simp[] >> Cases_on `sz <= 32` >> simp[] >> rewrite_tac[comp_ignore_bind_def]
      >- (irule compiler_label_hoare_preserving_bind >>
          simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]) >>
      irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- (irule compiler_label_hoare_preserves_reservation >>
          metis_tac[compile_memory_to_transient_label_bounds]) >>
      simp[compiler_label_hoare_typed_primitives]) >>
  simp[] >> split_pair_case_tac >> simp[] >>
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_dynarray_to_storage_label_bounds]
QED

Theorem compiler_block_tail_assign_code:
  compiler_block_tail (compile_assign_value ce dst LocCode value prim src_loc ty sty da sz)
Proof
  simp[Once compile_assign_value_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- MATCH_ACCEPT_TAC compiler_block_tail_assign_normalize >>
  gen_tac >> BETA_TAC >> Cases_on `prim` >>
  simp[compiler_block_tail_immutable_primitives] >>
  Cases_on `sz <= 32` >> simp[compiler_block_tail_immutable_primitives,
    compiler_block_tail_imm_store_words] >>
  irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, compiler_block_tail_immutable_primitives]
QED

Theorem compiler_label_hoare_assign_code:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_assign_value ce dst LocCode value prim src_loc ty sty da sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[Once compile_assign_value_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- MATCH_ACCEPT_TAC compiler_label_hoare_assign_normalize >>
  gen_tac >> BETA_TAC >> Cases_on `prim` >>
  simp[compiler_label_hoare_immutable_primitives] >>
  Cases_on `sz <= 32` >> simp[]
  >- (irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_immutable_primitives]) >>
  irule compiler_label_hoare_preserves_reservation >>
  metis_tac[compile_imm_store_words_label_bounds]
QED

Theorem compiler_block_tail_assign_value:
  compiler_block_tail (compile_assign_value ce dst loc value prim src_loc ty sty da sz)
Proof
  Cases_on `loc` >> simp[compiler_block_tail_assign_memory,
    compiler_block_tail_assign_storage, compiler_block_tail_assign_transient,
    compiler_block_tail_assign_code] >>
  simp[compile_assign_value_def, comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_assign_value:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_assign_value ce dst loc value prim src_loc ty sty da sz)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `loc` >> simp[compiler_label_hoare_assign_memory,
    compiler_label_hoare_assign_storage, compiler_label_hoare_assign_transient,
    compiler_label_hoare_assign_code] >>
  simp[compile_assign_value_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_target_name:
  compiler_block_tail (compile_get_target_ptr ce (NameTarget id))
Proof
  simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_block_tail_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_target_top:
  compiler_block_tail (compile_get_target_ptr ce (TopLevelNameTarget nsid))
Proof
  simp[compile_get_target_ptr_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[compiler_block_tail_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_target_attribute:
  compiler_block_tail (compile_get_target_ptr ce bt) ==>
  compiler_block_tail (compile_get_target_ptr ce (AttributeTarget bt fname))
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_target_subscript:
  compiler_block_tail (compile_get_target_ptr ce bt) /\
  compiler_block_tail (lower_value compile_expr ce (expr_type e) e) ==>
  compiler_block_tail (compile_get_target_ptr ce (SubscriptTarget bt e))
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  rename1 `SND (SND result)` >> Cases_on `SND (SND result)` >> simp[]
  >- suspend "array" >>
  rename1 `SND (SND result) = SOME place` >> Cases_on `place` >> simp[]
  >- suspend "map" >> suspend "array_value"
QED

Resume compiler_block_tail_target_subscript[array]:
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_array_subscript >> simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Resume compiler_block_tail_target_subscript[map]:
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_block_tail_mapping_helpers, compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_mapping_helpers, compiler_block_tail_primitives]
QED

Resume compiler_block_tail_target_subscript[array_value]:
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_array_subscript >> simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Finalise compiler_block_tail_target_subscript

Theorem compiler_label_hoare_target_name:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (NameTarget id))
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_target_top:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (TopLevelNameTarget nsid))
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_get_target_ptr_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_target_attribute:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt) (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (AttributeTarget bt fname))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_target_subscript:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (lower_value compile_expr ce (expr_type e) e)
    (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (SubscriptTarget bt e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  rename1 `SND (SND result)` >> Cases_on `SND (SND result)` >> simp[]
  >- suspend "array" >>
  rename1 `SND (SND result) = SOME place` >> Cases_on `place` >> simp[]
  >- suspend "map" >> suspend "array_value"
QED

Resume compiler_label_hoare_target_subscript[array]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_array_subscript >> simp[compiler_label_hoare_context_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Resume compiler_label_hoare_target_subscript[map]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_label_hoare_mapping_helpers, compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_mapping_helpers, compiler_label_hoare_typed_primitives]
QED

Resume compiler_label_hoare_target_subscript[array_value]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_array_subscript >> simp[compiler_label_hoare_context_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Finalise compiler_label_hoare_target_subscript

Theorem compiler_block_tail_target_info:
  !target ce pt.
    supportedTargets$supported_target_info tops bindings target = SOME pt /\
    ~supportedExprTraverse$target_has_internal_call target ==>
    compiler_block_tail (compile_get_target_ptr ce target)
Proof
  `((!e:expr. T) /\ (!target. !ce pt.
      supportedTargets$supported_target_info tops bindings target = SOME pt /\
      ~supportedExprTraverse$target_has_internal_call target ==>
      compiler_block_tail (compile_get_target_ptr ce target)))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- simp[compiler_block_tail_target_name]
  >- simp[compiler_block_tail_target_top]
  >- (drule_all supported_target_info_subscript_expr >> strip_tac >>
      irule compiler_block_tail_target_subscript >> reverse conj_tac
      >- (gvs[supportedExprTraverseTheory.target_has_internal_call_def,
              supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]) >>
      irule compiler_block_tail_lower_value >>
      metis_tac[compiler_block_tail_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  drule supported_target_info_attribute_target_base >> strip_tac >>
  irule compiler_block_tail_target_attribute >>
  gvs[supportedExprTraverseTheory.target_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]
QED

Theorem compiler_label_hoare_target_info:
  !target ce pt origin pending.
    supportedTargets$supported_target_info tops bindings target = SOME pt /\
    ~supportedExprTraverse$target_has_internal_call target ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_get_target_ptr ce target)
      (\r out. compiler_label_reservation origin pending out)
Proof
  `((!e:expr. T) /\ (!target. !ce pt origin pending.
      supportedTargets$supported_target_info tops bindings target = SOME pt /\
      ~supportedExprTraverse$target_has_internal_call target ==>
      compiler_label_hoare (compiler_label_reservation origin pending)
        (compile_get_target_ptr ce target)
        (\r out. compiler_label_reservation origin pending out)))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- simp[compiler_label_hoare_target_name]
  >- simp[compiler_label_hoare_target_top]
  >- (drule_all supported_target_info_subscript_expr >> strip_tac >>
      irule compiler_label_hoare_target_subscript >> reverse conj_tac
      >- (gvs[supportedExprTraverseTheory.target_has_internal_call_def,
              supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]) >>
      irule compiler_label_hoare_lower_value >>
      metis_tac[compiler_label_hoare_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  drule supported_target_info_attribute_target_base >> strip_tac >>
  irule compiler_label_hoare_target_attribute >>
  gvs[supportedExprTraverseTheory.target_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]
QED

Theorem compiler_block_tail_supported_target:
  supportedStmts$supported_target tops bindings target /\
  ~supportedExprTraverse$target_has_internal_call target ==>
  compiler_block_tail (compile_get_target_ptr ce target)
Proof
  Cases_on `target` >>
  simp[compiler_block_tail_target_name, compiler_block_tail_target_top] >>
  rename1 `supported_target tops bindings (_ bt _)` >> Cases_on `bt` >>
  simp[supportedStmtsTheory.supported_target_def] >> rpt strip_tac
  >- (irule compiler_block_tail_target_subscript >> reverse conj_tac
      >- simp[compiler_block_tail_target_top] >>
      irule compiler_block_tail_lower_value >>
      gvs[supportedExprTraverseTheory.target_has_internal_call_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          GSYM supportedExprTraverseTheory.expr_has_internal_call_def] >>
      metis_tac[compiler_block_tail_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  irule compiler_block_tail_target_attribute >> simp[compiler_block_tail_target_top]
QED

Theorem compiler_label_hoare_supported_target:
  supportedStmts$supported_target tops bindings target /\
  ~supportedExprTraverse$target_has_internal_call target ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce target)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `target` >>
  simp[compiler_label_hoare_target_name, compiler_label_hoare_target_top] >>
  rename1 `supported_target tops bindings (_ bt _)` >> Cases_on `bt` >>
  simp[supportedStmtsTheory.supported_target_def] >> rpt strip_tac
  >- (irule compiler_label_hoare_target_subscript >> reverse conj_tac
      >- simp[compiler_label_hoare_target_top] >>
      irule compiler_label_hoare_lower_value >>
      gvs[supportedExprTraverseTheory.target_has_internal_call_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          GSYM supportedExprTraverseTheory.expr_has_internal_call_def] >>
      metis_tac[compiler_label_hoare_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  irule compiler_label_hoare_target_attribute >> simp[compiler_label_hoare_target_top]
QED

Theorem tuple_comp_return_bind:
  comp_bind (comp_return x) f = f x
Proof
  simp[comp_bind_def, comp_return_def, FUN_EQ_THM]
QED

Theorem compiler_block_tail_tuple_store_all:
  !tys targets vals.
    (!bt. MEM (BaseTarget bt) targets ==>
      compiler_block_tail (compile_get_target_ptr ce bt)) ==>
    compiler_block_tail (compile_tuple_store_all ce tys targets vals)
Proof
  Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, compiler_block_tail_primitives] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def, LET_THM] >> rpt strip_tac
  >- suspend "base" >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives] >>
  metis_tac[MEM]
QED

Resume compiler_block_tail_tuple_store_all[base]:
  irule compiler_block_tail_bind >> reverse conj_tac >- metis_tac[MEM] >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind, LET_THM] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[compiler_block_tail_store_at_loc, compiler_block_tail_assign_value,
           compiler_block_tail_primitives]) >>
  metis_tac[MEM]
QED

Finalise compiler_block_tail_tuple_store_all

Theorem compiler_label_hoare_tuple_store_all:
  !tys targets vals.
    (!bt. MEM (BaseTarget bt) targets ==>
      compiler_label_hoare (compiler_label_reservation origin pending)
        (compile_get_target_ptr ce bt)
        (\r out. compiler_label_reservation origin pending out)) ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_tuple_store_all ce tys targets vals)
      (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, compiler_label_hoare_typed_primitives] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def, LET_THM] >> rpt strip_tac
  >- suspend "base" >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_typed_primitives] >>
  metis_tac[MEM]
QED

Resume compiler_label_hoare_tuple_store_all[base]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- metis_tac[MEM] >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind, LET_THM] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[compiler_label_hoare_store_at_loc, compiler_label_hoare_assign_value,
           compiler_label_hoare_typed_primitives]) >>
  metis_tac[MEM]
QED

Finalise compiler_label_hoare_tuple_store_all

Theorem compiler_block_tail_tuple_unpack:
  (!bt. MEM (BaseTarget bt) targets ==>
    compiler_block_tail (compile_get_target_ptr ce bt)) ==>
  compiler_block_tail (compile_tuple_unpack ce ty may_stage targets src_op)
Proof
  strip_tac >> simp[compile_tuple_unpack_def, LET_THM] >>
  IF_CASES_TAC >> simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_block_tail_primitives, comp_ignore_bind_def] >>
      irule compiler_block_tail_bind >>
      simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
           tuple_comp_return_bind] >>
      gen_tac >> irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_tuple_load_all, compiler_block_tail_tuple_store_all]
QED

Theorem compiler_label_hoare_tuple_unpack:
  (!bt. MEM (BaseTarget bt) targets ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_get_target_ptr ce bt)
      (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_tuple_unpack ce ty may_stage targets src_op)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_tuple_unpack_def, LET_THM] >>
  IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives,
                        compiler_label_hoare_context_primitives] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives, comp_ignore_bind_def] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_alloc_buffer,
           tuple_comp_return_bind] >>
      gen_tac >> irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_tuple_load_all, compiler_label_hoare_tuple_store_all]
QED

Theorem compiler_block_tail_stmt_pass:
  compiler_block_tail (compile_stmt ce lctx ty Pass)
Proof
  simp[compile_stmt_def, compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_stmt_pass:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty Pass)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_stmt_def, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_stmt_expr:
  supported_stmt tops bindings (Expr e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Expr e) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Expr e))
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, comp_ignore_bind_def] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives] >>
  metis_tac[compiler_block_tail_supported_expr, supported_expr_def]
QED

Theorem compiler_label_hoare_stmt_expr:
  supported_stmt tops bindings (Expr e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Expr e) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Expr e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_typed_primitives] >>
  metis_tac[compiler_label_hoare_supported_expr, supported_expr_def]
QED

Theorem compiler_block_tail_stmt_annassign:
  supported_stmt tops bindings (AnnAssign id vtyp e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (AnnAssign id vtyp e) ==>
  compiler_block_tail (compile_stmt ce lctx ty (AnnAssign id vtyp e))
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, comp_ignore_bind_def, LET_THM] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_emit_local_alloca] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- metis_tac[compiler_block_tail_supported_expr, supported_expr_def] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_block_tail_primitives, compiler_block_tail_unwrap_value]) >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_block_tail_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
  simp[compiler_block_tail_primitives] >> IF_CASES_TAC >>
  simp[compiler_block_tail_primitives, compiler_block_tail_assign_value, LET_THM]
QED

Theorem compiler_label_hoare_stmt_annassign:
  supported_stmt tops bindings (AnnAssign id vtyp e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (AnnAssign id vtyp e) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (AnnAssign id vtyp e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, comp_ignore_bind_def, LET_THM] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_emit_local_alloca] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- metis_tac[compiler_label_hoare_supported_expr, supported_expr_def] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_unwrap_value]) >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >>
  simp[compiler_label_hoare_typed_primitives] >> IF_CASES_TAC >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_assign_value, LET_THM]
QED

Theorem compiler_block_tail_assign_base_target:
  supported_assignment tops bindings (BaseTarget bt) e /\
  ~target_has_internal_call bt ==>
  compiler_block_tail (compile_get_target_ptr ce bt)
Proof
  simp[supported_assignment_def] >> strip_tac
  >- metis_tac[compiler_block_tail_supported_target] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
  metis_tac[compiler_block_tail_target_info]
QED

Theorem compiler_label_hoare_assign_base_target:
  supported_assignment tops bindings (BaseTarget bt) e /\
  ~target_has_internal_call bt ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[supported_assignment_def] >> strip_tac
  >- metis_tac[compiler_label_hoare_supported_target] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
  metis_tac[compiler_label_hoare_target_info]
QED

Theorem compiler_block_tail_stmt_assign_base:
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Assign (BaseTarget bt) e) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Assign (BaseTarget bt) e))
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  `compiler_block_tail (compile_get_target_ptr ce bt)` by
    (irule compiler_block_tail_assign_base_target >>
     gvs[supported_stmt_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supportedExprTraverseTheory.target_has_internal_call_def] >> metis_tac[]) >>
  simp[compile_stmt_def, LET_THM] >> IF_CASES_TAC
  >- (irule compiler_block_tail_bind >> simp[compiler_block_tail_store_at_loc]) >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- metis_tac[compiler_block_tail_supported_expr, supported_expr_def] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  qx_gen_tac `tgt` >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[compiler_block_tail_unwrap_value] >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  Cases_on `FST (SND tgt)` >>
  simp[compiler_block_tail_primitives, compiler_block_tail_assign_value]
QED

Theorem compiler_label_hoare_stmt_assign_base:
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Assign (BaseTarget bt) e) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Assign (BaseTarget bt) e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  `compiler_label_hoare (compiler_label_reservation origin pending)
     (compile_get_target_ptr ce bt) (\r out. compiler_label_reservation origin pending out)` by
    (irule compiler_label_hoare_assign_base_target >>
     gvs[supported_stmt_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supportedExprTraverseTheory.target_has_internal_call_def] >> metis_tac[]) >>
  simp[compile_stmt_def, LET_THM] >> IF_CASES_TAC
  >- (irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_store_at_loc]) >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- metis_tac[compiler_label_hoare_supported_expr, supported_expr_def] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  qx_gen_tac `tgt` >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[compiler_label_hoare_unwrap_value] >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  Cases_on `FST (SND tgt)` >>
  simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_assign_value]
QED

Theorem supported_assignments_exists_member:
  !targets target. MEM target targets /\ supported_assignment_exists p target ==>
    supported_assignments_exists p targets
Proof
  Induct >> simp[supported_assignment_exists_def] >> metis_tac[]
QED

Theorem supported_tuple_assignment_target:
  supported_stmt tops bindings (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Assign (TupleTarget targets) e) /\
  MEM (BaseTarget bt) targets ==>
  supported_target tops bindings bt /\ ~target_has_internal_call bt
Proof
  simp[supported_stmt_def, supported_assignment_def, EVERY_MEM,
       supported_stmt_expr_exists_def, supported_assignment_exists_def,
       supportedExprTraverseTheory.target_has_internal_call_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >>
  metis_tac[supported_assignments_exists_member, supported_assignment_exists_def]
QED

Theorem compiler_block_tail_stmt_assign_tuple:
  supported_stmt tops bindings (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Assign (TupleTarget targets) e) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Assign (TupleTarget targets) e))
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, LET_THM] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- metis_tac[compiler_block_tail_supported_expr, supported_expr_def] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_unwrap_value] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_tuple_unpack >>
  metis_tac[supported_tuple_assignment_target, compiler_block_tail_supported_target]
QED

Theorem compiler_label_hoare_stmt_assign_tuple:
  supported_stmt tops bindings (Assign (TupleTarget targets) e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Assign (TupleTarget targets) e) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Assign (TupleTarget targets) e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, LET_THM] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- metis_tac[compiler_label_hoare_supported_expr, supported_expr_def] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_unwrap_value] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_tuple_unpack >>
  metis_tac[supported_tuple_assignment_target, compiler_label_hoare_supported_target]
QED

Theorem compiler_block_tail_stmt_augassign:
  supported_stmt tops bindings (AugAssign target_ty bt bop e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (AugAssign target_ty bt bop e) ==>
  compiler_block_tail (compile_stmt ce lctx ty (AugAssign target_ty bt bop e))
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  `compiler_block_tail (compile_get_target_ptr ce bt)` by
    (gvs[supported_stmt_def, supported_aug_target_def,
         supported_stmt_expr_exists_def, AllCaseEqs(),
         supportedExprTraverseTheory.target_has_internal_call_def]
     >- metis_tac[compiler_block_tail_supported_target,
          supportedExprTraverseTheory.target_has_internal_call_def] >>
     Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
     rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
     metis_tac[compiler_block_tail_target_info,
       supportedExprTraverseTheory.target_has_internal_call_def]) >>
  simp[compile_stmt_def] >> irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  qx_gen_tac `tgt` >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  Cases_on `FST (SND tgt)` >> simp[compiler_block_tail_primitives] >>
  simp[tuple_comp_return_bind] >> irule compiler_block_tail_bind >> reverse conj_tac
  >- simp[compiler_block_tail_primitives] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_lower_value >>
      metis_tac[compiler_block_tail_supported_expr, supported_expr_def]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_primitives, bodyIntCallBuiltinLabelsTheory.compiler_block_tail_binop]
QED

Theorem compiler_label_hoare_stmt_augassign:
  supported_stmt tops bindings (AugAssign target_ty bt bop e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (AugAssign target_ty bt bop e) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (AugAssign target_ty bt bop e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  `compiler_label_hoare (compiler_label_reservation origin pending)
     (compile_get_target_ptr ce bt) (\r out. compiler_label_reservation origin pending out)` by
    (gvs[supported_stmt_def, supported_aug_target_def,
         supported_stmt_expr_exists_def, AllCaseEqs(),
         supportedExprTraverseTheory.target_has_internal_call_def]
     >- metis_tac[compiler_label_hoare_supported_target,
          supportedExprTraverseTheory.target_has_internal_call_def] >>
     Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
     rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
     metis_tac[compiler_label_hoare_target_info,
       supportedExprTraverseTheory.target_has_internal_call_def]) >>
  simp[compile_stmt_def] >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  qx_gen_tac `tgt` >> BETA_TAC >> simp[tuple_comp_return_bind] >>
  Cases_on `FST (SND tgt)` >> simp[compiler_label_hoare_typed_primitives] >>
  simp[tuple_comp_return_bind] >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_context_primitives] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_lower_value >>
      metis_tac[compiler_label_hoare_supported_expr, supported_expr_def]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_typed_primitives, bodyIntCallBuiltinLabelsTheory.compiler_label_hoare_binop]
QED

Theorem compiler_block_tail_stmt_return:
  supported_stmt tops bindings (Return value) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Return value) /\
  ce.ce_return_pc = SOME (PtrVar rpc sz) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Return value))
Proof
  Cases_on `value` >> rpt strip_tac >> simp[compile_stmt_def, compiler_block_tail_primitives] >>
  rename1 `Return (SOME e)` >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_internal_return_from_env] >>
  irule compiler_block_tail_lower_value >>
  metis_tac[compiler_block_tail_supported_expr, supported_expr_def]
QED

Theorem compiler_label_hoare_stmt_return:
  supported_stmt tops bindings (Return value) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Return value) /\
  ce.ce_return_pc = SOME (PtrVar rpc sz) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Return value))
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `value` >> rpt strip_tac >>
  simp[compile_stmt_def, compiler_label_hoare_context_primitives] >>
  rename1 `Return (SOME e)` >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_internal_return_from_env] >>
  irule compiler_label_hoare_lower_value >>
  metis_tac[compiler_label_hoare_supported_expr, supported_expr_def]
QED

Theorem compiler_block_tail_stmt_raise:
  supported_stmt tops bindings (Raise reason) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Raise reason))
Proof
  Cases_on `reason` >> simp[supported_stmt_def, supported_raise_reason_def,
    compile_stmt_def, compiler_block_tail_primitives, LET_THM] >> strip_tac >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_revert_with_reason] >>
  irule compiler_block_tail_reason_message >>
  metis_tac[supported_string_reason_expr]
QED

Theorem compiler_label_hoare_stmt_raise:
  supported_stmt tops bindings (Raise reason) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Raise reason))
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `reason` >> simp[supported_stmt_def, supported_raise_reason_def,
    compile_stmt_def, compiler_label_hoare_context_primitives, LET_THM] >> strip_tac >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_revert_with_reason] >>
  irule compiler_label_hoare_reason_message >>
  metis_tac[supported_string_reason_expr]
QED

Theorem compiler_block_tail_stmt_log:
  supported_stmt tops bindings (vyperAST$Log event_id args) /\
  ~supported_stmt_expr_exists expr_internal_call_root (vyperAST$Log event_id args) ==>
  compiler_block_tail (compile_stmt ce lctx ty (vyperAST$Log event_id args))
Proof
  rpt strip_tac >>
  `!e. MEM e args ==> supported_pure_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_log_member_expr] >>
  simp[compile_stmt_def, LET_THM] >>
  Cases_on `ce.ce_event_info (nsid_to_string event_id)` >>
  simp[compiler_block_tail_primitives] >>
  PairCases_on `x` >> simp[] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_log_eval_all >>
      qexists_tac `tops` >> simp[EVERY_MEM, supported_expr_def]) >>
  gen_tac >> simp[tuple_comp_return_bind] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_log_topic_ops] >>
  gen_tac >> simp[tuple_comp_return_bind] >> IF_CASES_TAC >>
  simp[compiler_block_tail_primitives, LET_THM] >>
  simp[comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >>
    reverse conj_tac >- simp[compiler_block_tail_alloc_buffer,
      compiler_block_tail_log_store_data, compiler_block_tail_abi_encode_to_buf] >>
    gen_tac >> simp[tuple_comp_return_bind, compiler_block_tail_primitives])
QED

Theorem compiler_label_hoare_stmt_log:
  supported_stmt tops bindings (vyperAST$Log event_id args) /\
  ~supported_stmt_expr_exists expr_internal_call_root (vyperAST$Log event_id args) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (vyperAST$Log event_id args))
    (\r out. compiler_label_reservation origin pending out)
Proof
  rpt strip_tac >>
  `!e. MEM e args ==> supported_pure_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_log_member_expr] >>
  simp[compile_stmt_def, LET_THM] >>
  Cases_on `ce.ce_event_info (nsid_to_string event_id)` >>
  simp[compiler_label_hoare_context_primitives] >>
  PairCases_on `x` >> simp[] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_log_eval_all >>
      qexists_tac `tops` >> simp[EVERY_MEM, supported_expr_def]) >>
  gen_tac >> simp[tuple_comp_return_bind] >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_log_topic_ops] >>
  gen_tac >> simp[tuple_comp_return_bind] >> IF_CASES_TAC >>
  simp[compiler_label_hoare_context_primitives, LET_THM, comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >>
    reverse conj_tac >- simp[compiler_label_hoare_alloc_buffer,
      compiler_label_hoare_log_store_data, compiler_label_hoare_abi_encode_to_buf] >>
    gen_tac >> simp[tuple_comp_return_bind, compiler_label_hoare_context_primitives])
QED

Theorem compiler_block_tail_dynarray_append:
  compiler_block_tail
    (compile_dynarray_append ce base_op val_op ws es dst src cap prim load_opc store_opc)
Proof
  simp[compile_dynarray_append_def, LET_THM, comp_ignore_bind_def] >>
  ntac 6 (irule compiler_block_tail_bind >>
    simp[compiler_block_tail_primitives] >> rpt gen_tac >> BETA_TAC) >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (Cases_on `prim` >> simp[compiler_block_tail_primitives] >>
      IF_CASES_TAC >> simp[compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >>
      simp[compiler_block_tail_store_memory, compiler_block_tail_word_copy_loop,
        compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_dynarray_append:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_dynarray_append ce base_op val_op ws es dst src cap prim load_opc store_opc)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_dynarray_append_def, LET_THM, comp_ignore_bind_def] >>
  ntac 6 (irule compiler_label_hoare_preserving_bind >>
    simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
    rpt gen_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (Cases_on `prim` >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
      IF_CASES_TAC
      >- (irule compiler_label_hoare_preserving_bind >>
          simp[compiler_label_hoare_store_memory] >>
          simp[compiler_label_hoare_def, comp_return_def]) >>
      irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- (irule compiler_label_hoare_preserves_reservation >>
          metis_tac[compile_word_copy_loop_label_bounds]) >>
      simp[compiler_label_hoare_def, comp_return_def]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_block_tail_stmt_append:
  supported_stmt tops bindings (Append target e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Append target e) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Append target e))
Proof
  rpt strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, LET_THM] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_lower_value >>
      metis_tac[compiler_block_tail_supported_expr, supported_expr_def]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_block_tail_primitives, LET_THM, comp_ignore_bind_def] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_alloc_buffer] >>
      gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
      simp[compiler_block_tail_store_memory, compiler_block_tail_primitives]) >>
  gen_tac >> simp[tuple_comp_return_bind, compiler_block_tail_dynarray_append]
QED

Theorem compiler_label_hoare_stmt_append:
  supported_stmt tops bindings (Append target e) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Append target e) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Append target e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  rpt strip_tac >>
  `supported_expr tops e /\ ~expr_has_internal_call e` by
    metis_tac[supported_stmt_rhs_expr] >>
  simp[compile_stmt_def, LET_THM] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_lower_value >>
      metis_tac[compiler_label_hoare_supported_expr, supported_expr_def]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[LET_THM, comp_ignore_bind_def]
      >- simp[compiler_label_hoare_def, comp_return_def] >>
      irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_alloc_buffer] >>
      gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_store_memory] >>
      simp[compiler_label_hoare_def, comp_return_def]) >>
  gen_tac >> simp[tuple_comp_return_bind, compiler_label_hoare_dynarray_append]
QED


Theorem compiler_block_tail_stmt_assert:
  supported_stmt tops bindings (Assert cond reason) ==>
  compiler_block_tail (compile_stmt ce lctx ty (Assert cond reason))
Proof
  strip_tac >>
  `supported_pure_expr tops cond /\ ~expr_has_internal_call cond` by
    metis_tac[supported_stmt_condition_expr] >>
  `compiler_block_tail (lower_value compile_expr ce (BaseT BoolT) cond)` by
    (irule compiler_block_tail_lower_value >>
     metis_tac[compiler_block_tail_supported_expr]) >>
  Cases_on `reason` >>
  simp[compile_stmt_def, LET_THM, tuple_comp_return_bind, comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives] >> gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_reason_message >>
      metis_tac[supported_assert_reason_expr]) >>
  gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_revert_with_reason] >>
  rpt gen_tac >> BETA_TAC >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_label_hoare_stmt_assert:
  supported_stmt tops bindings (Assert cond reason) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lctx ty (Assert cond reason))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >>
  `supported_pure_expr tops cond /\ ~expr_has_internal_call cond` by
    metis_tac[supported_stmt_condition_expr] >>
  `!origin pending. compiler_label_hoare (compiler_label_reservation origin pending)
    (lower_value compile_expr ce (BaseT BoolT) cond)
    (\r out. compiler_label_reservation origin pending out)` by
    (rpt gen_tac >> irule compiler_label_hoare_lower_value >>
     metis_tac[compiler_label_hoare_supported_expr]) >>
  Cases_on `reason` >>
  gvs[supported_stmt_def, supported_assert_reason_def] >>
  simp[compile_stmt_def, LET_THM, tuple_comp_return_bind, comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> simp[] >> gen_tac >> BETA_TAC >>
  ntac 2 (irule compiler_label_hoare_fresh_bind >> gen_tac >> strip_tac >> BETA_TAC) >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives] >> rpt gen_tac >> BETA_TAC >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives] >> rpt gen_tac >> BETA_TAC) >>
  all_tac
  >~ [`compile_reason_message ce e`]
  >- (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
      >- (irule compiler_label_hoare_reason_message >>
          metis_tac[supported_string_reason_expr]) >>
      gen_tac >> BETA_TAC >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_revert_with_reason] >> rpt gen_tac >> BETA_TAC >>
      suspend "reason_exit") >>
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  gvs[compiler_label_hoare_def, comp_return_def, pred_setTheory.DELETE_INSERT] >>
  `pending DELETE lbl' DELETE lbl = pending` by (pred_setLib.ASM_SET_TAC []) >> simp[]
QED

Resume compiler_label_hoare_stmt_assert[reason_exit]:
  irule compiler_label_hoare_new_block_bind >> simp[] >> rpt gen_tac >> BETA_TAC >>
  gvs[compiler_label_hoare_def, comp_return_def, pred_setTheory.DELETE_INSERT] >>
  `pending DELETE lbl' DELETE lbl = pending` by (pred_setLib.ASM_SET_TAC []) >> simp[]
QED

Finalise compiler_label_hoare_stmt_assert

(* External-return probe: aggregate encoding uses the general ABI boundary. *)
Theorem compiler_block_tail_external_return:
  compiler_block_tail
    (compile_external_return rv prim raw info maxsz nr key transient view)
Proof
  Cases_on `rv` >> Cases_on `prim` >> Cases_on `raw` >>
  Cases_on `nr` >> Cases_on `transient` >> Cases_on `view` >>
  simp[compile_external_return_def, contextTheory.compile_nonreentrant_unlock_def,
       comp_ignore_bind_def] >>
  rpt (irule compiler_block_tail_bind >> reverse conj_tac
       >- simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_abi_encode_to_buf] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
               compiler_block_tail_abi_encode_to_buf]
QED

Theorem compiler_label_hoare_external_return:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_external_return rv prim raw info maxsz nr key transient view)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `rv` >> Cases_on `prim` >> Cases_on `raw` >>
  Cases_on `nr` >> Cases_on `transient` >> Cases_on `view` >>
  simp[compile_external_return_def, contextTheory.compile_nonreentrant_unlock_def,
       comp_ignore_bind_def] >>
  rpt (irule compiler_label_hoare_preserving_bind >> reverse conj_tac
       >- simp[compiler_label_hoare_context_primitives,
               compiler_label_hoare_typed_primitives,
               compiler_label_hoare_alloc_buffer,
               compiler_label_hoare_abi_encode_to_buf] >>
       gen_tac >> BETA_TAC) >>
  simp[compiler_label_hoare_context_primitives,
       compiler_label_hoare_typed_primitives, compiler_label_hoare_abi_encode_to_buf]
QED
