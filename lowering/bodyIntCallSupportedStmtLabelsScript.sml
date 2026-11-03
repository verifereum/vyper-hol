(* Structural closure of the internal statement compiler label contracts. *)
Theory bodyIntCallSupportedStmtLabels
Ancestors
  bodyIntCallStmtControlLabels bodyIntCallStmtHelperLabels supportedStmtTraverse
  supportedStmts stmtLowering bodyIntCallLabelFrame bodyIntCallLabelReservations
  bodyIntCallContextLabels compileEnv emitHelper bodyIntCallSupportedExprLabels
  bodyIntCallExprLabels supportedExprs

Theorem compiler_block_tail_supported_stmt_mutual:
  (!tops bindings s ce lc ty rpc sz.
    supported_stmt tops bindings s /\
    ~supported_stmt_expr_exists expr_internal_call_root s /\
    ce.ce_return_pc = SOME (PtrVar rpc sz) ==>
    compiler_block_tail (compile_stmt ce lc ty s)) /\
  (!tops bindings ss ce lc ty rpc sz.
    supported_stmts tops bindings ss /\
    ~supported_stmts_expr_exists expr_internal_call_root ss /\
    ce.ce_return_pc = SOME (PtrVar rpc sz) ==>
    compiler_block_tail (compile_stmts ce lc ty ss))
Proof
  ho_match_mp_tac supported_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [`compile_stmt ce lc rt (AnnAssign name ty e)`]
  >- metis_tac[compiler_block_tail_stmt_annassign]
  >~ [`compile_stmt ce lc ty Pass`]
  >- simp[compiler_block_tail_stmt_pass]
  >~ [`compile_stmt ce lc ty Break`]
  >- (Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def, compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives])
  >~ [`compile_stmt ce lc ty Continue`]
  >- (Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def, compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives])
  >~ [`compile_stmt ce lc ty (Expr e)`]
  >- metis_tac[compiler_block_tail_stmt_expr]
  >~ [`compile_stmt ce lc ty (Return v)`]
  >- metis_tac[compiler_block_tail_stmt_return]
  >~ [`compile_stmt ce lc ty (Assign target e)`]
  >- (Cases_on `target` >>
      metis_tac[compiler_block_tail_stmt_assign_base, compiler_block_tail_stmt_assign_tuple])
  >~ [`compile_stmt ce lc rt (AugAssign ty target bop e)`]
  >- metis_tac[compiler_block_tail_stmt_augassign]
  >~ [`compile_stmt ce lc ty (Append target e)`]
  >- metis_tac[compiler_block_tail_stmt_append]
  >~ [`compile_stmt ce lc ty (Raise reason)`]
  >- metis_tac[compiler_block_tail_stmt_raise]
  >~ [`compile_stmt ce lc ty (vyperAST$Log id es)`]
  >- metis_tac[compiler_block_tail_stmt_log]
  >~ [`compile_stmt ce lc ty (Assert c reason)`]
  >- metis_tac[compiler_block_tail_stmt_assert]
  >~ [`compile_stmts ce lc ty []`]
  >- (Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def, compiler_block_tail_primitives] >>
      irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives])
  >~ [`compile_stmt ce lc ty (Return (SOME e))`]
  >- metis_tac[compiler_block_tail_stmt_return]
  >> rpt gen_tac >> strip_tac
  >~ [`compile_stmt ce lc ty (If c yes no)`]
  >- (irule compiler_block_tail_stmt_if >>
      gvs[supported_stmt_def, supported_stmt_expr_exists_def] >>
      irule compiler_block_tail_lower_value >>
      metis_tac[compiler_block_tail_supported_expr, supported_expr_def,
                supportedExprTraverseTheory.expr_has_internal_call_def])
  >~ [`compile_stmt ce lc rt (For name ty iter n ss)`]
  >- suspend "loop_tail"
  >> suspend "list_tail"
QED

Resume compiler_block_tail_supported_stmt_mutual[loop_tail]:
  Cases_on `iter`
  >- (irule compiler_block_tail_stmt_array >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> gvs[supported_stmt_def]) >>
      irule compiler_block_tail_supported_expr >>
      metis_tac[supported_iterator_array_expr, supported_expr_def, supported_stmt_def])
  >> irule compiler_block_tail_stmt_range_return_pc >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> gvs[supported_stmt_def])
  >> conj_tac >> irule compiler_block_tail_lower_value >>
  irule compiler_block_tail_supported_expr >>
  metis_tac[supported_iterator_range_exprs, supported_expr_def, supported_stmt_def]
QED

Resume compiler_block_tail_supported_stmt_mutual[list_tail]:
  gvs[supported_stmt_def, supported_stmt_expr_exists_def] >>
  rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac compiler_block_tail_termination_read >> gen_tac >>
  IF_CASES_TAC >- simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_declare_stmt_local_bind >> gen_tac >> strip_tac >>
  rewrite_tac[comp_ignore_bind_def] >> BETA_TAC >>
  irule compiler_block_tail_bind >> conj_tac >> rpt gen_tac >> BETA_TAC >>
  first_x_assum irule >> metis_tac[]
QED

Finalise compiler_block_tail_supported_stmt_mutual


Theorem compiler_label_hoare_supported_stmt_mutual:
  (!tops bindings s ce lc ty rpc sz origin pending.
    supported_stmt tops bindings s /\
    ~supported_stmt_expr_exists expr_internal_call_root s /\
    ce.ce_return_pc = SOME (PtrVar rpc sz) ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_stmt ce lc ty s) (\r out. compiler_label_reservation origin pending out)) /\
  (!tops bindings ss ce lc ty rpc sz origin pending.
    supported_stmts tops bindings ss /\
    ~supported_stmts_expr_exists expr_internal_call_root ss /\
    ce.ce_return_pc = SOME (PtrVar rpc sz) ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_stmts ce lc ty ss) (\r out. compiler_label_reservation origin pending out))
Proof
  ho_match_mp_tac supported_stmt_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [`compile_stmt ce lc ty Pass`]
  >- simp[compiler_label_hoare_stmt_pass]
  >~ [`compile_stmt ce lc ty Break`]
  >- (Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def,
        compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives])
  >~ [`compile_stmt ce lc ty Continue`]
  >- (Cases_on `lc` >> simp[compile_stmt_def, comp_ignore_bind_def,
        compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives])
  >~ [`compile_stmt ce lc ty (Expr e)`]
  >- metis_tac[compiler_label_hoare_stmt_expr]
  >~ [`compile_stmt ce lc ty (Return NONE)`]
  >- metis_tac[compiler_label_hoare_stmt_return]
  >~ [`compile_stmt ce lc ty (Return (SOME e))`]
  >- metis_tac[compiler_label_hoare_stmt_return]
  >~ [`compile_stmt ce lc rt (AnnAssign name ty e)`]
  >- metis_tac[compiler_label_hoare_stmt_annassign]
  >~ [`compile_stmt ce lc ty (Assign target e)`]
  >- (Cases_on `target` >>
      metis_tac[compiler_label_hoare_stmt_assign_base, compiler_label_hoare_stmt_assign_tuple])
  >~ [`compile_stmt ce lc rt (AugAssign ty target bop e)`]
  >- metis_tac[compiler_label_hoare_stmt_augassign]
  >~ [`compile_stmt ce lc ty (Append target e)`]
  >- metis_tac[compiler_label_hoare_stmt_append]
  >~ [`compile_stmt ce lc ty (Raise reason)`]
  >- metis_tac[compiler_label_hoare_stmt_raise]
  >~ [`compile_stmt ce lc ty (vyperAST$Log id es)`]
  >- metis_tac[compiler_label_hoare_stmt_log]
  >~ [`compile_stmt ce lc ty (Assert c reason)`]
  >- metis_tac[compiler_label_hoare_stmt_assert]
  >~ [`compile_stmts ce lc ty []`]
  >- simp[compile_stmt_def, compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
  >> rpt gen_tac >> strip_tac
  >~ [`compile_stmt ce lc ty (If c yes no)`] >- suspend "if_reservation"
  >~ [`compile_stmt ce lc rt (For name ty iter n ss)`] >- suspend "loop_reservation"
  >> suspend "list_reservation"
QED

Resume compiler_label_hoare_supported_stmt_mutual[if_reservation]:
  irule compiler_label_hoare_stmt_if >>
  gvs[supported_stmt_def, supported_stmt_expr_exists_def] >>
  rpt gen_tac >> irule compiler_label_hoare_lower_value >>
  metis_tac[compiler_label_hoare_supported_expr, supported_expr_def,
            supportedExprTraverseTheory.expr_has_internal_call_def]
QED

Resume compiler_label_hoare_supported_stmt_mutual[loop_reservation]:
  Cases_on `iter`
  >- (irule compiler_label_hoare_stmt_array >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> gvs[supported_stmt_def]) >>
      rpt gen_tac >> irule compiler_label_hoare_supported_expr >>
      metis_tac[supported_iterator_array_expr, supported_expr_def, supported_stmt_def])
  >> irule compiler_label_hoare_stmt_range >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> gvs[supported_stmt_def])
  >> conj_tac >> rpt gen_tac >> irule compiler_label_hoare_lower_value >>
  irule compiler_label_hoare_supported_expr >>
  metis_tac[supported_iterator_range_exprs, supported_expr_def, supported_stmt_def]
QED

Resume compiler_label_hoare_supported_stmt_mutual[list_reservation]:
  gvs[supported_stmt_def, supported_stmt_expr_exists_def] >>
  rewrite_tac[compile_stmt_def] >>
  ho_match_mp_tac compiler_label_hoare_termination_read >> gen_tac >>
  IF_CASES_TAC >- simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives] >>
  irule compiler_label_hoare_bind >>
  qexists_tac `\bce out. bce.ce_return_pc = ce.ce_return_pc /\
    compiler_label_reservation origin pending out` >>
  simp[compiler_label_hoare_declare_stmt_local_result] >>
  gen_tac >> irule compiler_label_hoare_pure_pre >> strip_tac >> BETA_TAC >>
  rewrite_tac[comp_ignore_bind_def] >>
  irule compiler_label_hoare_preserving_bind >> conj_tac >> rpt gen_tac >> BETA_TAC >>
  first_x_assum irule >> metis_tac[]
QED

Finalise compiler_label_hoare_supported_stmt_mutual


Theorem compiler_block_tail_supported_stmt:
  supported_stmt tops bindings s /\
  ~supported_stmt_expr_exists expr_internal_call_root s /\
  (?rpc sz. ce.ce_return_pc = SOME (PtrVar rpc sz)) ==>
  compiler_block_tail (compile_stmt ce lc ty s)
Proof
  metis_tac[compiler_block_tail_supported_stmt_mutual]
QED

Theorem compiler_block_tail_supported_stmts:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  (?rpc sz. ce.ce_return_pc = SOME (PtrVar rpc sz)) ==>
  compiler_block_tail (compile_stmts ce lc ty ss)
Proof
  metis_tac[compiler_block_tail_supported_stmt_mutual]
QED

Theorem compiler_label_hoare_supported_stmt:
  supported_stmt tops bindings s /\
  ~supported_stmt_expr_exists expr_internal_call_root s /\
  (?rpc sz. ce.ce_return_pc = SOME (PtrVar rpc sz)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmt ce lc ty s) (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[compiler_label_hoare_supported_stmt_mutual]
QED

Theorem compiler_label_hoare_supported_stmts:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  (?rpc sz. ce.ce_return_pc = SOME (PtrVar rpc sz)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_stmts ce lc ty ss) (\r out. compiler_label_reservation origin pending out)
Proof
  metis_tac[compiler_label_hoare_supported_stmt_mutual]
QED

Theorem compile_supported_stmt_label_bounds:
  supported_stmt tops bindings s /\
  ~supported_stmt_expr_exists expr_internal_call_root s /\
  (?rpc sz. ce.ce_return_pc = SOME (PtrVar rpc sz)) ==>
  !st r out. compile_stmt ce lc ty s st = (r,out) /\ compile_state_ok st ==>
    compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
    bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >> simp[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] compiler_label_hoare_supported_stmt) >> metis_tac[]
QED

Theorem compile_supported_stmts_label_bounds:
  supported_stmts tops bindings ss /\
  ~supported_stmts_expr_exists expr_internal_call_root ss /\
  (?rpc sz. ce.ce_return_pc = SOME (PtrVar rpc sz)) ==>
  !st r out. compile_stmts ce lc ty ss st = (r,out) /\ compile_state_ok st ==>
    compile_state_ok out /\ st.cs_next_label <= out.cs_next_label /\
    bound_labels out SUBSET (bound_labels st UNION compiler_labels_future st.cs_next_label)
Proof
  strip_tac >> ho_match_mp_tac compiler_label_hoare_label_bounds >> gen_tac >> simp[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] compiler_label_hoare_supported_stmts) >> metis_tac[]
QED
