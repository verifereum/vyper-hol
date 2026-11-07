Theory bodyPtrStructLitOwnershipRecursion
Ancestors bodyPtrStructLitOwnershipBodyClosure bodyPtrStructLitOwnershipBuiltinBody
  bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipCallbacks
  exprLowering supportedExprTraverse loweringShapeDefs loweringShapeProps
  exprCallBounds vyperAST list bodyPtrStructLitOwnershipRestrictions

Theorem alloc_run_compile_expr_bounded:
  !n. (!ce ty e. expr_size e <= n /\ ~supported_expr_exists expr_shape_root e ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_expr ce ty e) (\v s. T)) /\
  (!ce rt ty bi args. list_size expr_size args <= n /\ builtin_arity bi <= LENGTH args /\
    ~supported_exprs_exists expr_shape_root args ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_builtin_dispatch ce rt ty bi args) (\v s. T)) /\
  (!ce vt ty tb rt args. list_size expr_size args <= n /\ type_builtin_arity tb <= LENGTH args /\
    ~supported_exprs_exists expr_shape_root args ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_type_builtin_dispatch ce vt ty tb rt args) (\v s. T))
Proof
  completeInduct_on `n` >> rpt conj_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume alloc_run_compile_expr_bounded[expr]:
  rpt gen_tac >> strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  once_rewrite_tac [compile_expr_raw_def] >> simp[SF ETA_ss] >>
  irule alloc_run_compile_expr_body_closed >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (irule ownership_expr_child_shape >> simp[]) >>
      irule alloc_run_expr_child_callback_owned >> strip_tac >>
      first_x_assum (qspec_then `expr_size child` mp_tac) >> simp[] >>
      disch_then (fn th => mp_tac (cj 1 th)) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      irule alloc_run_builtin_child_callback_owned >> strip_tac >>
      first_x_assum (qspec_then `list_size expr_size args` mp_tac) >> simp[] >>
      disch_then (fn th => mp_tac (cj 2 th)) >>
      gvs[supported_expr_exists_def, expr_shape_root_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  irule alloc_run_type_child_callback_owned >> strip_tac >>
  first_x_assum (qspec_then `list_size expr_size args` mp_tac) >> simp[] >>
  disch_then (fn th => mp_tac (cj 3 th)) >>
  gvs[supported_expr_exists_def, expr_shape_root_def]
QED

Resume alloc_run_compile_expr_bounded[builtin]:
  rpt gen_tac >> strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  once_rewrite_tac [compile_expr_raw_def] >> simp[SF ETA_ss] >>
  irule alloc_run_compile_builtin_dispatch_body_cases >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `~supported_expr_exists expr_shape_root e` by
        metis_tac[ownership_exclusion_member] >> conj_tac
      >- (irule ownership_expr_child_shape >> simp[]) >>
      irule alloc_run_expr_child_callback_owned >> strip_tac >>
      first_x_assum (qspec_then `expr_size e` mp_tac) >> simp[] >>
      disch_then (fn th => mp_tac (cj 1 th)) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `~supported_expr_exists expr_shape_root e` by
        metis_tac[ownership_exclusion_array_member] >> conj_tac
      >- (irule ownership_expr_child_shape >> simp[]) >>
      irule alloc_run_expr_child_callback_owned >> strip_tac >>
      first_x_assum (qspec_then `expr_size e` mp_tac) >> simp[] >>
      disch_then (fn th => mp_tac (cj 1 th)) >> simp[]) >>
  strip_tac >>
  `MEM (HD args) args` by (Cases_on `args` >> gvs[]) >>
  `~supported_expr_exists expr_shape_root (extcode_addr_expr (HD args))` by
    metis_tac[ownership_exclusion_member, ownership_exclusion_extcode_addr] >>
  conj_tac
  >- (irule ownership_expr_child_shape >> simp[]) >>
  irule alloc_run_expr_child_callback_owned >> strip_tac >>
  first_x_assum (qspec_then `expr_size (extcode_addr_expr (HD args))` mp_tac) >>
  simp[] >> disch_then (fn th => mp_tac (cj 1 th)) >> simp[]
QED

Resume alloc_run_compile_expr_bounded[type_builtin]:
  rpt gen_tac >> strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  once_rewrite_tac [compile_expr_raw_def] >> simp[SF ETA_ss] >>
  irule alloc_run_compile_type_builtin_dispatch_body_cases >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `~supported_expr_exists expr_shape_root e` by
    metis_tac[ownership_exclusion_member] >> conj_tac
  >- (irule ownership_expr_child_shape >> simp[]) >>
  irule alloc_run_expr_child_callback_owned >> strip_tac >>
  first_x_assum (qspec_then `expr_size e` mp_tac) >> simp[] >>
  disch_then (fn th => mp_tac (cj 1 th)) >> simp[]
QED

Finalise alloc_run_compile_expr_bounded

Theorem alloc_run_compile_expr:
  ~supported_expr_exists expr_shape_root e ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr ce ty e) (\v s. T)
Proof
  strip_tac >> qspec_then `expr_size e` (mp_tac o cj 1) alloc_run_compile_expr_bounded >>
  simp[]
QED

Theorem alloc_run_compile_builtin_dispatch:
  builtin_arity bi <= LENGTH args /\
  ~supported_exprs_exists expr_shape_root args ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch ce rt ty bi args) (\v s. T)
Proof
  strip_tac >>
  qspec_then `list_size expr_size args` (mp_tac o cj 2) alloc_run_compile_expr_bounded >>
  simp[]
QED

Theorem alloc_run_compile_type_builtin_dispatch:
  type_builtin_arity tb <= LENGTH args /\
  ~supported_exprs_exists expr_shape_root args ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_type_builtin_dispatch ce vt ty tb rt args) (\v s. T)
Proof
  strip_tac >>
  qspec_then `list_size expr_size args` (mp_tac o cj 3) alloc_run_compile_expr_bounded >>
  simp[]
QED
