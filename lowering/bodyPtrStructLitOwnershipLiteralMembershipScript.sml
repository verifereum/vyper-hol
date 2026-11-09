Theory bodyPtrStructLitOwnershipLiteralMembership
Ancestors bodyPtrStructLitOwnershipMultiExprs bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  exprLowering compileEnv context loweringShapeDefs

Theorem alloc_run_compile_list_membership_in:
  !elems. alloc_run fresh_outputs (compile_list_membership_in needle elems)
    (\v s. fresh_outputs s)
Proof
  Induct >> simp[compile_list_membership_in_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  Cases_on `elems` >> simp[compile_list_membership_in_def, alloc_run_emit_op_fresh] >>
  gen_tac >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- gvs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  gvs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_list_membership_notin:
  !elems. alloc_run fresh_outputs (compile_list_membership_notin needle elems)
    (\v s. fresh_outputs s)
Proof
  Induct >> simp[compile_list_membership_notin_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  Cases_on `elems` >> simp[compile_list_membership_notin_def] >> gen_tac >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- gvs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  gvs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_builtin_dispatch_body_literal_membership:
  (op = In \/ op = NotIn) /\ is_ArrayT (expr_type (HD (TL args))) /\
  HD (TL args) = Builtin av (MakeArray a b) elems /\
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce (expr_type (HD args)) (HD args)) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce (expr_type (HD args)) (HD args)) (\v s. T) /\
  (!e. MEM e elems ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce ret_ty ty (Bop op) args) (\v s. T)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_ArrayT (expr_type (Builtin av (MakeArray a b) elems))` by metis_tac[] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `needle` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_multi_exprs_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `elem_ops` >> simp[] >> suspend "terminal"
QED

Resume alloc_run_compile_builtin_dispatch_body_literal_membership[terminal]:
  mp_tac (Q.SPEC `elem_ops` alloc_run_compile_list_membership_in) >>
  mp_tac (Q.SPEC `elem_ops` alloc_run_compile_list_membership_notin) >>
  Cases_on `op = In` >> simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> rename1 `shape_state start` >>
  `fresh_outputs start` by
    (qpat_x_assum `shape_state start` mp_tac >>
     simp[shape_state_def, shape_base_fresh_outputs]) >>
  first_x_assum drule_all >> simp[]
QED

Finalise alloc_run_compile_builtin_dispatch_body_literal_membership
