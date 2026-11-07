Theory bodyPtrStructLitOwnershipGuarded
Ancestors
  bodyPtrStructLitOwnershipDispatch bodyPtrStructLitOwnershipLock bodyPtrStructLitOwnershipBodyRun
  bodyPtrStructLitOwnershipModuleRegistration bodyPtrStructLitOwnershipStmtHelpers
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipLoops
  loweringShapeProps loweringShapeDefs supportedStmtTraverse moduleLowering
  compileEnv context

Theorem alloc_run_guarded_exit:
  alloc_run fresh_outputs
    (do cs <- comp_get;
        if block_is_terminated cs then return ()
        else do (if nr then compile_nonreentrant_unlock key tr view else return ());
                (case rt of SOME _ => emit_inst INVALID [] []
                          | NONE => emit_inst STOP [] []) od od)
    (\u s. fresh_outputs s)
Proof
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
  reverse conj_tac
  >- simp[alloc_run_def, comp_get_def, alloc_frame_refl] >>
  gen_tac >> Cases_on `block_is_terminated v` >> simp[]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_nonreentrant_unlock] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> Cases_on `rt` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_compile_guarded_body:
  !ce nr key tr view body rt.
  ce.ce_alloca_locals /\ ~supported_stmts_expr_exists expr_shape_root body ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_guarded_body ce nr key tr view body rt)
    (\u s. fresh_outputs s)
Proof
  rpt strip_tac >> simp[compile_guarded_body_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (Cases_on `nr`
      >- (simp[] >> irule alloc_run_conseq >>
          irule_at Any alloc_run_nonreentrant_lock_frame >>
          qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_compile_stmts_shape_fresh >>
      simp[loop_ctx_shape_ok_def]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_guarded_exit) >> simp[]
QED

Theorem alloc_run_compile_external_function_body:
  !ce args nr key tr view body rt.
  ce.ce_alloca_locals /\ ~supported_stmts_expr_exists expr_shape_root body ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_external_function_body ce args nr key tr view body rt)
    (\u s. fresh_outputs s)
Proof
  rpt strip_tac >> simp[compile_external_function_body_def] >>
  irule alloc_run_bind >>
  irule_at Any alloc_run_compile_register_positional_args_shape >>
  gen_tac >> simp[alloc_run_def] >> rpt strip_tac >>
  `v.ce_alloca_locals` by gvs[] >>
  drule_all alloc_run_compile_guarded_body >>
  simp[alloc_run_def] >> disch_then drule_all >> simp[]
QED

Theorem alloc_run_payable_check:
  alloc_run fresh_outputs (compile_entry_checks 4 payable)
    (\u s. fresh_outputs s)
Proof
  irule alloc_run_compile_entry_checks_fresh
QED

Theorem payable_check_eq:
  compile_entry_checks 4 payable =
    (if ~payable then
       do cv <- emit_op CALLVALUE []; nv <- emit_op ISZERO [cv];
          emit_void ASSERT [nv] od
     else comp_return ())
Proof
  simp[compile_entry_checks_def, FUN_EQ_THM, comp_ignore_bind_def,
       comp_bind_def, comp_return_def] >> gen_tac >>
  pairarg_tac >> simp[]
QED

Theorem alloc_run_payable_check_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s) (compile_entry_checks 4 payable)
    (\u s. shape_state s /\ R s /\ fresh_outputs s)
Proof
  strip_tac >> irule alloc_run_compile_entry_checks_frame >> simp[]
QED

Theorem alloc_run_compile_fallback_body:
  !ce pay nr key tr view body rt.
  ce.ce_alloca_locals /\ ~supported_stmts_expr_exists expr_shape_root body ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_fallback_body ce pay nr key tr view body rt)
    (\u s. fresh_outputs s)
Proof
  rpt strip_tac >> simp[compile_fallback_body_def] >>
  once_rewrite_tac[GSYM payable_check_eq] >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_payable_check_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_compile_guarded_body >> simp[]
QED
