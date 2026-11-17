(* Temporary worker: exclude materialized expression constructors. *)
Theory bodyAssignStorageExclusions
Ancestors
  bodySim exprLowering exprReasonOperand compileEnv context vyperAST
  pair finite_map

Theorem body_assign_storage_expr_cases:
  body_inv tops ctx cenv cx /\
  compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  (case e of TopLevelName _ _ => T | Pop _ _ => T |
     Attribute _ _ _ => T | Subscript _ _ _ => T | _ => F)
Proof
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 mp_tac assume_tac)) >>
  Cases_on `e` >> simp[] >>
  pure_once_rewrite_tac [CONJUNCT1 compile_expr_raw_def]
  >~ [`Literal ann lit`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_literal) >>
     gvs[reason_result_shape_def])
  >~ [`IfExp ann cond th el`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_ifexp) >>
     gvs[reason_result_shape_def])
  >~ [`StructLit ann nm fields`] >-
    (disch_then (mp_tac o MATCH_MP reason_compile_structlit) >>
     gvs[reason_result_shape_def])
  >~ [`Call ann dest args dflt`] >-
    (simp[compile_expr_body_def, expr_type_def] >>
     disch_then (mp_tac o MATCH_MP reason_compile_call) >>
     gvs[reason_result_shape_def])
  >~ [`Builtin ann bi args`] >- suspend "builtin"
  >~ [`TypeBuiltin ann tb rt args`] >- suspend "typebuiltin" >>
  simp[compile_expr_body_def, expr_type_def, compile_name_vv_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def, AllCaseEqs()] >>
  rename1 `FLOOKUP cenv.ce_vars nm` >>
  Cases_on `FLOOKUP cenv.ce_vars nm`
  >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[])) >>
  rename1 `FLOOKUP _ _ = SOME binding` >> Cases_on `binding` >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_ptr_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Resume body_assign_storage_expr_cases[builtin]:
  disch_then (mp_tac o MATCH_MP reason_compile_expr_builtin_shape_classify) >>
  gvs[reason_result_shape_def] >>
  (simp[exprCallBoundsTheory.builtin_child_callback_def] >>
   pure_once_rewrite_tac [CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)] >>
   Cases_on `bi` >> strip_tac
   >~ [`Acc item`] >- suspend "acc"
   >~ [`AsWeiValue denom`] >- suspend "wei"
   >~ [`Len`] >- (drule reason_builtin_len >> gvs[reason_result_shape_def])
   >~ [`Bop bop`] >- (drule reason_builtin_bop >> gvs[reason_result_shape_def])
   >~ [`MakeArray et bd`] >- (drule reason_builtin_makearray >> gvs[reason_result_shape_def])
   >~ [`MethodId`] >- (drule reason_builtin_method_id >> gvs[reason_result_shape_def])
   >~ [`Keccak256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`Sha256`] >- (drule_at Any reason_builtin_hash >> simp[reason_result_shape_def])
   >~ [`CalldataSlice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECAdd`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`ECMul`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Concat n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Slice n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def])
   >~ [`Uint2Str n`] >- (drule_at Any reason_builtin_fresh >> simp[reason_result_shape_def]) >>
   drule_at Any reason_builtin_scalar >> simp[reason_result_shape_def])
QED

Resume body_assign_storage_expr_cases[typebuiltin]:
  simp[compile_expr_body_def, expr_type_def] >>
  simp[exprCallBoundsTheory.type_child_callback_def] >>
  pure_once_rewrite_tac [CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)] >>
  strip_tac >> Cases_on `tb` >> gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def, oneline as_ptr_val_def,
      mk_ptr_def, base_ptr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), mk_ptr_def, base_ptr_def]
QED

Resume body_assign_storage_expr_cases[acc]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >>
  gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def, AllCaseEqs()]
QED

Resume body_assign_storage_expr_cases[wei]:
  simp[markerTheory.resconj_def, markerTheory.suspendimp_def] >>
  rpt strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), oneline as_stack_val_def]
QED

Finalise body_assign_storage_expr_cases
