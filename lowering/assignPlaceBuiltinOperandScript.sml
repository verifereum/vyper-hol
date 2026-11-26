Theory assignPlaceBuiltinOperand
Ancestors
  exprReasonOperand exprLowering context namedConstDispatchResult

Theorem assign_place_builtin_pointer_not_label:
  compile_builtin_dispatch_body f cenv vt ty bi args sa =
    (LocatedValue rt p,sb) ==> !l. p.ptr_operand <> Label l
Proof
  let
    fun pointer_shape th = drule_at Any th >> simp[reason_result_shape_def]
  in
    strip_tac >> Cases_on `bi`
    >~ [`Len`] >- pointer_shape reason_builtin_len
    >~ [`Bop _`] >- pointer_shape reason_builtin_bop
    >~ [`MakeArray _ _`] >- pointer_shape reason_builtin_makearray
    >~ [`MethodId`] >- pointer_shape reason_builtin_method_id
    >~ [`Acc _`] >-
      gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def,
          AllCaseEqs()]
    >~ [`AsWeiValue _`] >-
      (Cases_on `lower_value f cenv (expr_type (HD args)) (HD args) sa` >>
       gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def,
           AllCaseEqs()])
    >~ [`NamedConst`] >-
      (drule named_const_dispatch_not_label >> simp[vv_operand_def])
    >~ [`BoolChain _ _`] >-
      (gvs[compile_builtin_dispatch_body_def, LET_THM] >>
       rpt (pairarg_tac >> gvs[]))
    >~ [`Keccak256`] >- pointer_shape reason_builtin_hash
    >~ [`Sha256`] >- pointer_shape reason_builtin_hash
    >~ [`CalldataSlice _`] >- pointer_shape reason_builtin_fresh
    >~ [`Concat _`] >- pointer_shape reason_builtin_fresh
    >~ [`Slice _`] >- pointer_shape reason_builtin_fresh
    >~ [`Uint2Str _`] >- pointer_shape reason_builtin_fresh
    >~ [`ECAdd`] >- pointer_shape reason_builtin_fresh
    >~ [`ECMul`] >- pointer_shape reason_builtin_fresh
    >> pointer_shape reason_builtin_scalar
  end
QED
