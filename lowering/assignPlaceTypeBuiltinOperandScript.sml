Theory assignPlaceTypeBuiltinOperand
Ancestors
  exprSafeOperandBuiltins exprReasonOperand exprLowering context

Theorem assign_place_type_builtin_pointer_not_label:
  compile_type_builtin_dispatch_body f cenv vt ty tb ret_ty args sa =
    (LocatedValue rt p,sb) ==> !l. p.ptr_operand <> Label l
Proof
  Cases_on `tb` >>
  gvs[compile_type_builtin_dispatch_body_def,
      oneline as_stack_val_def, oneline as_ptr_val_def,
      AllCaseEqs(), base_ptr_def] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), mk_ptr_def] >>
  metis_tac[compile_empty_not_label, reason_abi_encode_operand,
            lower_abi_decode_not_label]
QED
