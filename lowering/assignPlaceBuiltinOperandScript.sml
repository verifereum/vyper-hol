Theory assignPlaceBuiltinOperand
Ancestors
  exprReasonOperand exprLowering context

Theorem assign_place_builtin_pointer_not_label:
  compile_builtin_dispatch_body f cenv vt ty bi args sa =
    (LocatedValue rt p,sb) ==> !l. p.ptr_operand <> Label l
Proof
  strip_tac >>
  `(!item. bi <> Acc item) /\ (!denom. bi <> AsWeiValue denom)` by
    (conj_tac
     >- (rpt strip_tac >>
         gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def,
             AllCaseEqs()]) >>
     rpt strip_tac >>
     Cases_on `lower_value f cenv (expr_type (HD args)) (HD args) sa` >>
     gvs[compile_builtin_dispatch_body_def, oneline as_stack_val_def,
         AllCaseEqs()]) >>
  Cases_on `bi` >>
  metis_tac[reason_builtin_scalar, reason_builtin_hash, reason_builtin_len,
            reason_builtin_bop, reason_builtin_fresh, reason_builtin_makearray,
            reason_builtin_method_id, reason_result_shape_def]
QED
