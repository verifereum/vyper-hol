(* Pure arms cannot select the internal-call layout alternative. *)
Theory bodyIntCallPureLayout
Ancestors
  exprSimIfExpCompat supportedExprs

Theorem pure_expr_lowered_type_compatible:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          well_formed_type env.type_defs t) /\
  sfields_tenv_consistent ce.ce_struct_fields env.type_defs /\
  supported_pure_expr tops e ==>
  lowered_value_type ce e = expr_type e \/
  (is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type ce e) /\
   arg_type_fits (lowered_value_type ce e) (expr_type e))
Proof
  strip_tac >> drule_all ifexp_lowered_type_classify >>
  strip_tac >> gvs[supported_pure_expr_def]
QED
