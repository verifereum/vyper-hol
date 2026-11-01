(* Supported type-builtin callback boundaries. *)
Theory bodyIntCallTypeBuiltinLabels
Ancestors
  bodyIntCallBuiltinLabels bodyIntCallLabelFrame bodyIntCallLabelReservations
  supportedExprForms exprLowering

Theorem compiler_block_tail_type_extrema_dispatch:
  (tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) ==>
  compiler_block_tail
    (compile_type_builtin_dispatch_body cfn cenv ann ty tb rt args)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `type_bounds rt` >> simp[compiler_block_tail_def]
QED

Theorem compiler_label_hoare_type_extrema_dispatch:
  (tb = MaxValue \/ tb = MinValue \/ tb = Epsilon) ==>
  compiler_label_hoare P
    (compile_type_builtin_dispatch_body cfn cenv ann ty tb rt args)
    (\r out. P out)
Proof
  strip_tac >> gvs[] >>
  rewrite_tac[lambdify compile_type_builtin_dispatch_body_def] >> simp[] >>
  Cases_on `type_bounds rt` >> simp[compiler_label_hoare_def]
QED
