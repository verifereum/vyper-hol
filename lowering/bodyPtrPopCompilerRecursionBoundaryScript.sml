Theory bodyPtrPopCompilerRecursionBoundary
Ancestors bodyPtrPopMathIntegration bodyPtrPopCompilerBoundary
  bodyPtrPopSliceIntegration
  exprLowering exprCallBounds compileEnv list basicSize

Theorem pop_builtin_child_boundary:
  (!s v t. list_size expr_size args < bound /\ pop_comp_boundary s /\
    bfn cenv ret_ty ty bi args s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  builtin_child_callback bound bfn cenv ret_ty ty bi args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `list_size expr_size args < bound` >>
  simp[builtin_child_callback_def] >> rpt strip_tac
  >- metis_tac[] >>
  drule_all pop_invalid_expr_boundary >> simp[]
QED

Theorem pop_type_child_boundary:
  (!s v t. list_size expr_size args < bound /\ pop_comp_boundary s /\
    tfn cenv vv_ty ty tb ret_ty args s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  type_child_callback bound tfn cenv vv_ty ty tb ret_ty args sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `list_size expr_size args < bound` >>
  simp[type_child_callback_def] >> rpt strip_tac
  >- metis_tac[] >>
  drule_all pop_invalid_expr_boundary >> simp[]
QED

Theorem pop_compile_mutual_boundary_closure:
  !E B TT.
  (!cfn bfn tfn.
    (!cenv ty e sa r sb. E e /\ pop_comp_boundary sa /\
      cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
    (!cenv ret_ty ty bi args sa r sb. B ret_ty bi args /\ pop_comp_boundary sa /\
      bfn cenv ret_ty ty bi args sa = (r,sb) ==> pop_comp_boundary sb) /\
    (!cenv vv_ty ty tb ret_ty args sa r sb. TT vv_ty tb ret_ty args /\ pop_comp_boundary sa /\
      tfn cenv vv_ty ty tb ret_ty args sa = (r,sb) ==> pop_comp_boundary sb) ==>
    !cenv ty e sa r sb. E e /\ pop_comp_boundary sa /\
      compile_expr_body cfn bfn tfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cfn.
    (!cenv ty e sa r sb. E e /\ pop_comp_boundary sa /\
      cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) ==>
    !cenv ret_ty ty bi args sa r sb. B ret_ty bi args /\ pop_comp_boundary sa /\
      compile_builtin_dispatch_body cfn cenv ret_ty ty bi args sa = (r,sb) ==>
      pop_comp_boundary sb) /\
  (!cfn.
    (!cenv ty e sa r sb. E e /\ pop_comp_boundary sa /\
      cfn cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) ==>
    !cenv vv_ty ty tb ret_ty args sa r sb. TT vv_ty tb ret_ty args /\ pop_comp_boundary sa /\
      compile_type_builtin_dispatch_body cfn cenv vv_ty ty tb ret_ty args sa = (r,sb) ==>
      pop_comp_boundary sb) ==>
  (!cenv ty e sa r sb. E e /\ pop_comp_boundary sa /\
    compile_expr cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cenv ret_ty ty bi args sa r sb. B ret_ty bi args /\ pop_comp_boundary sa /\
    compile_builtin_dispatch cenv ret_ty ty bi args sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cenv vv_ty ty tb ret_ty args sa r sb. TT vv_ty tb ret_ty args /\ pop_comp_boundary sa /\
    compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args sa = (r,sb) ==>
    pop_comp_boundary sb)
Proof
  rpt gen_tac >> strip_tac >>
  `!n.
    (!cenv ty e sa r sb. 2 * expr_size e + 2 = n /\ E e /\ pop_comp_boundary sa /\
      compile_expr cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
    (!cenv ret_ty ty bi args sa r sb. 2 * list_size expr_size args + 1 = n /\
      B ret_ty bi args /\ pop_comp_boundary sa /\
      compile_builtin_dispatch cenv ret_ty ty bi args sa = (r,sb) ==> pop_comp_boundary sb) /\
    (!cenv vv_ty ty tb ret_ty args sa r sb. 2 * list_size expr_size args + 1 = n /\
      TT vv_ty tb ret_ty args /\ pop_comp_boundary sa /\
      compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args sa = (r,sb) ==>
      pop_comp_boundary sb)` suffices_by metis_tac[] >>
  completeInduct_on `n` >>
  conj_tac >- suspend "expr" >>
  conj_tac >- suspend "builtin" >>
  suspend "type"
QED

Resume pop_compile_mutual_boundary_closure[expr]:
  rpt strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  qpat_assum `!cfn bfn tfn. _`
    (drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`)) >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "expr_callback" >>
  conj_tac >- suspend "builtin_callback" >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  suspend "type_callback"
QED

Resume pop_compile_mutual_boundary_closure[expr_callback]:
  rpt strip_tac >>
  drule_at (Pat `expr_child_callback _ _ _ _ _ _ = _`)
    pop_expr_child_typed_boundary >>
  disch_then irule >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[] >> rpt strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `2 * expr_size e' + 2` mp_tac) >>
  (impl_tac >- decide_tac) >>
  rule_assum_tac BETA_RULE >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`) o CONJUNCT1) >>
  disch_then irule >> simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume pop_compile_mutual_boundary_closure[builtin_callback]:
  rpt strip_tac >>
  drule_at (Pat `builtin_child_callback _ _ _ _ _ _ _ _ = _`)
    pop_builtin_child_boundary >>
  disch_then irule >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `2 * list_size expr_size args + 1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  rule_assum_tac BETA_RULE >>
  disch_then (drule_at (Pat `compile_builtin_dispatch _ _ _ _ _ _ = _`) o
    CONJUNCT1 o CONJUNCT2) >>
  disch_then irule >> simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume pop_compile_mutual_boundary_closure[type_callback]:
  rpt strip_tac >>
  drule_at (Pat `type_child_callback _ _ _ _ _ _ _ _ _ = _`)
    pop_type_child_boundary >>
  disch_then irule >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `2 * list_size expr_size args + 1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  rule_assum_tac BETA_RULE >>
  disch_then (drule_at (Pat `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _`) o
    CONJUNCT2 o CONJUNCT2) >>
  disch_then irule >> simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume pop_compile_mutual_boundary_closure[builtin]:
  rpt strip_tac >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  first_assum
    (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)) >>
  disch_then irule >>
  conj_tac >- suspend "builtin_expr_callback" >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume pop_compile_mutual_boundary_closure[type]:
  rpt strip_tac >>
  qpat_x_assum `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_expr_raw_def] >>
  simp_tac bool_ss [] >> strip_tac >>
  first_assum
    (drule_at (Pat `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _`)) >>
  disch_then irule >>
  conj_tac >- suspend "type_expr_callback" >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume pop_compile_mutual_boundary_closure[builtin_expr_callback]:
  rpt strip_tac >>
  drule_at (Pat `expr_child_callback _ _ _ _ _ _ = _`)
    pop_expr_child_typed_boundary >>
  disch_then irule >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `2 * expr_size e + 2` mp_tac) >>
  (impl_tac >- decide_tac) >>
  rule_assum_tac BETA_RULE >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`) o CONJUNCT1) >>
  disch_then irule >> simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume pop_compile_mutual_boundary_closure[type_expr_callback]:
  rpt strip_tac >>
  drule_at (Pat `expr_child_callback _ _ _ _ _ _ = _`)
    pop_expr_child_typed_boundary >>
  disch_then irule >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_x_assum `!m. _` (qspec_then `2 * expr_size e + 2` mp_tac) >>
  (impl_tac >- decide_tac) >>
  rule_assum_tac BETA_RULE >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`) o CONJUNCT1) >>
  disch_then irule >> simp_tac bool_ss [] >>
  conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Finalise pop_compile_mutual_boundary_closure
