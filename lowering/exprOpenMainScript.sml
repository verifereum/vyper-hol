(*
 * compile_expr keeps its block open
 *
 * TOP-LEVEL:
 *   compile_expr_open_general — a supported expression that evaluates
 *     compiles, at any annotated type, without terminating its block:
 *     bodySimStmtCases's compile_expr_open
 *)

Theory exprOpenMain
Ancestors
  exprOpenDispatch exprOpenFirstOperand exprOpenChild exprOpenCases
  exprOpenPrimitives exprOpenCopies exprOpenTerminals exprOpenBuiltins
  bodySim exprSimHyps supportedExprs supportedExprForms supportedTypes
  exprLowering exprCallBounds compileEnv vyperAST vyperTypeSystem list

Theorem compile_expr_open_general:
  !e tops ctx cenv cx env es tv es1 aty sa vv sb.
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    expr_body_pre cenv cx env e es /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    eval_expr cx e es = (INL tv,es1) /\
    compile_expr cenv aty e sa = (vv,sb) /\
    ~block_is_terminated sa ==> ~block_is_terminated sb
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >> strip_tac >>
  Cases_on `e`
  >~ [`compile_expr _ _ (Name _ _) _ = _`]
    >- (irule compile_expr_name_open >>
        goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
        gvs[expr_body_pre_def] >> metis_tac[])
  >~ [`compile_expr _ _ (TopLevelName _ _) _ = _`]
    >- suspend "toplevel"
  >~ [`compile_expr _ _ (Literal _ _) _ = _`]
    >- (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
        simp[Once compile_expr_def] >> strip_tac >>
        drule_all compile_literal_vv_open >> simp[])
  >~ [`compile_expr _ _ (FlagMember _ _ _) _ = _`]
    >- gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
  >~ [`compile_expr _ _ (Builtin _ _ _) _ = _`] >- suspend "builtin"
  >~ [`compile_expr _ _ (TypeBuiltin _ _ _ _) _ = _`] >- suspend "type_builtin" >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def]
  >~ [`compile_expr_body _ _ _ _ _ (IfExp _ _ _ _) _ = _`]
    >- metis_tac[compile_ifexp_open]
  >~ [`compile_expr_body _ _ _ _ _ (Pop _ _) _ = _`]
    >- metis_tac[compile_pop_body_open]
  >~ [`compile_expr_body _ _ _ _ _ (StructLit _ _ _) _ = _`]
    >- (strip_tac >> irule compile_struct_literal_body_open >>
        goal_assum (drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`)) >>
        gvs[expr_body_pre_def] >> metis_tac[])
  >~ [`compile_expr_body _ _ _ _ _ (Subscript _ _ _) _ = _`]
    >- (simp[compile_expr_body_def] >> metis_tac[compile_subscript_open])
  >~ [`compile_expr_body _ _ _ _ _ (Attribute _ _ _) _ = _`]
    >- (simp[compile_expr_body_def] >> metis_tac[compile_attribute_open]) >>
  simp[compile_expr_body_def] >> metis_tac[compile_supported_call_open]
QED

Resume compile_expr_open_general[toplevel]:
  PairCases_on `p` >>
  irule compile_expr_toplevel_open >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
      body_inv_def] >> metis_tac[]
QED

Resume compile_expr_open_general[builtin]:
  rename1 `compile_expr cenv aty (Builtin ann bi args) sa = (vv,sb)` >>
  `!arg rest. args = arg::rest ==>
     !cty v st. lower_value
       (expr_child_callback (list_size expr_size args) compile_expr)
       cenv cty arg sa = (v,st) ==> ~block_is_terminated st` by
    (rpt gen_tac >> strip_tac >> gvs[] >> rpt gen_tac >> strip_tac >>
     drule_at (Pat `lower_value _ _ _ _ _ = _`) lower_value_child_open >>
     simp[] >> disch_then irule >>
     rpt gen_tac >> strip_tac >>
     drule eval_builtin_head_success >> strip_tac >>
     drule expr_body_pre_builtin_head >> disch_tac >>
     `supported_expr tops arg` by
       gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
           supported_pure_exprs_every] >>
     qpat_x_assum `!y. expr_size y < _ ==> _` irule >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     simp[expr_size_def] >> metis_tac[expr_list_member_bound, MEM]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  drule_at (Pat `compile_expr_body _ _ _ _ _ _ _ = _`) compile_builtin_body_open >>
  disch_then irule >>
  simp[builtin_child_callback_def, expr_size_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_builtin_dispatch _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  suspend "builtin_dispatch"
QED

Resume compile_expr_open_general[type_builtin]:
  rename1 `compile_expr cenv aty (TypeBuiltin ann tb rty args) sa = (vv,sb)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, type_child_callback_def, expr_size_def,
       vyperASTTheory.expr_type_def] >>
  once_rewrite_tac[compile_expr_raw_def] >> strip_tac >>
  Cases_on `tb`
  >~ [`Empty`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`MaxValue`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`MinValue`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`Epsilon`] >- metis_tac[compile_type_dispatch_constant_open]
  >~ [`AbiEncode`] >- metis_tac[compile_type_dispatch_abi_open]
  >~ [`AbiDecode`] >- metis_tac[compile_type_dispatch_abi_open]
  >~ [`Extract32`]
    >- (Cases_on `args` >>
        gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
            supported_type_builtin_form_def] >>
        rename1 `TypeBuiltin _ _ _ (arg_e::rest)` >> Cases_on `rest` >>
        gvs[supported_type_builtin_form_def]) >>
  Cases_on `args` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
      supported_type_builtin_form_def, supported_pure_exprs_every] >>
  rename1 `TypeBuiltin _ _ _ (arg_e::rest)` >> Cases_on `rest` >>
  gvs[supported_type_builtin_form_def] >>
  drule_at (Pat `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _`)
    compile_type_dispatch_convert_open >> disch_then irule >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`) lower_value_child_open >>
  simp[] >> disch_then irule >> rpt gen_tac >> strip_tac >>
  drule eval_type_builtin_head_success >> strip_tac >>
  drule expr_body_pre_type_builtin_head >> disch_tac >>
  qpat_x_assum `!y. expr_size y < _ ==> _` irule >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[expr_size_def, supported_expr_def] >> metis_tac[]
QED

Resume compile_expr_open_general[builtin_dispatch]:
  `supported_builtin_form tops ann bi args` by
    gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  Cases_on `bi`
  >~ [`Not`] >- metis_tac[compile_dispatch_not_open]
  >~ [`Neg`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`Abs`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`AddMod`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`MulMod`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`PowMod256`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`Env`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`BlockHash`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`BlobHash`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`ECRecover`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`ECAdd`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`ECMul`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`Uint2Str`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`CalldataSlice`] >- metis_tac[compile_dispatch_terminal_open]
  >~ [`MakeArray elem bound`]
    >- (Cases_on `elem` >> gvs[supported_builtin_form_def] >>
        drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
          compile_dispatch_make_array_open >> simp[] >> metis_tac[]) >>
  Cases_on `args` >> gvs[supported_builtin_form_def] >>
  rename1 `compile_builtin_dispatch_body _ _ _ _ _ (arg_e::rest) _ = _` >>
  Cases_on `rest` >> gvs[supported_builtin_form_def]
  >~ [`Bop op`]
    >- (rename1 `compile_builtin_dispatch_body _ _ _ _ _ (arg_e::arg2_e::rest) _ = _` >>
        Cases_on `rest` >> gvs[supported_builtin_form_def] >>
        metis_tac[compile_dispatch_bop_open])
  >~ [`AsWeiValue`]
    >- (drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
          compile_dispatch_as_wei_value_open >> simp[] >>
        disch_then irule >> rpt strip_tac >> gvs[SF ETA_ss] >> metis_tac[]) >>
  drule_at (Pat `compile_builtin_dispatch_body _ _ _ _ _ _ _ = _`)
    compile_dispatch_acc_open >> simp[] >> disch_then irule >>
  rpt strip_tac >> gvs[SF ETA_ss] >> metis_tac[]
QED

Finalise compile_expr_open_general
