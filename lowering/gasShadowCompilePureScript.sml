(* Pure observations and total selectors for source shadows. *)
Theory gasShadowCompilePure
Ancestors
  gasShadowCompileBase gasShadow exprLowering exprCallBounds vyperAST list pair

Theorem gas_shadow_place_type[simp]:
  !e cenv. place_type cenv (gas_shadow_expr e) = place_type cenv e
Proof
  ho_match_mp_tac
    (expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
      SIMP_RULE (srw_ss()) []) >>
  simp[gas_shadow_expr_def, place_type_def, expr_type_def]
QED

Theorem gas_shadow_infer_array_location[simp]:
  infer_array_location cenv (gas_shadow_expr e) = infer_array_location cenv e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, infer_array_location_def]
QED

Theorem gas_shadow_expr_int_literal[simp]:
  expr_int_literal (gas_shadow_expr e) = expr_int_literal e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, expr_int_literal_def]
QED

Theorem gas_shadow_method_id_literal[simp]:
  method_id_literal (gas_shadow_expr e) = method_id_literal e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, method_id_literal_def]
QED

Theorem gas_shadow_HD:
  HD (MAP gas_shadow_expr args) =
    if args = [] then HD args else gas_shadow_expr (HD args)
Proof
  Cases_on `args` >> simp[]
QED

Theorem gas_shadow_TL[simp]:
  TL (MAP gas_shadow_expr args) = MAP gas_shadow_expr (TL args)
Proof
  Cases_on `args` >> simp[]
QED

Theorem gas_shadow_EL:
  !n args. EL n (MAP gas_shadow_expr args) =
    if n < LENGTH args then gas_shadow_expr (EL n args) else EL n args
Proof
  Induct >> Cases_on `args` >> simp[EL, gas_shadow_HD]
QED

Theorem gas_shadow_lowered_value_type[simp]:
  lowered_value_type cenv (gas_shadow_expr e) = lowered_value_type cenv e
Proof
  completeInduct_on `expr_size e` >> rpt strip_tac >> gvs[] >>
  Cases_on `e` >>
  simp[gas_shadow_expr_def, lowered_value_type_def, expr_type_def]
  >~ [`lowered_value_type _ (Call _ ct _ _) = _`]
  >- (Cases_on `ct` >> simp[lowered_value_type_def, expr_type_def])
  >~ [`lowered_value_type _ (Builtin _ _ _) = _`]
  >- (rename1 `gas_shadow_builtin bi` >>
      Cases_on `bi` >>
      simp[gas_shadow_builtin_def, lowered_value_type_def, expr_type_def,
           MAP_MAP_o, combinTheory.o_DEF] >>
      IF_CASES_TAC >> simp[lowered_value_type_def, expr_type_def]) >>
  rename1 `MAP gas_shadow_expr args` >>
  rename1 `TypeBuiltin ann tb ret_ty _` >>
  Cases_on `tb` >> simp[lowered_value_type_def, expr_type_def, MAP_MAP_o, combinTheory.o_DEF]
  >~ [`AbiEncode ensure method_id`]
  >- (`!a. MEM a args ==>
         lowered_value_type cenv (gas_shadow_expr a) = lowered_value_type cenv a`
        by (rpt strip_tac >>
            first_x_assum (qspec_then `expr_size a` mp_tac) >>
            impl_tac >- (drule expr_list_member_bound >> simp[expr_size_def, ETA_AX]) >>
            simp[]) >>
      `MAP (\a. lowered_value_type cenv (gas_shadow_expr a)) args =
       MAP (lowered_value_type cenv) args` by (irule MAP_CONG >> simp[]) >>
      Cases_on `args` >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  Cases_on `args` >> simp[gas_shadow_HD, MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem gas_shadow_is_msg_data[simp]:
  is_msg_data (gas_shadow_expr e) = is_msg_data e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, is_msg_data_def] >>
  rename1 `gas_shadow_expr obj` >> Cases_on `obj` >>
  simp[gas_shadow_expr_def, is_msg_data_def]
QED

Theorem gas_shadow_is_extcode[simp]:
  is_extcode (gas_shadow_expr e) = is_extcode e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, is_extcode_def] >>
  rename1 `MAP gas_shadow_expr args` >>
  rename1 `gas_shadow_builtin bi` >>
  Cases_on `bi` >>
  rw[gas_shadow_builtin_def, is_extcode_def] >>
  Cases_on `args` >> simp[is_extcode_def] >>
  rename1 `MAP gas_shadow_expr tail` >> Cases_on `tail` >> simp[is_extcode_def] >>
  rename1 `Acc acc` >> Cases_on `acc` >> simp[is_extcode_def]
QED

Theorem gas_shadow_extcode_addr_expr[simp]:
  extcode_addr_expr (gas_shadow_expr e) = gas_shadow_expr (extcode_addr_expr e)
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, extcode_addr_expr_def] >>
  rename1 `MAP gas_shadow_expr args` >>
  rename1 `gas_shadow_builtin bi` >>
  Cases_on `bi` >>
  rw[gas_shadow_builtin_def, extcode_addr_expr_def, gas_shadow_expr_def] >>
  rename1 `Acc acc` >> Cases_on `acc` >>
  simp[extcode_addr_expr_def, gas_shadow_expr_def] >>
  Cases_on `args` >> simp[extcode_addr_expr_def, gas_shadow_expr_def] >>
  rename1 `MAP gas_shadow_expr tail` >> Cases_on `tail` >>
  simp[extcode_addr_expr_def, gas_shadow_expr_def]
QED

Theorem gas_shadow_is_self_code[simp]:
  is_self_code (gas_shadow_expr e) = is_self_code e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, is_self_code_def] >>
  rename1 `MAP gas_shadow_expr args` >>
  rename1 `gas_shadow_builtin bi` >> Cases_on `bi` >>
  rw[gas_shadow_builtin_def, is_self_code_def] >>
  rename1 `Acc acc` >> Cases_on `acc` >> simp[is_self_code_def] >>
  Cases_on `args` >> simp[is_self_code_def] >>
  rename1 `MAP gas_shadow_expr tail` >> Cases_on `tail` >> simp[is_self_code_def] >>
  rename1 `gas_shadow_expr head` >> Cases_on `head` >>
  simp[gas_shadow_expr_def, is_self_code_def] >>
  rename1 `gas_shadow_builtin child_bi` >> Cases_on `child_bi` >>
  rw[gas_shadow_builtin_def, is_self_code_def] >>
  rename1 `Env env` >> Cases_on `env` >> simp[is_self_code_def] >>
  rename1 `MAP gas_shadow_expr child_args` >> Cases_on `child_args` >>
  simp[is_self_code_def]
QED

Theorem gas_shadow_HD_alternative:
  !args shadow. ?selected_shadow.
    HD (if shadow then MAP gas_shadow_expr args else args) =
    if selected_shadow then gas_shadow_expr (HD args) else HD args
Proof
  rpt gen_tac >> Cases_on `shadow`
  >- (Cases_on `args = []`
      >- (qexists_tac `F` >> simp[gas_shadow_HD]) >>
      qexists_tac `T` >> simp[gas_shadow_HD]) >>
  qexists_tac `F` >> simp[]
QED

Theorem gas_shadow_EL_alternative:
  !n args shadow. ?selected_shadow.
    EL n (if shadow then MAP gas_shadow_expr args else args) =
    if selected_shadow then gas_shadow_expr (EL n args) else EL n args
Proof
  rpt gen_tac >> Cases_on `shadow`
  >- (Cases_on `n < LENGTH args`
      >- (qexists_tac `T` >> simp[gas_shadow_EL]) >>
      qexists_tac `F` >> simp[gas_shadow_EL]) >>
  qexists_tac `F` >> simp[]
QED
