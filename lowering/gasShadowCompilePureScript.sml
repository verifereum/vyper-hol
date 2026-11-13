(* Pure observations and total selectors for source shadows. *)
Theory gasShadowCompilePure
Ancestors
  gasShadowCompileBase gasShadow exprLowering vyperSubscriptOverlap
  vyperTypeCallGraph vyperAST list pair

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

Theorem gas_shadow_bytestring_literal_hash[simp]:
  bytestring_literal_hash (gas_shadow_expr e) = bytestring_literal_hash e
Proof
  Cases_on `e` >> simp[gas_shadow_expr_def, bytestring_literal_hash_def]
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
  completeInduct_on `expr_size e` >> rpt strip_tac >> gvs[PULL_FORALL] >>
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
  Cases_on `tb` >> simp[lowered_value_type_def, expr_type_def, MAP_MAP_o, combinTheory.o_DEF] >>
  Cases_on `args` >> simp[gas_shadow_HD, MAP_MAP_o, combinTheory.o_DEF] >>
  rename1 `h::t` >>
  `!x. MEM x (h::t) ==>
       lowered_value_type cenv (gas_shadow_expr x) = lowered_value_type cenv x`
    by (rpt strip_tac >> first_x_assum irule >>
        drule exprCallBoundsTheory.expr_list_member_bound >> simp[expr_size_def]) >>
  `MAP (\x. lowered_value_type cenv (gas_shadow_expr x)) t =
   MAP (lowered_value_type cenv) t` by simp[MAP_EQ_f] >>
  simp[]
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

Theorem gas_shadow_accesses_expr[local]:
  (!e. accesses_expr (gas_shadow_expr e) = accesses_expr e) /\
  (!t. accesses_target (gas_shadow_target t) = accesses_target t) /\
  (!es. accesses_exprs (MAP gas_shadow_expr es) = accesses_exprs es) /\
  (!opt. accesses_opt (OPTION_MAP gas_shadow_expr opt) = accesses_opt opt) /\
  (!kes. accesses_named_exprs (MAP (I ## gas_shadow_expr) kes) =
         accesses_named_exprs kes)
Proof
  ho_match_mp_tac accesses_expr_ind >>
  rw[accesses_expr_def, gas_shadow_expr_def, gas_shadow_builtin_def,
     risky_builtin_def, pairTheory.PAIR_MAP_THM] >>
  gvs[COND_RAND, risky_builtin_def]
QED

Theorem gas_shadow_int_calls_expr[local]:
  (!e. int_calls_expr (gas_shadow_expr e) = int_calls_expr e) /\
  (!t. int_calls_target (gas_shadow_target t) = int_calls_target t) /\
  (!es. int_calls_exprs (MAP gas_shadow_expr es) = int_calls_exprs es) /\
  (!opt. int_calls_opt (OPTION_MAP gas_shadow_expr opt) = int_calls_opt opt) /\
  (!kes. int_calls_named_exprs (MAP (I ## gas_shadow_expr) kes) =
         int_calls_named_exprs kes)
Proof
  ho_match_mp_tac int_calls_expr_ind >>
  rw[int_calls_expr_def, gas_shadow_expr_def, pairTheory.PAIR_MAP_THM]
QED

Theorem gas_shadow_base_through_dynarray[local]:
  !e. base_through_dynarray (gas_shadow_expr e) = base_through_dynarray e
Proof
  ho_match_mp_tac
    (expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
      SIMP_RULE (srw_ss()) []) >>
  simp[gas_shadow_expr_def, base_through_dynarray_def]
QED

Theorem gas_shadow_subscript_overlap[simp]:
  subscript_overlap mods (gas_shadow_expr base_e) (gas_shadow_expr idx_e) =
  subscript_overlap mods base_e idx_e
Proof
  simp[subscript_overlap_def, expr_accesses_def, reached_functions_def,
       gas_shadow_accesses_expr, gas_shadow_int_calls_expr,
       gas_shadow_base_through_dynarray]
QED
