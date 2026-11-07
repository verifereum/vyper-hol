Theory gasShadowAllocLimits
Ancestors
  gasShadowSourceMetadata gasShadowModuleDefs gasShadowCompileStmtBase
  gasShadowCenv gasShadow allocLimits compileVyper list vyperAST

Theorem gas_shadow_map_expr_type[simp]:
  !es. MAP expr_type (MAP gas_shadow_expr es) = MAP expr_type es
Proof
  Induct >> simp[]
QED

(* The shadow keeps a slice's .code source and its address. *)
Theorem gas_shadow_extcode[local]:
  !e. (is_extcode (gas_shadow_expr e) <=> is_extcode e) /\
      (is_extcode e ==>
       extcode_addr_expr (gas_shadow_expr e) =
       gas_shadow_expr (extcode_addr_expr e))
Proof
  Cases >> simp[gas_shadow_expr_def, exprLoweringTheory.is_extcode_def] >>
  rename1 `Builtin _ b l` >> Cases_on `b` >>
  rw[gas_shadow_builtin_def, exprLoweringTheory.is_extcode_def] >>
  rename1 `Acc a` >> Cases_on `a` >>
  simp[exprLoweringTheory.is_extcode_def] >>
  Cases_on `l` >> simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `_ :: tl` >> Cases_on `tl` >>
  simp[exprLoweringTheory.is_extcode_def,
       exprLoweringTheory.extcode_addr_expr_def]
QED

Theorem gas_shadow_alloc_limits_expr:
  (!ce e. alloc_limits_expr ce (gas_shadow_expr e) = alloc_limits_expr ce e) /\
  (!ce g. alloc_limits_target ce (gas_shadow_target g) = alloc_limits_target ce g) /\
  (!ce es. alloc_limits_exprs ce (MAP gas_shadow_expr es) = alloc_limits_exprs ce es) /\
  (!ce eo. alloc_limits_opt ce (OPTION_MAP gas_shadow_expr eo) = alloc_limits_opt ce eo) /\
  (!ce es. alloc_limits_named_exprs ce (MAP (I ## gas_shadow_expr) es) =
    alloc_limits_named_exprs ce es)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >>
  simp[gas_shadow_expr_def, alloc_limits_expr_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `bi` >>
      gvs[gas_shadow_builtin_def, MAP_MAP_o, combinTheory.o_DEF]
      >~ [`extcode_addr_expr`]
      >- (Cases_on `es` >> gvs[gas_shadow_extcode] >>
          rename1 `is_extcode h` >> Cases_on `is_extcode h` >>
          gvs[gas_shadow_extcode]) >>
      IF_CASES_TAC >> gvs[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `tb` >> simp[] >>
      Cases_on `es` >> simp[]) >>
  rpt gen_tac >> strip_tac >> simp[] >> Cases_on `ct` >>
  simp[ext_call_alloc_ok_def] >> rename1 `ExtCall _ _ sig _` >>
  PairCases_on `sig` >>
  simp[SF ETA_ss, ext_call_alloc_ok_def, GSYM MAP_DROP, GSYM MAP_TAKE, MAP_MAP_o,
       combinTheory.o_DEF, gasShadowCompilePureTheory.gas_shadow_lowered_value_type]
QED

Theorem gas_shadow_alloc_limits_assignment:
  (!ce g. alloc_limits_assignment ce (gas_shadow_assignment g) = alloc_limits_assignment ce g) /\
  (!ce gs. alloc_limits_assignments ce (MAP gas_shadow_assignment gs) = alloc_limits_assignments ce gs)
Proof
  ho_match_mp_tac alloc_limits_assignment_ind >>
  simp[gas_shadow_assignment_def, alloc_limits_assignment_def,
       gas_shadow_alloc_limits_expr]
QED

Theorem gas_shadow_alloc_limits_iterator[simp]:
  !ce it. alloc_limits_iterator ce (gas_shadow_iterator it) = alloc_limits_iterator ce it
Proof
  rpt gen_tac >> Cases_on `it` >>
  simp[gas_shadow_iterator_def, alloc_limits_iterator_def, gas_shadow_alloc_limits_expr]
QED

Theorem gas_shadow_custom_error_exprs:
  !err. custom_error_exprs (gas_shadow_custom_error err) =
    MAP gas_shadow_expr (custom_error_exprs err)
Proof
  Cases >> simp[gas_shadow_custom_error_def, custom_error_exprs_def,
                MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]
QED

Theorem gas_shadow_alloc_limits_assert[simp]:
  !ce ar. alloc_limits_assert ce (gas_shadow_assert_reason ar) = alloc_limits_assert ce ar
Proof
  rpt gen_tac >> Cases_on `ar` >>
  simp[gas_shadow_assert_reason_def, alloc_limits_assert_def,
       gas_shadow_custom_error_exprs, gas_shadow_alloc_limits_expr]
QED

Theorem gas_shadow_alloc_limits_raise[simp]:
  !ce rr. alloc_limits_raise ce (gas_shadow_raise_reason rr) = alloc_limits_raise ce rr
Proof
  rpt gen_tac >> Cases_on `rr` >>
  simp[gas_shadow_raise_reason_def, alloc_limits_raise_def,
       gas_shadow_custom_error_exprs, gas_shadow_alloc_limits_expr]
QED

Theorem gas_shadow_log_alloc_ok[simp]:
  !ce id es. log_alloc_ok ce id (MAP gas_shadow_expr es) = log_alloc_ok ce id es
Proof
  simp[log_alloc_ok_def]
QED

Theorem gas_shadow_target_store_place[local]:
  !ce bt. target_store_place ce (gas_shadow_target bt) = target_store_place ce bt
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >>
  gvs[gas_shadow_expr_def, target_store_place_def]
QED

Theorem gas_shadow_lowered_value_type[local]:
  !ce e. lowered_value_type ce (gas_shadow_expr e) = lowered_value_type ce e
Proof
  recInduct exprLoweringTheory.lowered_value_type_ind >>
  rw[gas_shadow_expr_def, exprLoweringTheory.lowered_value_type_def,
     vyperASTTheory.expr_type_def] >>
  gvs[listTheory.LENGTH_EQ_NUM_compute]
QED

Theorem gas_shadow_is_empty_value_expr[local]:
  !e. is_empty_value_expr (gas_shadow_expr e) = is_empty_value_expr e
Proof
  recInduct stmtLoweringTheory.is_empty_value_expr_ind >>
  rw[gas_shadow_expr_def, gas_shadow_builtin_def,
     stmtLoweringTheory.is_empty_value_expr_def]
QED

Theorem gas_shadow_assign_alloc_ok[local]:
  !ce bt e. assign_alloc_ok ce (gas_shadow_target bt) (gas_shadow_expr e) =
            assign_alloc_ok ce bt e
Proof
  simp[assign_alloc_ok_def, gas_shadow_target_store_place,
       gas_shadow_lowered_value_type, gas_shadow_is_empty_value_expr]
QED

Theorem gas_shadow_alloc_limits_stmt:
  (!ce s. alloc_limits_stmt ce (gas_shadow_stmt s) = alloc_limits_stmt ce s) /\
  (!ce ss. alloc_limits_stmts ce (MAP gas_shadow_stmt ss) = alloc_limits_stmts ce ss)
Proof
  ho_match_mp_tac alloc_limits_stmt_ind >>
  simp[gas_shadow_stmt_def, alloc_limits_stmt_def, gas_shadow_alloc_limits_expr,
       gas_shadow_alloc_limits_assignment] >>
  rpt gen_tac >> Cases_on `g` >>
  simp[gas_shadow_assignment_def, gas_shadow_assign_alloc_ok]
QED

Theorem gas_shadow_stmt_valued_return:
  (!s. stmt_valued_return (gas_shadow_stmt s) = stmt_valued_return s) /\
  (!ss. stmts_valued_return (MAP gas_shadow_stmt ss) = stmts_valued_return ss)
Proof
  ho_match_mp_tac stmt_valued_return_ind >>
  simp[gas_shadow_stmt_def, stmt_valued_return_def]
QED

(* The allocation limits read no default arguments. *)
Theorem gas_shadow_cenv_alloc_basic[simp]:
  (!c t. type_alloc_ok (gas_shadow_cenv c) t = type_alloc_ok c t) /\
  (!c id es. log_alloc_ok (gas_shadow_cenv c) id es = log_alloc_ok c id es) /\
  (!c tg es. ext_call_alloc_ok (gas_shadow_cenv c) tg es =
             ext_call_alloc_ok c tg es)
Proof
  rpt conj_tac
  >- simp[type_alloc_ok_def]
  >- simp[log_alloc_ok_def] >>
  ho_match_mp_tac ext_call_alloc_ok_ind >> simp[ext_call_alloc_ok_def]
QED

Theorem gas_shadow_cenv_target_store_place[simp]:
  !bt. target_store_place (gas_shadow_cenv c) bt = target_store_place c bt
Proof
  `(!e:expr. T) /\
   (!bt. target_store_place (gas_shadow_cenv c) bt = target_store_place c bt)`
    suffices_by simp[] >>
  ho_match_mp_tac expr_induction >> simp[target_store_place_def]
QED

Theorem gas_shadow_cenv_return_buffer_ok[simp]:
  return_buffer_ok (gas_shadow_cenv c) = return_buffer_ok c
Proof
  simp[return_buffer_ok_def]
QED

Theorem gas_shadow_cenv_assign_alloc_ok[simp]:
  assign_alloc_ok (gas_shadow_cenv c) bt e = assign_alloc_ok c bt e
Proof
  simp[assign_alloc_ok_def]
QED

Theorem gas_shadow_cenv_alloc_limits_expr[simp]:
  (!c e. alloc_limits_expr (gas_shadow_cenv c) e = alloc_limits_expr c e) /\
  (!c t. alloc_limits_target (gas_shadow_cenv c) t = alloc_limits_target c t) /\
  (!c es. alloc_limits_exprs (gas_shadow_cenv c) es = alloc_limits_exprs c es) /\
  (!c e. alloc_limits_opt (gas_shadow_cenv c) e = alloc_limits_opt c e) /\
  (!c kes. alloc_limits_named_exprs (gas_shadow_cenv c) kes =
           alloc_limits_named_exprs c kes)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >> rw[alloc_limits_expr_def]
QED

Theorem gas_shadow_cenv_alloc_limits_assignment[simp]:
  (!c g. alloc_limits_assignment (gas_shadow_cenv c) g =
         alloc_limits_assignment c g) /\
  (!c gs. alloc_limits_assignments (gas_shadow_cenv c) gs =
          alloc_limits_assignments c gs)
Proof
  ho_match_mp_tac alloc_limits_assignment_ind >> rw[alloc_limits_assignment_def]
QED

Theorem gas_shadow_cenv_alloc_limits_reasons[simp]:
  (!c it. alloc_limits_iterator (gas_shadow_cenv c) it =
          alloc_limits_iterator c it) /\
  (!c r. alloc_limits_assert (gas_shadow_cenv c) r = alloc_limits_assert c r) /\
  (!c r. alloc_limits_raise (gas_shadow_cenv c) r = alloc_limits_raise c r)
Proof
  rpt conj_tac >> gen_tac >> Cases >>
  simp[alloc_limits_iterator_def, alloc_limits_assert_def,
       alloc_limits_raise_def]
QED

Theorem gas_shadow_cenv_alloc_limits_stmt[simp]:
  (!c s. alloc_limits_stmt (gas_shadow_cenv c) s = alloc_limits_stmt c s) /\
  (!c ss. alloc_limits_stmts (gas_shadow_cenv c) ss = alloc_limits_stmts c ss)
Proof
  ho_match_mp_tac alloc_limits_stmt_ind >> rw[alloc_limits_stmt_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem gas_shadow_fn_allocs_ok:
  !tops m n r f a d t b.
    fn_allocs_ok (MAP gas_shadow_toplevel tops)
      (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b) =
    fn_allocs_ok tops (m,n,r,f,a,d,t,b)
Proof
  simp[fn_allocs_ok_def, gas_shadow_alloc_limits_expr, gas_shadow_alloc_limits_stmt]
QED

Theorem gas_shadow_external_return_buffer_ok:
  !p. external_return_buffer_ok (gas_shadow_external_package p) =
    external_return_buffer_ok p
Proof
  gen_tac >> PairCases_on `p` >>
  simp[gas_shadow_external_package_def, external_return_buffer_ok_def,
       gas_shadow_stmt_valued_return]
QED

Theorem gas_shadow_every_fn_allocs_ok:
  !fs tops.
    EVERY (fn_allocs_ok (MAP gas_shadow_toplevel tops))
      (MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fs) =
    EVERY (fn_allocs_ok tops) fs
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[gas_shadow_fn_allocs_ok]
QED

Theorem gas_shadow_fallback_fn_allocs_ok:
  !fb tops.
    EVERY (fn_allocs_ok (MAP gas_shadow_toplevel tops))
      (case OPTION_MAP (\(m,n,r,f,a,d,t,b). (m,n,r,f,a,MAP gas_shadow_expr d,t,MAP gas_shadow_stmt b)) fb of
         NONE => [] | SOME f => [f]) =
    EVERY (fn_allocs_ok tops) (case fb of NONE => [] | SOME f => [f])
Proof
  Cases >> simp[] >> rpt gen_tac >> PairCases_on `x` >>
  simp[gas_shadow_fn_allocs_ok]
QED

Theorem gas_shadow_every_external_return_buffer_ok:
  !ps. EVERY external_return_buffer_ok (MAP gas_shadow_external_package ps) =
    EVERY external_return_buffer_ok ps
Proof
  Induct >> simp[gas_shadow_external_return_buffer_ok]
QED
