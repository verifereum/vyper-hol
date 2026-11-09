(*
 * What the lowering's allocation-limit check (allocLimits, compileVyper's
 * fn_allocs_ok) gives the proofs.
 *
 * TOP-LEVEL:
 *   alloc_limits_struct_fields  -- the check reads only the struct sizes
 *   alloc_limits_stmt_exists    -- alloc_limits_expr of every expression of
 *                                  a statement that holds no block,
 *                                  but a slice's .code
 *                                  source (is_extcode), which the check skips
 *   fn_allocs_ok_body           -- alloc_limits_stmts of a function body the
 *                                  runtime unit lowers, and the parameters'
 *                                  sizes, in any compile env that agrees
 *                                  with its own (alloc_env_agree)
 *)
Theory allocLimitsProps
Ancestors
  allocLimits compileVyper compileEnv supportedExprTraverse
  supportedStmtTraverse vyperAST list

Theorem lowered_value_type_struct_fields:
  !c e c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type ==>
           lowered_value_type c' e = lowered_value_type c e
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >> rpt strip_tac >>
  gvs[exprLoweringTheory.lowered_value_type_def]
QED

Theorem ext_call_alloc_ok_struct_fields:
  !c ct es c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type ==>
               ext_call_alloc_ok c' ct es = ext_call_alloc_ok c ct es
Proof
  ho_match_mp_tac ext_call_alloc_ok_ind >> rpt strip_tac >>
  drule type_memory_bytes_frame >> strip_tac >>
  `lowered_value_type c' = lowered_value_type c` by
    (simp[FUN_EQ_THM] >> metis_tac[lowered_value_type_struct_fields]) >>
  gvs[ext_call_alloc_ok_def]
QED

Theorem target_subscript_overlap_frame:
  !c c' bt idx.
    c'.ce_struct_fields = c.ce_struct_fields /\ c'.ce_modules = c.ce_modules /\
    c'.ce_var_type = c.ce_var_type /\ c'.ce_hashmap_info = c.ce_hashmap_info /\
    c'.ce_module_var_type = c.ce_module_var_type ==>
    target_subscript_overlap c' bt idx = target_subscript_overlap c bt idx
Proof
  rw[] >>
  `!bt. target_place_type c' bt = target_place_type c bt` by
    (gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
     Cases_on `bt` >> gvs[target_place_type_def]) >>
  `!bt. target_through_dynarray c' bt = target_through_dynarray c bt` by
    (gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
     Cases_on `bt` >> gvs[target_through_dynarray_def]) >>
  simp[target_subscript_overlap_def]
QED

Theorem alloc_limits_struct_fields:
  (!c e c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
            alloc_limits_expr c' e = alloc_limits_expr c e) /\
  (!c tgt c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
              alloc_limits_target c' tgt = alloc_limits_target c tgt) /\
  (!c es c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
             alloc_limits_exprs c' es = alloc_limits_exprs c es) /\
  (!c opt c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
              alloc_limits_opt c' opt = alloc_limits_opt c opt) /\
  (!c kes c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
              alloc_limits_named_exprs c' kes = alloc_limits_named_exprs c kes)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> drule type_memory_bytes_frame >> strip_tac >>
  drule ext_call_alloc_ok_struct_fields >> strip_tac >>
  drule_all target_subscript_overlap_frame >> strip_tac >>
  simp[alloc_limits_expr_def, type_alloc_ok_def]
QED

(* A slice's .code source, which the check skips for its address, is
   exempt from the per-subexpression fact; its address is not. *)
Theorem supported_exprs_exists_extcode[local]:
  !Q es. es <> [] /\ is_extcode (HD es) ==>
         (supported_exprs_exists (\e. ~is_extcode e /\ ~Q e) es <=>
          supported_exprs_exists (\e. ~is_extcode e /\ ~Q e)
            (extcode_addr_expr (HD es) :: TL es))
Proof
  gen_tac >> Cases >> simp[] >> rename1 `is_extcode h` >>
  Cases_on `h` >> simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `Builtin _ b l` >> Cases_on `b` >>
  simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `Acc a` >> Cases_on `a` >> simp[exprLoweringTheory.is_extcode_def] >>
  Cases_on `l` >> simp[exprLoweringTheory.is_extcode_def] >>
  rename1 `_ :: tl` >> Cases_on `tl` >>
  simp[exprLoweringTheory.is_extcode_def,
       exprLoweringTheory.extcode_addr_expr_def, supported_expr_exists_def]
QED

Theorem alloc_limits_expr_exists:
  (!cenv e. alloc_limits_expr cenv e ==>
            ~supported_expr_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) e) /\
  (!cenv tgt. alloc_limits_target cenv tgt ==>
              ~supported_target_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) tgt) /\
  (!cenv es. alloc_limits_exprs cenv es ==>
             ~supported_exprs_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) es) /\
  (!cenv opt. alloc_limits_opt cenv opt ==>
              ~supported_opt_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) opt) /\
  (!cenv kes. alloc_limits_named_exprs cenv kes ==>
              ~supported_fields_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) kes)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> gvs[alloc_limits_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `alloc_limits_exprs _ (if _ then _ else _)` mp_tac >>
  IF_CASES_TAC >> gvs[supported_exprs_exists_extcode]
QED

Theorem alloc_limits_assignment_exists:
  (!cenv g. alloc_limits_assignment cenv g ==>
            ~supported_assignment_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) g) /\
  (!cenv gs. alloc_limits_assignments cenv gs ==>
             ~supported_assignments_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) gs)
Proof
  ho_match_mp_tac alloc_limits_assignment_ind >>
  rw[alloc_limits_assignment_def, supported_assignment_exists_def] >>
  drule (cj 2 alloc_limits_expr_exists) >> simp[]
QED

Theorem alloc_limits_iterator_exists:
  !cenv it. alloc_limits_iterator cenv it ==>
            ~supported_iterator_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) it
Proof
  Cases_on `it` >>
  rw[alloc_limits_iterator_def, supported_iterator_exists_def] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

Theorem alloc_limits_assert_exists:
  !cenv r. alloc_limits_assert cenv r ==>
           ~supported_assert_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) r
Proof
  Cases_on `r` >>
  rw[alloc_limits_assert_def, supported_assert_exists_def,
     GSYM supported_exprs_exists_every] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

Theorem alloc_limits_raise_exists:
  !cenv r. alloc_limits_raise cenv r ==>
           ~supported_raise_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) r
Proof
  Cases_on `r` >>
  rw[alloc_limits_raise_def, supported_raise_exists_def,
     GSYM supported_exprs_exists_every] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

(* A block checks its statements under the local types compile_stmts
   threads to them (decl_var_type), so only a statement that holds no block
   checks every expression under cenv itself. *)
Theorem alloc_limits_stmt_exists:
  !cenv s.
    alloc_limits_stmt cenv s /\ (!c ss1 ss2. s <> If c ss1 ss2) /\
    (!id ty it n body. s <> For id ty it n body) ==>
    ~supported_stmt_expr_exists (\e. ~is_extcode e /\ ~alloc_limits_expr cenv e) s
Proof
  gen_tac >> Cases >>
  rw[alloc_limits_stmt_def, supported_stmt_expr_exists_def] >>
  imp_res_tac alloc_limits_expr_exists >>
  imp_res_tac alloc_limits_assignment_exists >>
  imp_res_tac alloc_limits_iterator_exists >>
  imp_res_tac alloc_limits_assert_exists >>
  imp_res_tac alloc_limits_raise_exists >> simp[]
QED

(* The other checks read only the struct sizes too. *)
Theorem alloc_limits_assignment_struct_fields:
  (!c g c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
            alloc_limits_assignment c' g = alloc_limits_assignment c g) /\
  (!c gs c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
             alloc_limits_assignments c' gs = alloc_limits_assignments c gs)
Proof
  ho_match_mp_tac alloc_limits_assignment_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >> gvs[alloc_limits_assignment_def] >>
  metis_tac[alloc_limits_struct_fields]
QED

Theorem alloc_limits_frame:
  !c c'. c'.ce_struct_fields = c.ce_struct_fields /\
              c'.ce_func_return_type = c.ce_func_return_type /\
              c'.ce_modules = c.ce_modules /\ c'.ce_var_type = c.ce_var_type /\
              c'.ce_hashmap_info = c.ce_hashmap_info /\
              c'.ce_module_var_type = c.ce_module_var_type ==>
    type_memory_bytes c' = type_memory_bytes c /\
    alloc_limits_expr c' = alloc_limits_expr c /\
    alloc_limits_target c' = alloc_limits_target c /\
    alloc_limits_exprs c' = alloc_limits_exprs c /\
    alloc_limits_opt c' = alloc_limits_opt c /\
    alloc_limits_assignment c' = alloc_limits_assignment c /\
    alloc_limits_iterator c' = alloc_limits_iterator c /\
    alloc_limits_assert c' = alloc_limits_assert c /\
    alloc_limits_raise c' = alloc_limits_raise c
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes c' = type_memory_bytes c` by
    (irule type_memory_bytes_frame >> simp[]) >>
  `alloc_limits_expr c' = alloc_limits_expr c /\
   alloc_limits_target c' = alloc_limits_target c /\
   alloc_limits_exprs c' = alloc_limits_exprs c /\
   alloc_limits_opt c' = alloc_limits_opt c /\
   alloc_limits_assignment c' = alloc_limits_assignment c` by
    (rpt conj_tac >> simp[FUN_EQ_THM] >>
     metis_tac[alloc_limits_struct_fields,
               alloc_limits_assignment_struct_fields]) >>
  asm_rewrite_tac[] >> simp[FUN_EQ_THM] >> rpt conj_tac >> Cases >>
  gvs[alloc_limits_iterator_def, alloc_limits_assert_def,
      alloc_limits_raise_def]
QED

(* The fields of the compile env an assignment's buffer check reads. *)
Definition alloc_env_agree_def:
  alloc_env_agree c c' <=>
    c'.ce_struct_fields = c.ce_struct_fields /\
    c'.ce_event_info = c.ce_event_info /\
    c'.ce_module_vars = c.ce_module_vars /\
    c'.ce_hashmap_info = c.ce_hashmap_info /\
    c'.ce_module_var_type = c.ce_module_var_type /\
    c'.ce_func_return_type = c.ce_func_return_type /\
    c'.ce_modules = c.ce_modules /\
    c'.ce_var_type = c.ce_var_type
End

Theorem alloc_env_agree_var_type:
  !c c' f. alloc_env_agree c c' ==>
    alloc_env_agree (c with ce_var_type updated_by f)
                    (c' with ce_var_type updated_by f)
Proof
  rw[alloc_env_agree_def]
QED

Theorem alloc_env_agree_decl_var_type:
  !c c' s. alloc_env_agree c c' ==>
    alloc_env_agree (decl_var_type c s) (decl_var_type c' s)
Proof
  ntac 2 gen_tac >> Cases >> rpt strip_tac >>
  gvs[decl_var_type_def, alloc_env_agree_var_type]
QED

Theorem target_store_place_frame:
  !c c' bt.
    c'.ce_struct_fields = c.ce_struct_fields /\
    c'.ce_module_vars = c.ce_module_vars /\
    c'.ce_hashmap_info = c.ce_hashmap_info /\
    c'.ce_module_var_type = c.ce_module_var_type ==>
    target_store_place c' bt = target_store_place c bt
Proof
  ntac 2 gen_tac >> strip_tac >>
  measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> gvs[target_store_place_def]
QED

Theorem lowered_value_type_frame:
  !c e c'. c'.ce_struct_fields = c.ce_struct_fields /\
           c'.ce_func_return_type = c.ce_func_return_type ==>
           lowered_value_type c' e = lowered_value_type c e
Proof
  recInduct exprLoweringTheory.lowered_value_type_ind >>
  simp[exprLoweringTheory.lowered_value_type_def]
QED

Theorem assign_alloc_ok_frame:
  !c c' bt e. alloc_env_agree c c' ==>
    assign_alloc_ok c' bt e = assign_alloc_ok c bt e
Proof
  rw[alloc_env_agree_def, assign_alloc_ok_def] >>
  drule_all target_store_place_frame >> disch_then (qspec_then `bt` SUBST1_TAC) >>
  drule type_memory_bytes_frame >> strip_tac >>
  `lowered_value_type c' e = lowered_value_type c e` by
    (irule lowered_value_type_frame >> simp[]) >>
  simp[]
QED

(* A statement's check reads the struct sizes, for a log the events, and
   for an assignment's buffer the module's variables and the internal
   functions' return types. *)
Theorem alloc_limits_stmt_struct_fields:
  (!c s c'. alloc_env_agree c c' ==>
            alloc_limits_stmt c' s = alloc_limits_stmt c s) /\
  (!c ss c'. alloc_env_agree c c' ==>
             alloc_limits_stmts c' ss = alloc_limits_stmts c ss)
Proof
  ho_match_mp_tac alloc_limits_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> rename1 `alloc_env_agree c0 c1` >>
  drule assign_alloc_ok_frame >> strip_tac >>
  `!s. alloc_env_agree (decl_var_type c0 s) (decl_var_type c1 s)` by
    metis_tac[alloc_env_agree_decl_var_type] >>
  `!f. alloc_env_agree (c0 with ce_var_type updated_by f)
                       (c1 with ce_var_type updated_by f)` by
    metis_tac[alloc_env_agree_var_type] >>
  `!f. alloc_limits_expr (c1 with ce_var_type updated_by f) =
       alloc_limits_expr (c0 with ce_var_type updated_by f)` by
    (gen_tac >> irule (cj 2 alloc_limits_frame) >> gvs[alloc_env_agree_def]) >>
  `c1.ce_struct_fields = c0.ce_struct_fields /\
   c1.ce_func_return_type = c0.ce_func_return_type /\
   c1.ce_modules = c0.ce_modules /\ c1.ce_var_type = c0.ce_var_type /\
   c1.ce_hashmap_info = c0.ce_hashmap_info /\
   c1.ce_module_var_type = c0.ce_module_var_type /\
   c1.ce_event_info = c0.ce_event_info` by gvs[alloc_env_agree_def] >>
  drule_all alloc_limits_frame >> strip_tac >>
  gvs[alloc_limits_stmt_def, log_alloc_ok_def] >> metis_tac[]
QED

(* A target compile_get_target_ptr places in storage or transient storage
   has the place type target_store_place gives it. *)
Theorem compile_get_target_ptr_store_place:
  !cfn cenv bt sa r sb.
    compile_get_target_ptr cfn cenv bt sa = (r,sb) /\
    (FST (SND r) = SOME LocStorage \/ FST (SND r) = SOME LocTransient) ==>
    target_store_place cenv bt = SOME (SND (SND r))
Proof
  ntac 2 gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac >>
  simp[Once exprLoweringTheory.compile_get_target_ptr_def]
  >- (simp[target_store_place_def] >> BasicProvers.every_case_tac >> simp[comp_return_def] >> rpt strip_tac >> gvs[])
  >- (simp[target_store_place_def] >> BasicProvers.every_case_tac >> simp[comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[comp_bind_def] >>
  Cases_on `compile_get_target_ptr cfn cenv b sa` >>
  rename1 `_ = (rb, sm)` >> PairCases_on `rb` >>
  `(rb1 = SOME LocStorage \/ rb1 = SOME LocTransient) ==>
   target_store_place cenv b = SOME rb2` by
    (first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
     disch_then drule >> simp[])
  >- (simp[LET_THM] >>
      Cases_on `rb2`
      >- (simp[comp_bind_def, comp_return_def, LET_THM] >>
          rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def, LET_THM]) >>
          rpt strip_tac >> gvs[target_store_place_def]) >>
      Cases_on `x`
      >- (simp[comp_bind_def, comp_return_def, LET_THM] >>
          rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def, LET_THM]) >>
          rpt strip_tac >> gvs[target_store_place_def]) >>
      simp[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def, LET_THM]) >>
      rpt strip_tac >> gvs[target_store_place_def] >>
      Cases_on `t` >> simp[]) >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[target_store_place_def]
QED

(* A function the runtime unit lowers (lower_vyper_runtime_unit_allocs_ok)
   has its parameters' sizes, alloc_limits_stmts of its body (its locals'
   sizes and the expressions' buffers) and its return type's size below the
   limit in every compile env
   that agrees with build_compile_env's on the fields the check reads: the
   struct sizes, the events, the module's variables and the internal
   functions' return types. *)
Theorem fn_allocs_ok_body:
  !tops mut nr rr fname fargs dflts ret ss cenv.
    fn_allocs_ok tops (mut, nr, rr, fname, fargs, dflts, ret, ss) /\
    alloc_env_agree
      (build_compile_env tops Internal mut fname fargs ret ss F) cenv ==>
    EVERY (\(_,ty). type_memory_bytes cenv ty < 2 ** 64) fargs /\
    alloc_limits_exprs cenv dflts /\ alloc_limits_stmts cenv ss /\
    type_memory_bytes cenv ret < 2 ** 64
Proof
  rpt gen_tac >> strip_tac >> gvs[fn_allocs_ok_def] >>
  qabbrev_tac `c = build_compile_env tops Internal mut fname fargs ret ss F` >>
  `cenv.ce_struct_fields = c.ce_struct_fields /\
   cenv.ce_func_return_type = c.ce_func_return_type /\
   cenv.ce_modules = c.ce_modules /\ cenv.ce_var_type = c.ce_var_type /\
   cenv.ce_hashmap_info = c.ce_hashmap_info /\
   cenv.ce_module_var_type = c.ce_module_var_type` by gvs[alloc_env_agree_def] >>
  drule_all alloc_limits_frame >> strip_tac >>
  `alloc_limits_stmts cenv ss` by
    metis_tac[alloc_limits_stmt_struct_fields] >>
  gvs[]
QED
