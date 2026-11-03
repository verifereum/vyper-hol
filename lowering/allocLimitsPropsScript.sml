(*
 * What the lowering's allocation-limit check (allocLimits, compileVyper's
 * fn_allocs_ok) gives the proofs.
 *
 * TOP-LEVEL:
 *   alloc_limits_struct_fields  -- the check reads only the struct sizes
 *   alloc_limits_stmts_exists   -- alloc_limits_expr of every expression of
 *                                  a body, as supported_stmts_expr_exists
 *                                  traverses it
 *   fn_allocs_ok_body           -- that, and the parameters' and declared
 *                                  locals' sizes, of a function the runtime
 *                                  unit lowers, in any compile env with its
 *                                  struct sizes
 *)
Theory allocLimitsProps
Ancestors
  allocLimits compileVyper compileEnv supportedExprTraverse
  supportedStmtTraverse vyperAST list

Theorem type_memory_bytes_struct_fields:
  !c ty c'. c'.ce_struct_fields = c.ce_struct_fields ==>
            type_memory_bytes c' ty = type_memory_bytes c ty
Proof
  recInduct type_memory_bytes_ind >> rw[type_memory_bytes_def] >>
  AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

Theorem type_memory_bytes_frame:
  !c c'. c'.ce_struct_fields = c.ce_struct_fields ==>
         type_memory_bytes c' = type_memory_bytes c
Proof
  rw[FUN_EQ_THM] >> irule type_memory_bytes_struct_fields >> simp[]
QED

Theorem lowered_value_type_struct_fields:
  !c e c'. c'.ce_struct_fields = c.ce_struct_fields ==>
           lowered_value_type c' e = lowered_value_type c e
Proof
  ho_match_mp_tac exprLoweringTheory.lowered_value_type_ind >> rpt strip_tac >>
  gvs[exprLoweringTheory.lowered_value_type_def]
QED

Theorem ext_call_alloc_ok_struct_fields:
  !c ct es c'. c'.ce_struct_fields = c.ce_struct_fields ==>
               ext_call_alloc_ok c' ct es = ext_call_alloc_ok c ct es
Proof
  ho_match_mp_tac ext_call_alloc_ok_ind >> rpt strip_tac >>
  drule type_memory_bytes_frame >> strip_tac >>
  `lowered_value_type c' = lowered_value_type c` by
    (simp[FUN_EQ_THM] >> metis_tac[lowered_value_type_struct_fields]) >>
  gvs[ext_call_alloc_ok_def]
QED

Theorem alloc_limits_struct_fields:
  (!c e c'. c'.ce_struct_fields = c.ce_struct_fields ==>
            alloc_limits_expr c' e = alloc_limits_expr c e) /\
  (!c tgt c'. c'.ce_struct_fields = c.ce_struct_fields ==>
              alloc_limits_target c' tgt = alloc_limits_target c tgt) /\
  (!c es c'. c'.ce_struct_fields = c.ce_struct_fields ==>
             alloc_limits_exprs c' es = alloc_limits_exprs c es) /\
  (!c opt c'. c'.ce_struct_fields = c.ce_struct_fields ==>
              alloc_limits_opt c' opt = alloc_limits_opt c opt) /\
  (!c kes c'. c'.ce_struct_fields = c.ce_struct_fields ==>
              alloc_limits_named_exprs c' kes = alloc_limits_named_exprs c kes)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> drule type_memory_bytes_frame >> strip_tac >>
  drule ext_call_alloc_ok_struct_fields >> strip_tac >>
  simp[alloc_limits_expr_def, type_alloc_ok_def]
QED

Theorem alloc_limits_expr_exists:
  (!cenv e. alloc_limits_expr cenv e ==>
            ~supported_expr_exists (\e. ~alloc_limits_expr cenv e) e) /\
  (!cenv tgt. alloc_limits_target cenv tgt ==>
              ~supported_target_exists (\e. ~alloc_limits_expr cenv e) tgt) /\
  (!cenv es. alloc_limits_exprs cenv es ==>
             ~supported_exprs_exists (\e. ~alloc_limits_expr cenv e) es) /\
  (!cenv opt. alloc_limits_opt cenv opt ==>
              ~supported_opt_exists (\e. ~alloc_limits_expr cenv e) opt) /\
  (!cenv kes. alloc_limits_named_exprs cenv kes ==>
              ~supported_fields_exists (\e. ~alloc_limits_expr cenv e) kes)
Proof
  ho_match_mp_tac alloc_limits_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> gvs[alloc_limits_expr_def, supported_expr_exists_def]
QED

Theorem alloc_limits_assignment_exists:
  (!cenv g. alloc_limits_assignment cenv g ==>
            ~supported_assignment_exists (\e. ~alloc_limits_expr cenv e) g) /\
  (!cenv gs. alloc_limits_assignments cenv gs ==>
             ~supported_assignments_exists (\e. ~alloc_limits_expr cenv e) gs)
Proof
  ho_match_mp_tac alloc_limits_assignment_ind >>
  rw[alloc_limits_assignment_def, supported_assignment_exists_def] >>
  drule (cj 2 alloc_limits_expr_exists) >> simp[]
QED

Theorem alloc_limits_iterator_exists:
  !cenv it. alloc_limits_iterator cenv it ==>
            ~supported_iterator_exists (\e. ~alloc_limits_expr cenv e) it
Proof
  Cases_on `it` >>
  rw[alloc_limits_iterator_def, supported_iterator_exists_def] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

Theorem alloc_limits_assert_exists:
  !cenv r. alloc_limits_assert cenv r ==>
           ~supported_assert_exists (\e. ~alloc_limits_expr cenv e) r
Proof
  Cases_on `r` >>
  rw[alloc_limits_assert_def, supported_assert_exists_def,
     GSYM supported_exprs_exists_every] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

Theorem alloc_limits_raise_exists:
  !cenv r. alloc_limits_raise cenv r ==>
           ~supported_raise_exists (\e. ~alloc_limits_expr cenv e) r
Proof
  Cases_on `r` >>
  rw[alloc_limits_raise_def, supported_raise_exists_def,
     GSYM supported_exprs_exists_every] >>
  imp_res_tac alloc_limits_expr_exists >> simp[]
QED

Theorem alloc_limits_stmts_exists:
  (!cenv s. alloc_limits_stmt cenv s ==>
            ~supported_stmt_expr_exists (\e. ~alloc_limits_expr cenv e) s) /\
  (!cenv ss. alloc_limits_stmts cenv ss ==>
             ~supported_stmts_expr_exists (\e. ~alloc_limits_expr cenv e) ss)
Proof
  ho_match_mp_tac alloc_limits_stmt_ind >>
  rw[alloc_limits_stmt_def, supported_stmt_expr_exists_def] >>
  imp_res_tac alloc_limits_expr_exists >>
  imp_res_tac alloc_limits_assignment_exists >>
  imp_res_tac alloc_limits_iterator_exists >>
  imp_res_tac alloc_limits_assert_exists >>
  imp_res_tac alloc_limits_raise_exists >> simp[]
QED

(* The other checks read only the struct sizes too. *)
Theorem alloc_limits_assignment_struct_fields:
  (!c g c'. c'.ce_struct_fields = c.ce_struct_fields ==>
            alloc_limits_assignment c' g = alloc_limits_assignment c g) /\
  (!c gs c'. c'.ce_struct_fields = c.ce_struct_fields ==>
             alloc_limits_assignments c' gs = alloc_limits_assignments c gs)
Proof
  ho_match_mp_tac alloc_limits_assignment_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >> gvs[alloc_limits_assignment_def] >>
  metis_tac[alloc_limits_struct_fields]
QED

Theorem alloc_limits_frame:
  !c c'. c'.ce_struct_fields = c.ce_struct_fields ==>
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

(* A statement's check reads the struct sizes and, for a log, the events. *)
Theorem alloc_limits_stmt_struct_fields:
  (!c s c'. c'.ce_struct_fields = c.ce_struct_fields /\
            c'.ce_event_info = c.ce_event_info ==>
            alloc_limits_stmt c' s = alloc_limits_stmt c s) /\
  (!c ss c'. c'.ce_struct_fields = c.ce_struct_fields /\
             c'.ce_event_info = c.ce_event_info ==>
             alloc_limits_stmts c' ss = alloc_limits_stmts c ss)
Proof
  ho_match_mp_tac alloc_limits_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> drule alloc_limits_frame >> strip_tac >>
  gvs[alloc_limits_stmt_def, log_alloc_ok_def]
QED

(* A function the runtime unit lowers (lower_vyper_runtime_unit_allocs_ok)
   has its parameters' sizes, alloc_limits_expr of its body's expressions,
   its locals' sizes and its return type's size below the limit in every compile env
   with the program's struct sizes and events: build_compile_env's, and the
   packaged functions'. *)
Theorem fn_allocs_ok_body:
  !tops mut nr rr fname fargs dflts ret ss cenv.
    fn_allocs_ok tops (mut, nr, rr, fname, fargs, dflts, ret, ss) /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) ==>
    EVERY (\(_,ty). type_memory_bytes cenv ty < 2 ** 64) fargs /\
    alloc_limits_exprs cenv dflts /\ alloc_limits_stmts cenv ss /\
    ~supported_stmts_expr_exists (\e. ~alloc_limits_expr cenv e) ss /\
    type_memory_bytes cenv ret < 2 ** 64
Proof
  rpt gen_tac >> strip_tac >> gvs[fn_allocs_ok_def] >>
  qabbrev_tac `c = build_compile_env tops Internal mut fname fargs ret ss F` >>
  `cenv.ce_struct_fields = c.ce_struct_fields` by
    simp[Abbr `c`, build_compile_env_ce_struct_fields] >>
  `cenv.ce_event_info = c.ce_event_info` by
    (simp[Abbr `c`, build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  drule alloc_limits_frame >> strip_tac >>
  `alloc_limits_stmts cenv ss` by
    metis_tac[alloc_limits_stmt_struct_fields] >>
  gvs[] >> irule (cj 2 alloc_limits_stmts_exists) >> simp[]
QED
