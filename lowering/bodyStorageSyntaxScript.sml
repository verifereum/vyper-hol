(* Syntactic interfaces used by oracle storage preservation. *)
Theory bodyStorageSyntax
Ancestors
  list pair option supportedProgram supportedStmts supportedStmtTraverse
  supportedTargets supportedExprs supportedExprForms supportedExprTraverse
  supportedDecls supportedNames vyperAST vyperInterpreter vyperTypeCallGraph

Definition storage_internal_callee_def:
  storage_internal_callee tops c <=>
    IS_SOME (supported_function_decl tops c Internal)
End

Theorem storage_supported_internal_lookup:
  !ts ns name mut nr rr params dflts ret fn_body.
  supported_function_decl ts (ns,name) Internal =
    SOME (mut,nr,rr,params,dflts,ret,fn_body) ==>
  ns = NONE /\
  lookup_function NONE name Internal ts = SOME (mut,nr,params,dflts,ret,fn_body)
Proof
  Induct >> simp[supported_function_decl_def] >>
  Cases_on `h` >> rw[supported_function_decl_def,lookup_function_def] >>
  gvs[] >> TRY (Cases_on `v` >> gvs[lookup_function_def]) >> metis_tac[]
QED

Theorem storage_internal_callee_lookup:
  storage_internal_callee tops (src,fn) ==>
  src = NONE /\ IS_SOME (lookup_function NONE fn Internal tops)
Proof
  rw[storage_internal_callee_def,IS_SOME_EXISTS] >>
  qmatch_asmsub_rename_tac `supported_function_decl tops (src,fn) Internal = SOME decl` >>
  PairCases_on `decl` >> drule storage_supported_internal_lookup >>
  strip_tac >> gvs[]
QED

Theorem storage_lookup_declaration:
  !src name vis ts mut nr params dflts ret fn_body.
  lookup_function src name vis ts = SOME (mut,nr,params,dflts,ret,fn_body) /\
  (vis = Internal \/ vis = Deploy) ==>
  (nr = F /\ params = [] /\ dflts = [] /\ fn_body = []) \/
  ?rr. MEM (FunctionDecl vis mut nr rr name params dflts ret fn_body) ts
Proof
  ho_match_mp_tac lookup_function_ind >>
  rw[lookup_function_def] >> gvs[] >> metis_tac[]
QED

Theorem storage_no_internal_expr_calls:
  (!e. ~supported_expr_exists expr_internal_call_root e ==> int_calls_expr e = []) /\
  (!t. ~supported_target_exists expr_internal_call_root t ==> int_calls_target t = []) /\
  (!es. ~supported_exprs_exists expr_internal_call_root es ==> int_calls_exprs es = []) /\
  (!eo. ~supported_opt_exists expr_internal_call_root eo ==> int_calls_opt eo = []) /\
  (!kes. ~supported_fields_exists expr_internal_call_root kes ==> int_calls_named_exprs kes = [])
Proof
  ho_match_mp_tac int_calls_expr_ind >>
  rw[int_calls_expr_def,supported_expr_exists_def,expr_internal_call_root_def]
QED

Theorem storage_no_internal_assignment_calls[local]:
  (!g. ~supported_assignment_exists expr_internal_call_root g ==> int_calls_atarget g = []) /\
  (!gs. ~supported_assignments_exists expr_internal_call_root gs ==> int_calls_atargets gs = [])
Proof
  ho_match_mp_tac int_calls_atarget_ind >>
  rw[int_calls_atarget_def,supported_assignment_exists_def] >>
  metis_tac[storage_no_internal_expr_calls]
QED

Theorem storage_no_internal_iterator_calls[local]:
  ~supported_iterator_exists expr_internal_call_root it ==> int_calls_iterator it = []
Proof
  Cases_on `it` >> rw[supported_iterator_exists_def,int_calls_iterator_def] >>
  metis_tac[storage_no_internal_expr_calls]
QED

Theorem storage_no_internal_reason_calls[local]:
  (!r. ~supported_raise_exists expr_internal_call_root r ==> int_calls_raise_reason r = []) /\
  (!r. ~supported_assert_exists expr_internal_call_root r ==> int_calls_assert_reason r = [])
Proof
  conj_tac >> Cases >>
  rw[supported_raise_exists_def,supported_assert_exists_def,
     int_calls_raise_reason_def,int_calls_assert_reason_def] >>
  FIRST [drule (cj 1 storage_no_internal_expr_calls) >> simp[],
         irule (cj 3 storage_no_internal_expr_calls) >>
         simp[supported_exprs_exists_every]]
QED

Theorem storage_no_internal_stmt_calls:
  (!s. ~supported_stmt_expr_exists expr_internal_call_root s ==> int_calls_stmt s = []) /\
  (!ss. ~supported_stmts_expr_exists expr_internal_call_root ss ==> int_calls_stmts ss = [])
Proof
  ho_match_mp_tac int_calls_stmt_ind >>
  rw[int_calls_stmt_def,supported_stmt_expr_exists_def] >>
  imp_res_tac storage_no_internal_expr_calls >>
  imp_res_tac storage_no_internal_assignment_calls >>
  imp_res_tac storage_no_internal_iterator_calls >>
  imp_res_tac storage_no_internal_reason_calls >> gvs[]
QED

Theorem storage_pure_calls:
  (!tops e. supported_pure_expr tops e ==> int_calls_expr e = []) /\
  (!tops es. supported_pure_exprs tops es ==> int_calls_exprs es = []) /\
  (!tops e. supported_place_expr tops e ==> int_calls_expr e = [])
Proof
  `!x. expr_internal_call_root x ==> expr_effect_root x` by
    (Cases >> simp[expr_internal_call_root_def,expr_effect_root_def]) >>
  metis_tac[storage_no_internal_expr_calls,supported_pure_no_effect,
            supported_expr_exists_mono]
QED

Theorem storage_effect_calls[local]:
  (!tops e. supported_effect_expr tops e ==>
      EVERY (storage_internal_callee tops) (int_calls_expr e)) /\
  (!tops e. supported_effect_place_expr tops e ==>
      EVERY (storage_internal_callee tops) (int_calls_expr e))
Proof
  ho_match_mp_tac supported_effect_expr_ind >>
  rw[supported_effect_expr_def,int_calls_expr_def,storage_internal_callee_def] >>
  imp_res_tac storage_pure_calls >> gvs[]
QED

Theorem storage_expr_syntax:
  supported_expr tops e ==>
  ~supported_expr_exists expr_evm_run_root e /\
  EVERY (storage_internal_callee tops) (int_calls_expr e)
Proof
  strip_tac >> conj_tac
  >- metis_tac[supported_expr_no_evm_run,expr_has_evm_run_def] >>
  fs[supported_expr_def] >> imp_res_tac storage_pure_calls >>
  imp_res_tac storage_effect_calls >> gvs[]
QED

Theorem storage_target_info_syntax:
  !bt tops bindings vt.
  supported_target_info tops bindings bt = SOME vt ==>
  ~supported_target_exists expr_evm_run_root bt /\
  EVERY (storage_internal_callee tops) (int_calls_target bt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rw[supported_target_info_def,int_calls_expr_def,
     supported_expr_exists_def,AllCaseEqs()] >>
  imp_res_tac storage_expr_syntax >> gvs[] >>
  qmatch_asmsub_rename_tac `supported_target_info tops bindings child = SOME _` >>
  qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
  simp[expr_size_def] >> metis_tac[]
QED

Theorem storage_target_syntax:
  supported_target tops bindings bt ==>
  ~supported_target_exists expr_evm_run_root bt /\
  EVERY (storage_internal_callee tops) (int_calls_target bt)
Proof
  Cases_on `bt` >> rw[supported_target_def,AllCaseEqs(),
                      int_calls_expr_def,supported_expr_exists_def] >>
  Cases_on `b` >>
  gvs[int_calls_expr_def,supported_expr_exists_def] >>
  imp_res_tac storage_expr_syntax >> gvs[]
QED

Theorem storage_flat_targets_syntax[local]:
  !gs. EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt | TupleTarget _ => F) gs ==>
  ~supported_assignments_exists expr_evm_run_root gs /\
  EVERY (storage_internal_callee tops) (int_calls_atargets gs)
Proof
  Induct >> simp[int_calls_atarget_def,supported_assignment_exists_def] >>
  Cases_on `h` >> simp[] >> strip_tac >>
  drule_all storage_target_syntax >>
  gvs[int_calls_atarget_def,supported_assignment_exists_def]
QED

Theorem storage_assignment_syntax:
  supported_assignment tops bindings tgt e ==>
  ~supported_assignment_exists expr_evm_run_root tgt /\
  EVERY (storage_internal_callee tops) (int_calls_atarget tgt) /\
  ~supported_expr_exists expr_evm_run_root e /\
  EVERY (storage_internal_callee tops) (int_calls_expr e)
Proof
  Cases_on `tgt` >> rw[supported_assignment_def,AllCaseEqs()] >>
  imp_res_tac storage_expr_syntax >>
  imp_res_tac storage_target_syntax >> imp_res_tac storage_target_info_syntax >>
  imp_res_tac storage_flat_targets_syntax >>
  gvs[int_calls_atarget_def,supported_assignment_exists_def] >>
  qmatch_asmsub_rename_tac `supported_target_info tops bindings bt` >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  rename1 `supported_target_info tops bindings bt = SOME pt` >>
  Cases_on `pt` >> gvs[] >> drule_all storage_target_info_syntax >> simp[]
QED

Theorem storage_reason_syntax:
  supported_string_reason tops e ==>
  ~supported_expr_exists expr_evm_run_root e /\
  EVERY (storage_internal_callee tops) (int_calls_expr e)
Proof
  strip_tac >> Cases_on `e` >>
  gvs[supported_string_reason_def,supported_expr_def] >>
  TRY (rename1 `Literal ty lit` >> Cases_on `lit` >>
       gvs[supported_string_reason_def,int_calls_expr_def,supported_expr_exists_def,expr_evm_run_root_def]) >>
  metis_tac[storage_expr_syntax,supported_expr_def]
QED

Theorem storage_pure_expr_syntax[local]:
  supported_pure_expr tops e ==> ~supported_expr_exists expr_evm_run_root e
Proof
  metis_tac[storage_expr_syntax,supported_expr_def]
QED

Theorem storage_pure_exprs_syntax[local]:
  !es. supported_pure_exprs tops es ==>
    ~supported_exprs_exists expr_evm_run_root es /\
    EVERY (storage_internal_callee tops) (int_calls_exprs es)
Proof
  Induct >> simp[supported_pure_expr_def,supported_expr_exists_def,int_calls_expr_def] >>
  metis_tac[storage_expr_syntax,supported_expr_def]
QED

Theorem storage_aug_target_syntax[local]:
  supported_aug_target tops bindings bt ==>
  ~supported_target_exists expr_evm_run_root bt /\
  EVERY (storage_internal_callee tops) (int_calls_target bt)
Proof
  rw[supported_aug_target_def] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  Cases_on `x` >> gvs[] >> drule_all storage_target_info_syntax >> simp[]
QED

Theorem storage_append_target_syntax[local]:
  supported_append_target tops bt ==>
  ~supported_target_exists expr_evm_run_root bt /\
  EVERY (storage_internal_callee tops) (int_calls_target bt)
Proof
  Cases_on `bt` >> simp[supported_append_target_def,supported_expr_exists_def,int_calls_expr_def]
QED

Theorem storage_iterator_syntax[local]:
  supported_iterator tops ty it n ==>
  ~supported_iterator_exists expr_evm_run_root it /\
  EVERY (storage_internal_callee tops) (int_calls_iterator it)
Proof
  Cases_on `it`
  >- (Cases_on `e` >>
      simp[supported_iterator_exists_def,supported_expr_exists_def,int_calls_iterator_def,
           int_calls_expr_def,expr_evm_run_root_def,supported_iterator_def]) >>
  rename1 `supported_iterator tops ty (Range lo hi) n` >>
  Cases_on `lo` >> Cases_on `hi` >>
  rw[supported_iterator_def] >>
  imp_res_tac storage_pure_expr_syntax >> imp_res_tac storage_pure_calls >>
  gvs[supported_iterator_exists_def,int_calls_iterator_def,
      expr_evm_run_root_def,supported_expr_exists_def,int_calls_expr_def]
QED

Theorem storage_stmt_syntax:
  (!tops bindings s. supported_stmt tops bindings s ==>
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    EVERY (storage_internal_callee tops) (int_calls_stmt s)) /\
  (!tops bindings ss. supported_stmts tops bindings ss ==>
    ~supported_stmts_expr_exists expr_evm_run_root ss /\
    EVERY (storage_internal_callee tops) (int_calls_stmts ss))
Proof
  ho_match_mp_tac supported_stmt_ind >>
  rw[supported_stmt_def,int_calls_stmt_def,supported_stmt_expr_exists_def,
     int_calls_expr_def,supported_expr_exists_def] >>
  imp_res_tac storage_expr_syntax >> imp_res_tac storage_assignment_syntax >>
  imp_res_tac storage_target_syntax >>
  imp_res_tac storage_target_info_syntax >>
  imp_res_tac storage_aug_target_syntax >> imp_res_tac storage_append_target_syntax >>
  imp_res_tac storage_pure_expr_syntax >> imp_res_tac storage_pure_exprs_syntax >>
  imp_res_tac storage_iterator_syntax >> gvs[] >>
  TRY (Cases_on `reason` >>
       gvs[supported_raise_reason_def,supported_assert_reason_def,
           supported_raise_exists_def,supported_assert_exists_def,
           int_calls_raise_reason_def,int_calls_assert_reason_def] >>
       imp_res_tac storage_reason_syntax >> gvs[]) >>
  imp_res_tac storage_pure_calls >> gvs[supported_log_def] >>
  imp_res_tac storage_pure_exprs_syntax >> gvs[]
QED

Theorem storage_supported_lookup:
  supported_program tops /\
  lookup_function src name vis tops = SOME (mut,nr,params,dflts,ret,fn_body) /\
  (vis = Internal \/ vis = Deploy) ==>
  ~nr /\ dflts = [] /\
  (?bindings. supported_stmts tops bindings fn_body) /\
  ~supported_stmts_expr_exists expr_evm_run_root fn_body /\
  EVERY (storage_internal_callee tops) (int_calls_stmts fn_body) /\
  (vis = Internal ==> int_calls_stmts fn_body = [])
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  drule_all storage_lookup_declaration >> strip_tac
  >- gvs[supported_stmt_def,supported_stmt_expr_exists_def,int_calls_stmt_def] >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def,supported_declaration_body_def,
       supported_function_body_def] >> strip_tac >>
  imp_res_tac storage_stmt_syntax >> imp_res_tac storage_no_internal_stmt_calls >>
  gvs[NULL_EQ] >> imp_res_tac storage_no_internal_stmt_calls >> metis_tac[]
QED

Theorem storage_supported_callable_lookup:
  supported_program tops /\
  lookup_callable_function in_deploy fn tops = SOME (mut,nr,params,dflts,ret,fn_body) ==>
  ~nr /\ dflts = [] /\ (?bindings. supported_stmts tops bindings fn_body) /\
  ~supported_stmts_expr_exists expr_evm_run_root fn_body /\
  EVERY (storage_internal_callee tops) (int_calls_stmts fn_body)
Proof
  rw[lookup_callable_function_def,AllCaseEqs()] >>
  drule_at (Pat `lookup_function _ _ _ _ = _`) storage_supported_lookup >> simp[]
QED
