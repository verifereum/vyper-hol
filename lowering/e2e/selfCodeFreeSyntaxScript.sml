(* Syntax boundaries for transaction-code independence. *)
Theory selfCodeFreeSyntax
Ancestors
  e2eProducers supportedExprTraverse supportedStmtTraverse
  exprLowering vyperInterpreter vyperGetter vyperContext vyperAST list sorting

val _ = Parse.hide "body";

Theorem build_getter_occurrence:
  !e kt vt n args ret exp p.
    (!ty id. ~p (Name ty id)) /\
    (!ty base key. ~p (Subscript ty base key)) /\
    build_getter e kt vt n = (args,ret,exp) ==>
    (supported_expr_exists p exp = supported_expr_exists p e)
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >>
  simp[Once build_getter_def] >> rw[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[supported_expr_exists_def] >> metis_tac[]
QED

Theorem getter_self_code_free:
  ~supported_expr_exists is_self_code ne /\
  getter nr ne kt vt = (mut,nr',args,dflts,ret,body) ==>
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body
Proof
  rw[getter_def] >> pairarg_tac >>
  gvs[supported_expr_exists_def, supported_stmt_expr_exists_def] >>
  `supported_expr_exists is_self_code exp =
   supported_expr_exists is_self_code ne` suffices_by simp[] >>
  irule build_getter_occurrence >> simp[is_self_code_def] >>
  goal_assum (drule_at Any)
QED

Theorem lookup_function_self_code_free:
  !src name vis ts mut nr args dflts ret body.
    ~program_reads_self_code ts /\
    lookup_function src name vis ts = SOME (mut,nr,args,dflts,ret,body) ==>
    ~supported_exprs_exists is_self_code dflts /\
    ~supported_stmts_expr_exists is_self_code body
Proof
  recInduct lookup_function_ind >>
  rw[lookup_function_def, program_reads_self_code_def,
     supported_expr_exists_def, supported_stmt_expr_exists_def] >>
  gvs[AllCaseEqs(), is_self_code_def] >>
  imp_res_tac getter_self_code_free >>
  gvs[supported_expr_exists_def, is_self_code_def]
QED

Theorem lookup_callable_function_self_code_free:
  ~program_reads_self_code ts /\
  lookup_callable_function deploy name ts = SOME (mut,nr,args,dflts,ret,body) ==>
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body
Proof
  rw[lookup_callable_function_def, AllCaseEqs()] >>
  metis_tac[lookup_function_self_code_free]
QED

Theorem lookup_exported_function_self_code_free:
  (!sid ts. get_module_code cx sid = SOME ts ==>
     ~program_reads_self_code ts) /\
  lookup_exported_function cx am name = SOME (mut,nr,args,dflts,ret,body) ==>
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body
Proof
  rw[lookup_exported_function_def, get_self_code_def, AllCaseEqs()] >>
  metis_tac[lookup_function_self_code_free]
QED

Theorem self_code_free_slice_source:
  ~supported_expr_exists is_self_code (Builtin ty bt es) /\
  code_slice_source bt es = SOME (ct,addr) ==>
  ~is_self_addr addr /\
  ~supported_exprs_exists is_self_code (TL es) /\
  ~supported_exprs_exists is_self_code [addr]
Proof
  rw[code_slice_source_SOME, supported_expr_exists_def] >>
  gvs[supported_expr_exists_def] >>
  Cases_on `addr` >>
  gvs[is_self_addr_def, is_self_code_def] >>
  rename1 `Builtin _ b xs` >> Cases_on `b` >>
  gvs[is_self_addr_def, is_self_code_def] >>
  rename1 `Env env` >> Cases_on `env` >>
  gvs[is_self_addr_def, is_self_code_def] >>
  Cases_on `xs` >> gvs[is_self_addr_def, is_self_code_def]
QED

Theorem supported_exprs_exclusion_sublist:
  (!e. MEM e xs ==> MEM e ys) /\ ~supported_exprs_exists p ys ==>
  ~supported_exprs_exists p xs
Proof
  simp[supported_exprs_exists_every, EXISTS_MEM] >> metis_tac[]
QED

Theorem supported_exprs_exclusion_TAKE:
  ~supported_exprs_exists p es ==> ~supported_exprs_exists p (TAKE n es)
Proof
  strip_tac >> irule supported_exprs_exclusion_sublist >>
  qexists `es` >> simp[] >> metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem supported_exprs_exclusion_DROP:
  ~supported_exprs_exists p es ==> ~supported_exprs_exists p (DROP n es)
Proof
  strip_tac >> irule supported_exprs_exclusion_sublist >>
  qexists `es` >> simp[] >> metis_tac[rich_listTheory.MEM_DROP_IMP]
QED

Theorem supported_exprs_exclusion_TL:
  ~supported_exprs_exists p es ==> ~supported_exprs_exists p (TL es)
Proof
  Cases_on `es` >> simp[supported_expr_exists_def]
QED

Theorem supported_exprs_exclusion_custom_error:
  order_custom_error_args params err = SOME es /\
  ~supported_exprs_exists p (custom_error_exprs err) ==>
  ~supported_exprs_exists p es
Proof
  strip_tac >> drule order_custom_error_args_perm >> strip_tac >>
  irule supported_exprs_exclusion_sublist >>
  qexists `custom_error_exprs err` >> simp[] >> metis_tac[PERM_MEM_EQ]
QED
