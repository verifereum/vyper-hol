(* Transfer the program's self-code exclusion through function lookup,
   including the implicit public getters. *)
Theory callCodeLookup
Ancestors
  e2eProducers vyperInterpreter vyperGetter vyperAST exprLowering
  supportedStmtTraverse supportedExprTraverse list pair

Theorem build_getter_no_self_code[local]:
  !e kt vt n.
    ~supported_expr_exists is_self_code e ==>
    ~supported_expr_exists is_self_code (SND (SND (build_getter e kt vt n)))
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >>
  disch_tac >> disch_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >>
  gvs[supported_expr_exists_def, is_self_code_def] >>
  pairarg_tac >> gvs[] >> metis_tac[pairTheory.SND]
QED

Theorem getter_no_self_code[local]:
  getter nr e kt vt = (mut,nr',args,ds,rt,ss) /\
  ~supported_expr_exists is_self_code e ==>
  ~supported_exprs_exists is_self_code ds /\
  ~supported_stmts_expr_exists is_self_code ss
Proof
  simp[getter_def] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def] >>
  metis_tac[build_getter_no_self_code, pairTheory.SND]
QED

Theorem lookup_function_no_self_code:
  !tops sid name vis mut nr args ds rt ss.
    ~program_reads_self_code tops /\
    lookup_function sid name vis tops = SOME (mut,nr,args,ds,rt,ss) ==>
    ~supported_exprs_exists is_self_code ds /\
    ~supported_stmts_expr_exists is_self_code ss
Proof
  Induct_on `tops`
  >- (rpt gen_tac >> Cases_on `vis` >>
      simp[lookup_function_def, supported_stmt_expr_exists_def,
           supported_expr_exists_def]) >>
  Cases >> rpt gen_tac >> Cases_on `vis` >>
  simp[lookup_function_def, AllCaseEqs()] >>
  strip_tac >>
  `~program_reads_self_code tops` by
    gvs[program_reads_self_code_def] >>
  gvs[lookup_function_def, AllCaseEqs()] >>
  rpt (first_x_assum drule_all >> strip_tac) >>
  gvs[program_reads_self_code_def] >>
  Cases_on `v` >>
  gvs[lookup_function_def, AllCaseEqs(), supported_stmt_expr_exists_def,
      supported_expr_exists_def, is_self_code_def] >>
  rpt (first_x_assum drule >> strip_tac) >> gvs[] >>
  drule (pp (Pos hd) getter_no_self_code) >>
  simp[supported_expr_exists_def, is_self_code_def]
QED
