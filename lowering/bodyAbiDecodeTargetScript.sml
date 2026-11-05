(* A function body that lookup_function returns has its ABI-decode targets
   among the program's: the premise that body_stmt(s)_ok and
   body_stmts_sim take, discharged for the frames that run a looked-up
   function's body. *)
Theory bodyAbiDecodeTarget
Ancestors
  supportedProgram supportedStmtTraverse supportedExprTraverse
  vyperGetter vyperInterpreter vyperAST

Theorem build_getter_abi_decode_target[local]:
  !e kt vt n args ret exp target.
    build_getter e kt vt n = (args,ret,exp) /\
    supported_expr_exists (expr_abi_decode_target_root target) exp ==>
    supported_expr_exists (expr_abi_decode_target_root target) e
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >>
  TRY (disch_tac) >> rpt gen_tac >>
  simp[Once build_getter_def] >> rw[] >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (first_x_assum (drule_then drule) >> simp[]) >>
  gvs[supported_expr_exists_def, expr_abi_decode_target_root_def]
QED

Theorem lookup_function_abi_decode_target_occurs:
  !src name vis tops mut nr args dflts ret body target.
    lookup_function src name vis tops = SOME (mut,nr,args,dflts,ret,body) /\
    supported_stmts_expr_exists (expr_abi_decode_target_root target) body ==>
    occurs_abi_decode_target target tops
Proof
  Induct_on `tops` >>
  simp[lookup_function_def, occurs_abi_decode_target_def] >-
  (Cases_on `vis` >>
   rw[lookup_function_def, supported_stmt_expr_exists_def]) >>
  Cases >> rpt gen_tac >>
  simp[lookup_function_def, declaration_abi_decode_target_def] >>
  TRY (Cases_on `v`) >> Cases_on `vis` >>
  rw[lookup_function_def, declaration_abi_decode_target_def] >>
  gvs[getter_def, 
      supported_stmt_expr_exists_def, supported_expr_exists_def,
      expr_abi_decode_target_root_def, occurs_abi_decode_target_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  TRY (disj2_tac >> first_x_assum irule >> metis_tac[] >> NO_TAC) >>
  TRY (first_x_assum irule >> metis_tac[] >> NO_TAC) >>
  imp_res_tac build_getter_abi_decode_target >>
  gvs[supported_stmt_expr_exists_def, supported_expr_exists_def,
      expr_abi_decode_target_root_def]
QED
