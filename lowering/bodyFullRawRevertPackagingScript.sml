(* Packaging the RawRevert value judgment using the shared stack conversion. *)
Theory bodyFullRawRevertPackaging
Ancestors
  bodyFullPreds bodyFullExprGeneric bodyFullRawRevertInterfaces
  vyperSystemControl exprLowering builtinSystem compileEnv vyperAST
Libs
  pairLib

Theorem raw_revert_body_full_from_value:
  (!cx ann args dflt DF lo d PG tops ctx shadow_ctx func shadow_func
      cenv env ty es.
    (!cenv ty e.
       gas_shadow_compiles (lower_value compile_expr cenv ty e)
         (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
    body_exprs_full_ok cx args /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Call ann RawRevert args dflt) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann RawRevert args dflt) es) ==>
  !cx ann es dflt.
    (!cenv ty e.
       gas_shadow_compiles (lower_value compile_expr cenv ty e)
         (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ann RawRevert es dflt)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_full_ok_def] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call ann RawRevert es dflt) es'` by metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_stack_full >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[raw_revert_no_success] >>
      drule raw_revert_source_pre >> strip_tac >> gvs[] >>
      simp[vyperASTTheory.expr_type_def,
           exprLoweringTheory.lowered_value_type_def,
           vyperValueTheory.evaluate_type_def,
           valueEncodingTheory.type_memory_size_def]) >>
  drule raw_revert_source_pre >> strip_tac >> gvs[] >>
  gen_tac >>
  simp[Once compile_expr_def, compile_call_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED
