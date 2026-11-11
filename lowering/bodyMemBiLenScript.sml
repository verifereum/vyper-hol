(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: len (S1: exprSimBuiltins' compile_len_case, exprSimLen). *)
Theory bodyMemBiLen
Ancestors
  bodyMemoryPreds bodyMemBiLenCompose exprSimLen exprSimSource exprSimProps
  exprSimHypsDefs exprSimDefs loweringPosts list fragExec exprSimHyps
  exprSimWordBuiltins exprBopLowering exprLowering exprLoweringProps
  builtinSimple emitHelper compileEnv accountsRelProps valueEncoding
  venomExecSemantics venomInst venomState vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeSystem vyperTypeBuiltins vyperValue vyperTyping
  vyperStorage builtinProps vyperTypeInvariants context freshWrites
  loweringSlice emitHelperProps exprSimUnwrap exprSimCopy vyperTypeExprResult
  vyperTypeExprSoundness vyperExprNoControl gasContext gasOutcome gasSummary
  gasSummaryCompose gasExemptCert fragGasMode fragGasPath

Theorem body_builtin_len_mem:
  !cx ty es.
    (builtin_args_length_ok Len (LENGTH es) ==> body_expr_mem_ok cx (HD es)) ==>
    body_expr_mem_ok cx (Builtin ty Len es)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  drule len_pre_args >> strip_tac >> gvs[builtin_args_length_ok_def] >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es'`] mp_tac) >>
     fs[expr_body_pre_def]) >>
  `expr_vv_sim_mem ctx func cenv cx ty' e es'` by
    (fs[body_expr_mem_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (irule compile_len_singleton_forced_sim_mem >> metis_tac[]) >>
  irule compile_len_singleton_sim_mem >> metis_tac[]
QED
