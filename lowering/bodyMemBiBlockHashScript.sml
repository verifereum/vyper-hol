(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: blockhash (S1: exprSimBuiltins' compile_blockhash_case). *)
Theory bodyMemBiBlockHash
Ancestors
  bodyMemoryPreds bodyMemBiBlockHashFrag bodyMemBiBlockHashPath exprSimBuiltins
  bodyUnopFragMemory exprSimMemoryStack exprSimHypsDefs exprSimSource
  vyperTyping vyperTypeSystem vyperAST list vyperInterpreter vyperContext compileEnv exprLoweringProps

Theorem body_builtin_blockhash_mem:
  !cx ty es.
    (builtin_args_length_ok BlockHash (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty BlockHash es)
Proof
  rpt gen_tac >> strip_tac >> rw[body_expr_mem_ok_def] >>
  `?e. es = [e] /\ ty = BaseT (BytesT (Fixed 32)) /\
       expr_type e = BaseT (UintT 256)` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `es` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[body_exprs_mem_ok_def, builtin_args_length_ok_def] >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es'`] mp_tac) >>
     simp[] >> disch_then irule >> fs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx ty' e es'` by
    metis_tac[body_expr_mem_ok_def] >>
  `expr_sim_mem ctx func cenv cx ty' (Builtin (BaseT (BytesT (Fixed 32))) BlockHash [e]) es'` by
    (irule compile_blockhash_sim_mem >> simp[] >> qexists_tac `env` >> simp[]) >>
  simp[] >>
  irule body_expr_vv_sim_mem_stack_word >>
  simp[expr_type_def, is_word_type_def, compile_blockhash_stack] >>
  metis_tac[eval_expr_builtin_value]
QED

