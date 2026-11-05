(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: keccak256 (S1: exprSimBuiltins' compile_keccak256_case,
   exprSimHash). *)
Theory bodyMemBiKeccak
Ancestors
  bodyMemoryPreds bodyMemBiKeccakTyped exprSimMemoryStack exprSimHash
  exprSimHypsDefs exprSimSource exprLoweringProps exprSimDefs exprLowering emitHelper
  vyperTyping vyperContext vyperTypeSystem vyperAST compileEnv valueEncoding

Theorem body_builtin_keccak256_mem:
  !cx ty es.
    (builtin_args_length_ok Keccak256 (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty Keccak256 es)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  `builtin_args_length_ok Keccak256 (LENGTH es)` by
    (gvs[expr_body_pre_def, well_typed_expr_def,
         well_typed_builtin_app_def, builtin_args_length_ok_def]) >>
  `?e. es = [e]` by
    (gvs[builtin_args_length_ok_def] >>
     Cases_on `es` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  gvs[body_exprs_mem_ok_def] >>
  `expr_body_pre cenv cx env e es'` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- gvs[expr_body_pre_def] >>
     qexistsl_tac [`ty`, `[e]`, `Keccak256`, `es'`] >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty' (Builtin ty Keccak256 [e]) es'` by
    (irule compile_keccak256_sim_mem >>
     conj_tac >- metis_tac[] >>
     fs[body_expr_mem_ok_def] >> metis_tac[]) >>
  simp[] >>
  irule body_expr_vv_sim_mem_stack_word >> simp[] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[eval_expr_builtin_value] >>
      gvs[expr_body_pre_def, well_typed_expr_def,
          well_typed_builtin_app_def, expr_type_def, is_word_type_def]) >>
  gen_tac >>
  simp[compile_hash_singleton, as_stack_val_def] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_stack_val ty suffix` >>
  Cases_on `suffix` >> simp[as_stack_val_def] >> metis_tac[]
QED
