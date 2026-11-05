(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: ecrecover (S1: exprSimPrecompiles'
   compile_ecrecover_call_case). *)
Theory bodyMemBiECRecover
Ancestors
  bodyMemoryPreds bodyMemBiECRecoverCompose exprSimPrecompiles exprSimDefs
  exprSimProps exprLowering exprLoweringProps exprSimWordArgs exprSimHypsDefs
  vyperTyping vyperAST vyperTypeSystem compileEnv list rich_list builtinMisc
  loweringPosts exprBopLowering vyperInterpreter vyperState vyperContext
  vyperValue vyperTypeInvariants valueEncoding integer_word words byte
  bodyArgsMemory exprSimMemoryStack exprSimSource

Theorem body_builtin_ecrecover_mem:
  !cx ty es.
    (builtin_args_length_ok ECRecover (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty ECRecover es)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `Builtin ann ECRecover args` >>
  rewrite_tac[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  drule ecrecover_pre_types >> strip_tac >>
  `body_exprs_mem_ok cx args` by
    (first_x_assum irule >> simp[builtin_args_length_ok_def]) >>
  `expr_sim_mem ctx func cenv cx ty (Builtin ann ECRecover args) es` by
    (irule ecrecover_expr_sim_mem >> qexists_tac `env` >> simp[] >>
     gen_tac >> irule typed_args_ready_mem_of_body >> rpt conj_tac
     >- (rpt strip_tac
         >- (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
               (mp_then Any mp_tac expr_body_pre_builtin_arg) >>
             simp[] >> disch_then irule >> simp[]) >>
         gvs[listTheory.EVERY_MEM]) >>
     metis_tac[]) >>
  simp[] >> irule body_expr_vv_sim_mem_stack_word >>
  simp[expr_type_def, is_word_type_def] >> conj_tac
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Builtin (BaseT AddressT) ECRecover args) sa` >>
      drule_all compile_ecrecover_stack >> strip_tac >> gvs[]) >>
  metis_tac[eval_expr_builtin_value]
QED
