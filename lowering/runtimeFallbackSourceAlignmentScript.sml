(* Source provenance of the classified fallback slot. *)
Theory runtimeFallbackSourceAlignment
Ancestors compileVyper loweringShapeProps supportedProgram supportedDecls
  entryStateRel entryDispatchProps defaultDispatchFacts constSubst
  vyperInterpreter vyperTypeContract
Libs BasicProvers

Theorem classified_fallback_fold_name[local]:
  !tops mut nr rr name args ds ret fbody.
    FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) =
      SOME (mut,nr,rr,name,args,ds,ret,fbody) ==>
    name = "__default__"
Proof
  Induct >> simp[] >> gen_tac >>
  qabbrev_tac `acc = FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `acc` >> gvs[GSYM markerTheory.Abbrev_def] >>
  Cases_on `h` >> pure_rewrite_tac[classify_function_def] >>
  pure_rewrite_tac[pairTheory.FST, pairTheory.SND] >>
  TRY (first_x_assum MATCH_ACCEPT_TAC) >>
  Cases_on `f` >>
  pure_rewrite_tac[vyperASTTheory.function_visibility_case_def] >>
  Cases_on `s = "__default__"` >>
  pure_asm_rewrite_tac[] >>
  simp_tac std_ss [] >> metis_tac[]
QED

Theorem classified_fallback_name:
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,ds,ret,fbody) ==>
  name = "__default__"
Proof
  simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `fb` >> gvs[] >> PairCases_on `x` >>
  simp[subst_consts_fn_def] >> strip_tac >> gvs[] >>
  qspec_then `tops` mp_tac classified_fallback_fold_name >> simp[]
QED

Theorem classified_fallback_source_alignment_nr:
  supported_program tops /\ source_typing_ok tops am tx /\
  tx.function_name = "__default__" /\
  FST (SND (SND (classify_functions tops))) = SOME fb /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,[],ret,fbody) ==>
  fb = (mut,nr,
        lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
        tx.function_name,args,([]:expr list),ret,
        subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  strip_tac >> PairCases_on `fb` >>
  drule classified_fallback_name >> strip_tac >>
  drule classify_functions_fallback_mem >> strip_tac >>
  `EXISTS is_default_decl tops` by
    (simp[listTheory.EXISTS_MEM] >> goal_assum (drule_at Any) >>
     simp[vyperCalldataTheory.is_default_decl_def]) >>
  `vyperInterpreter$lookup_function NONE "__default__" External tops =
     SOME (mut,nr,args,[],ret,fbody)` by metis_tac[] >>
  drule_all default_fallback_classified >> gvs[subst_consts_fn_def, subst_consts_expr_def]
QED

Theorem classified_fallback_source_alignment:
  supported_program tops /\ source_typing_ok tops am tx /\
  tx.function_name = "__default__" /\
  FST (SND (SND (classify_functions tops))) = SOME fb /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  fb = (mut,F,
        lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
        tx.function_name,args,([]:expr list),ret,
        subst_consts_stmts (module_consts_env tops []) fbody)
Proof
  rpt strip_tac >> drule_all classified_fallback_source_alignment_nr >> simp[]
QED
