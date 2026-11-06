(* Source validity resolves the compiler's selector table. *)
Theory sourceEntrySelection
Ancestors entryDispatchProps e2eDefs supportedProgram supportedNames
  supportedDecls list

Theorem source_valid_linear_dispatch_target:
  supported_program tops /\
  valid_vyper_call tops tx cd ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  !fb. linear_dispatch_target cd
    (MAP (\(sel,lbl,_). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
    "fn_" ++ tx.function_name
Proof
  strip_tac >>
  gvs[valid_vyper_call_def] >> gen_tac >>
  `!nr' mut' typ x.
     ~MEM (VariableDecl (Public nr') mut' tx.function_name typ x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  `!nr' b kt vt x.
     ~MEM (HashMapDecl (Public nr') b tx.function_name kt vt x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
      (FST (classify_functions tops))))` by
    fs[supported_program_def, supported_declaration_names_def,
       supported_selectors_distinct_def] >>
  drule_all linear_dispatch_selects_function >> simp[]
QED
