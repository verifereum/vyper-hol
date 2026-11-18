(* Source validity resolves the compiler's selector table. *)
Theory sourceEntrySelection
Ancestors entryDispatchProps e2eDefs supportedProgram supportedNames
  supportedDecls list

Theorem source_selected_linear_dispatch_target:
  supported_program tops /\
  tx.function_name <> "__default__" /\
  LENGTH tx.args = LENGTH args /\
  calldata_encodes (type_env tops) tx.function_name (MAP SND args) tx.args cd /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  !fb. linear_dispatch_target cd
    (MAP (\(sel,lbl,_). (sel,lbl))
      (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
    "fn_" ++ tx.function_name
Proof
  strip_tac >> gen_tac >>
  `ALL_DISTINCT (MAP FST (build_selectors (type_env tops)
      (FST (classify_functions tops))))` by
    fs[supported_program_def, supported_declaration_names_def,
       supported_selectors_distinct_def] >>
  drule_all linear_dispatch_selects_function >> simp[]
QED

Theorem valid_vyper_call_selected_calldata:
  valid_vyper_call tops tx cd ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  tx.function_name <> "__default__" /\
  LENGTH tx.args = LENGTH args /\
  calldata_encodes (type_env tops) tx.function_name (MAP SND args) tx.args cd
Proof
  simp[valid_vyper_call_def] >> rpt strip_tac >> gvs[]
QED

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
  strip_tac >> irule source_selected_linear_dispatch_target >>
  gvs[valid_vyper_call_def] >> goal_assum (drule_at Any) >> simp[]
QED
