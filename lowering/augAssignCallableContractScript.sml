(* The supported Internal lookup fixes the semantic callee in either mode. *)
Theory augAssignCallableContract
Ancestors
  supportedProgram supportedDecls vyperInterpreter list pair option

Theorem augassign_supported_callable_contract:
  !tops id in_deploy mut nr args defaults ret body.
  supported_program tops /\
  IS_SOME (supported_function_decl tops id Internal) /\
  lookup_callable_function in_deploy (SND id) tops =
    SOME (mut,nr,args,defaults,ret,body) ==>
  FST id = NONE /\ ~nr /\ defaults = [] /\
  supported_function_body tops Internal args body /\
  ~supported_stmts_expr_exists expr_internal_call_root body
Proof
  `!tops id mut nr rr args dflts ret body.
    supported_function_decl tops id Internal =
      SOME (mut,nr,rr,args,dflts,ret,body) ==>
    FST id = NONE /\
    lookup_function NONE (SND id) Internal tops =
      SOME (mut,nr,args,dflts,ret,body) /\
    MEM (FunctionDecl Internal mut nr rr (SND id) args dflts ret body) tops` by
    (Induct >> Cases_on `id` >> simp[supported_function_decl_def] >>
     Cases_on `h` >> simp[supported_function_decl_def, lookup_function_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()] >>
     first_x_assum drule >> simp[lookup_function_def] >>
     Cases_on `v` >> simp[lookup_function_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `supported_function_decl tops id Internal` >> gvs[] >>
  PairCases_on `x` >> first_x_assum drule >> strip_tac >>
  gvs[lookup_callable_function_def] >>
  drule_all supported_program_declaration >>
  simp[supported_function_header_contract] >> strip_tac >>
  drule_all supported_program_function >> strip_tac >>
  gvs[NULL_EQ] >> drule supported_internal_body_contract >> simp[]
QED
