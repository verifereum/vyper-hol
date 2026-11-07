Theory bodyPtrStructLitOwnershipSources
Ancestors supportedProgram supportedDecls loweringShapeProps compileVyper
  supportedStmtTraverse loweringShapeDefs list pair

Theorem structlit_supported_function_defaults:
  !tops vis mut nr rr name args defaults ret body.
  supported_program tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
  defaults = []
Proof
  rpt strip_tac >> drule_all supported_program_declaration >>
  simp[supported_function_header_contract, NULL_EQ]
QED

Theorem structlit_supported_function_body:
  !tops vis mut nr rr name args defaults ret body.
  supported_program tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops ==>
  ~supported_stmts_expr_exists expr_shape_root body
Proof
  rpt gen_tac >> strip_tac >> drule_all supported_program_function >>
  metis_tac[supported_function_body_shape]
QED

Theorem structlit_classify_constructor_source:
  !tops mut nr rr name args defaults ret body.
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,body) ==>
  MEM (FunctionDecl Deploy mut nr rr name args defaults ret body) tops
Proof
  Induct_on `tops` >- simp[classify_functions_def] >> rpt gen_tac >>
  simp[classify_functions_def, Once FOLDR] >>
  qmatch_goalsub_abbrev_tac `classify_function h acc` >>
  PairCases_on `acc` >> fs[classify_functions_def] >>
  Cases_on `h` >> simp[classify_function_def] >>
  rename1 `case vis of External => _ | Internal => _ | Deploy => _` >>
  Cases_on `vis` >> simp[classify_function_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), COND_RAND] >> metis_tac[classify_functions_def]
QED

Theorem structlit_classified_function_source:
  !tops exts ints fb ctor mut nr rr name args defaults ret body.
  classify_functions tops = (exts,ints,fb,ctor) /\
  (MEM (mut,nr,rr,name,args,defaults,ret,body) exts \/
   MEM (mut,nr,rr,name,args,defaults,ret,body) ints \/
   fb = SOME (mut,nr,rr,name,args,defaults,ret,body) \/
   ctor = SOME (mut,nr,rr,name,args,defaults,ret,body)) ==>
  ?vis. MEM (FunctionDecl vis mut nr rr name args defaults ret body) tops
Proof
  metis_tac[classify_functions_external_source, MEM_classify_internal,
    classify_functions_fallback_mem, structlit_classify_constructor_source,
    FST, SND]
QED

Theorem structlit_classified_function_defaults:
  !tops exts ints fb ctor mut nr rr name args defaults ret body.
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) /\
  (MEM (mut,nr,rr,name,args,defaults,ret,body) exts \/
   MEM (mut,nr,rr,name,args,defaults,ret,body) ints \/
   fb = SOME (mut,nr,rr,name,args,defaults,ret,body) \/
   ctor = SOME (mut,nr,rr,name,args,defaults,ret,body)) ==>
  defaults = []
Proof
  metis_tac[structlit_classified_function_source,
    structlit_supported_function_defaults]
QED

Theorem structlit_classified_function_body:
  !tops exts ints fb ctor mut nr rr name args defaults ret body.
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) /\
  (MEM (mut,nr,rr,name,args,defaults,ret,body) exts \/
   MEM (mut,nr,rr,name,args,defaults,ret,body) ints \/
   fb = SOME (mut,nr,rr,name,args,defaults,ret,body) \/
   ctor = SOME (mut,nr,rr,name,args,defaults,ret,body)) ==>
  ~supported_stmts_expr_exists expr_shape_root body
Proof
  metis_tac[structlit_classified_function_source,
    structlit_supported_function_body]
QED
