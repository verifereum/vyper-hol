Theory entryClassifiedSupport
Ancestors
  loweringShapeProps supportedProgram supportedDecls

Theorem entry_classified_external_support:
  !tops mut nr rr name args defaults ret body.
  supported_program tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,body)
    (FST (classify_functions tops)) ==>
  ~nr /\ NULL defaults /\
  EVERY (supported_function_argument tops External o SND) args /\
  supported_function_return tops External ret /\
  supported_function_body tops External args body /\
  supported_return_layouts ret body
Proof
  rpt gen_tac >> strip_tac >> drule classify_functions_external_source >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def, supported_declaration_body_def]
QED

Theorem entry_classified_internal_support:
  !tops mut nr rr name args defaults ret body.
  supported_program tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,body)
    (FST (SND (classify_functions tops))) ==>
  ~nr /\ NULL defaults /\
  EVERY (supported_function_argument tops Internal o SND) args /\
  supported_function_return tops Internal ret /\
  supported_function_body tops Internal args body /\
  supported_return_layouts ret body
Proof
  rpt gen_tac >> simp[MEM_classify_internal] >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def, supported_declaration_body_def]
QED

Theorem entry_classified_fallback_support:
  !tops mut nr rr name args defaults ret body.
  supported_program tops /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,body) ==>
  ~nr /\ NULL defaults /\
  EVERY (supported_function_argument tops External o SND) args /\
  supported_function_return tops External ret /\
  supported_function_body tops External args body /\
  supported_return_layouts ret body
Proof
  rpt gen_tac >> strip_tac >> drule classify_functions_fallback_mem >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def, supported_declaration_body_def]
QED
