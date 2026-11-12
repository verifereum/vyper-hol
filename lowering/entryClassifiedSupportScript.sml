Theory entryClassifiedSupport
Ancestors
  loweringShapeProps supportedProgram supportedDecls

(* Since public getters are classified externals, a classified entry is either
   a supported source function or a synthesized getter. *)
Theorem entry_classified_external_support:
  !tops mut nr rr name args defaults ret body.
  supported_program tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,body)
    (FST (classify_functions tops)) ==>
  (NULL defaults /\
   EVERY (supported_function_argument tops External o SND) args /\
   supported_function_return tops External ret /\
   supported_function_body tops External args body /\
   supported_return_layouts ret body) \/
  ?top. MEM top tops /\
        public_getter top = SOME (mut,nr,rr,name,args,defaults,ret,body)
Proof
  rpt gen_tac >> strip_tac >>
  `module_consts_env tops [] = []` by
    metis_tac[supported_headers_module_consts_env, supported_program_def,
              supported_declaration_headers_def] >>
  drule classify_functions_external_source >> strip_tac >>
  gvs[constSubstTheory.subst_consts_fn_empty]
  >- (disj1_tac >> drule_all supported_program_declaration >>
      simp[supported_declaration_header_def, supported_declaration_body_def]) >>
  disj2_tac >> metis_tac[]
QED

Theorem entry_classified_internal_support:
  !tops mut nr rr name args defaults ret body.
  supported_program tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,body)
    (FST (SND (classify_functions tops))) ==>
  NULL defaults /\
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
  NULL defaults /\
  EVERY (supported_function_argument tops External o SND) args /\
  supported_function_return tops External ret /\
  supported_function_body tops External args body /\
  supported_return_layouts ret body
Proof
  rpt gen_tac >> strip_tac >> drule classify_functions_fallback_mem >> strip_tac >>
  drule_all supported_program_declaration >>
  simp[supported_declaration_header_def, supported_declaration_body_def]
QED
