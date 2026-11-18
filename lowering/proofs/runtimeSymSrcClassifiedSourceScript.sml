Theory runtimeSymSrcClassifiedSource
Ancestors
  supportedProgram supportedDecls constSubst compileVyper

Theorem runtime_sym_supported_subst_consts_fn:
  supported_program tops ==>
  subst_consts_fn (module_consts_env tops []) source = source
Proof
  strip_tac >>
  `module_consts_env tops [] = []` by
    (irule supported_headers_module_consts_env >>
     gvs[supported_program_def, supported_declaration_headers_def] >>
     metis_tac[]) >>
  simp[]
QED
