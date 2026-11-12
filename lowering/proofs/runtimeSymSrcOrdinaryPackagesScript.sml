Theory runtimeSymSrcOrdinaryPackages
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleArgs runtimeSymSrcModuleBodies
  runtimeSymSrcInternalFunction runtimeSymSrcFunctionLists
  runtimeSymSrcInterfaces runtimeSymSrcEmissionProbe
  compileVyper moduleLowering compileEnv loweringShapeDefs list

Theorem runtime_sym_external_package_body:
  supported_program tops /\ ~program_reads_self_code tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,fbody) (FST (classify_functions tops)) /\
  set_external_package_target target
    (package_external_fn tops trans keys (mut,nr,rr,name,args,defaults,ret,fbody)) =
    (lbl,ce,params,mincd,pay,nr',key,tr,view,stmts,rt) /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==> EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) /\
  (!ce args off s u s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_external_function_body ce params nr' key tr view stmts rt s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> drule_all runtime_sym_external_source >> strip_tac >>
  drule runtime_sym_external_package_fields >> strip_tac >> gvs[] >>
  drule runtime_sym_external_environment >> strip_tac >>
  `!ce args off s ce' s'. runtime_sym_env ce /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_register_positional_args ce args off s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')` by
    (mp_tac runtime_sym_register_positional_args >>
     (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       rpt gen_tac >> Cases_on `u` >> first_assum MATCH_ACCEPT_TAC)) >> metis_tac[]) >>
  drule_at (Pat `compile_external_function_body _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_external_function_body >>
  disch_then (qspecl_then [`tops`,
    `args ++ supported_stmts_bindings T fbody ++ supported_stmts_bindings F fbody`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt gen_tac >> first_assum MATCH_ACCEPT_TAC)) >> simp[]
QED
