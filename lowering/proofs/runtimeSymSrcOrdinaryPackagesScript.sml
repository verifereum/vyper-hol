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

Theorem runtime_sym_internal_package_body:
  supported_program tops /\ ~program_reads_self_code tops /\
  MEM (mut,nr,rr,name,args,defaults,ret,fbody) (FST (SND (classify_functions tops))) /\
  set_internal_package_target target
    (package_internal_fn tops trans keys ctor imm (mut,nr,rr,name,args,defaults,ret,fbody)) =
    (lbl,ce,params,buf,nr',key,tr,view,ct,im,stmts,rt) /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (v,s') ==> EVERY runtime_sym_inst (state_insts s')) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_fixed_region_with_id n s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand (SND v).buf_operand) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_internal_function ce params buf nr' key tr view ct im stmts rt s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> drule_all runtime_sym_internal_source >> strip_tac >>
  drule runtime_sym_internal_package_fields >> strip_tac >> gvs[] >>
  drule runtime_sym_internal_environment >> strip_tac >>
  drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_internal_function >>
  disch_then (qspecl_then [`tops`,
    `args ++ supported_stmts_bindings T fbody ++ supported_stmts_bindings F fbody`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt conj_tac >> rpt gen_tac >> first_assum MATCH_ACCEPT_TAC)) >> simp[]
QED

Theorem runtime_sym_fallback_package_body:
  supported_program tops /\ ~program_reads_self_code tops /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,fbody) /\
  set_fallback_package_target target
    (package_fallback_fn tops trans keys (SOME (mut,nr,rr,name,args,defaults,ret,fbody))) =
    SOME (ce,pay,nr',key,tr,view,stmts,rt) /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_fallback_body ce pay nr' key tr view stmts rt s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> drule_all runtime_sym_fallback_source >> strip_tac >>
  drule runtime_sym_fallback_package_fbody >> strip_tac >> gvs[] >>
  drule runtime_sym_fallback_environment >> strip_tac >>
  drule_at (Pat `compile_fallback_body _ _ _ _ _ _ _ _ _ = _`)
    runtime_sym_fallback_body >>
  disch_then (qspecl_then [`tops`,
    `args ++ supported_stmts_bindings T fbody ++ supported_stmts_bindings F fbody`] mp_tac) >> simp[] >>
  (impl_tac >- (rpt gen_tac >> first_assum MATCH_ACCEPT_TAC)) >> simp[]
QED

Theorem runtime_sym_external_classified_bodies:
  supported_program tops /\ ~program_reads_self_code tops /\
  (!src. MEM src sources ==> MEM src (FST (classify_functions tops))) /\
  packages = MAP (set_external_package_target target o package_external_fn tops trans keys) sources /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==> EVERY runtime_sym_inst (state_insts s') /\
    ~is_label_operand b.buf_operand) /\
  (!ce args off s u s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    compile_decode_args ce args off CALLDATALOAD (Lit 0w) 4 s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_external_fn_bodies packages s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> match_mp_tac runtime_sym_external_fn_bodies >>
  rewrite_tac[EVERY_MEM] >> gen_tac >> PairCases_on `e` >>
  simp_tac bool_ss [pairTheory.pair_case_thm, GSYM EVERY_MEM] >> strip_tac >>
  CONV_TAC (DEPTH_CONV pairLib.PAIRED_BETA_CONV) >>
  conj_tac >- metis_tac[runtime_sym_entry_checks] >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  qpat_x_assum `(_,_,_,_,_,_,_,_,_,_,_) = _` (assume_tac o SYM) >>
  rpt strip_tac >>
  drule_at (Pat `set_external_package_target _ _ = _`) runtime_sym_external_package_body >>
  simp[] >> disch_then irule >> conj_tac
  >- (rpt gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >> qexists `s` >> simp[]
QED

Theorem runtime_sym_internal_classified_bodies:
  supported_program tops /\ ~program_reads_self_code tops /\
  (!src. MEM src sources ==> MEM src (FST (SND (classify_functions tops)))) /\
  packages = MAP (set_internal_package_target target o package_internal_fn tops trans keys ctor imm) sources /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (v,s') ==> EVERY runtime_sym_inst (state_insts s')) /\
  (!n s v s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_fixed_region_with_id n s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand (SND v).buf_operand) ==>
  !s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_internal_fn_bodies packages s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> match_mp_tac runtime_sym_internal_fn_bodies >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  qpat_x_assum `(_,_,_,_,_,_,_,_,_,_,_,_) = _` (assume_tac o SYM) >>
  drule_at (Pat `set_internal_package_target _ _ = _`) runtime_sym_internal_package_body >>
  simp[] >> disch_then irule >> conj_tac
  >- (rpt gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac >- metis_tac[] >> qexists `s` >> simp[]
QED
