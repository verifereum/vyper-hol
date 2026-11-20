Theory entryPackagedRuntimeCode
Ancestors
  entryRuntimeBodyCode entryClassifiedSupport entrySupportedStatementCode
  entryCodePredicate entryExpressionCode supportedProgram compileVyper
  moduleLowering vyperGetter list

Theorem entry_code_function_body[local]:
  supported_function_body tops vis args fb ==>
  !ce lc rt. EVERY (EVERY (supported_expr tops) o SND) ce.ce_func_defaults ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmts ce lc rt fb)
Proof
  simp[supported_function_body_def] >> rpt strip_tac >>
  irule entry_code_supported_stmts >>
  qexistsl_tac [`args ++ supported_stmts_bindings T fb ++ supported_stmts_bindings F fb`, `tops`] >>
  simp[]
QED

Theorem entry_code_build_defaults[local]:
  supported_program tops /\ module_consts_env tops [] = [] ==>
  EVERY (EVERY (supported_expr tops) o SND) (build_func_defaults tops)
Proof
  strip_tac >> simp[build_func_defaults_def, EVERY_MAP, EVERY_MEM] >>
  qx_gen_tac `src` >> strip_tac >> gvs[MEM_MAP] >>
  rename1 `MEM decl (FST (SND (classify_functions tops)))` >>
  PairCases_on `decl` >>
  drule_all entry_classified_internal_support >> strip_tac >>
  gvs[supportedExprsTheory.supported_pure_exprs_every, EVERY_MEM] >>
  metis_tac[supportedExprsTheory.supported_expr_def]
QED

Theorem entry_code_build_getter[local]:
  !ne kt vt n args ret exp.
    build_getter ne kt vt n = (args,ret,exp) /\
    (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
       (compile_expr ce et ne)) ==>
    !ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_expr ce et exp)
Proof
  recInduct build_getter_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [build_getter_def]) >>
  rw[] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[entry_code_subscript_expr, entry_code_name_expr]
QED

Theorem entry_code_public_getter_body[local]:
  public_getter top = SOME (mut,nr,rr,name,args,defaults,ret,gbody) ==>
  !ce lc rt. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_stmts ce lc rt gbody)
Proof
  rw[oneline public_getter_def, AllCaseEqs()] >> gvs[getter_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  irule entry_code_return_some_stmts >>
  metis_tac[entry_code_build_getter, entry_code_toplevel_name_expr]
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_MEM] >>
  qx_gen_tac `src` >> strip_tac >> PairCases_on `src` >>
  drule_all entry_classified_external_support >> strip_tac >> gvs[] >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  irule entry_code_external_function_body
  >- (rpt gen_tac >> strip_tac >>
      irule entry_code_function_body >> qexistsl_tac [`src4`, `tops`, `External`] >>
      Cases_on `src6 = NoneT` >>
      fs[update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
               build_compile_env_ce_func_defaults, entry_code_build_defaults]) >>
  metis_tac[entry_code_public_getter_body]
QED
*)
Theorem entry_code_packaged_externals:
  supported_program tops /\ module_consts_env tops [] = [] ==>
  EVERY (\(lbl,ce,args,cds,pay,nr,key,tr,vw,fb,rt).
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_external_function_body ce args nr key tr vw fb rt))
    (MAP (set_external_package_target target)
      (MAP (package_external_fn tops T (K global_nonreentrant_slot))
        (FST (classify_functions tops))))
Proof
  cheat
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  strip_tac >> simp[EVERY_MAP, EVERY_MEM] >>
  qx_gen_tac `src` >> strip_tac >> PairCases_on `src` >>
  drule_all entry_classified_internal_support >> strip_tac >> gvs[] >>
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  irule entry_code_internal_function >>
  rpt gen_tac >> strip_tac >>
  irule entry_code_function_body >> qexistsl_tac [`src4`, `tops`, `Internal`] >>
  Cases_on `src6 = NoneT` >>
      fs[update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
           build_compile_env_ce_func_defaults, entry_code_build_defaults]
QED
*)
Theorem entry_code_packaged_internals:
  supported_program tops /\ module_consts_env tops [] = [] ==>
  EVERY (\(lbl,ce,ps,buf,nr,key,tr,vw,ctor,im,fb,rt).
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_internal_function ce ps buf nr key tr vw ctor im fb rt))
    (MAP (set_internal_package_target target)
      (MAP (package_internal_fn tops T (K global_nonreentrant_slot) F 0)
        (FST (SND (classify_functions tops)))))
Proof
  cheat
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  strip_tac >>
  Cases_on `FST (SND (SND (classify_functions tops)))`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  rename1 `SOME src` >> PairCases_on `src` >>
  drule_all entry_classified_fallback_support >> strip_tac >> gvs[] >>
  simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  irule entry_code_fallback_body >>
  rpt gen_tac >> strip_tac >>
  irule entry_code_function_body >> qexistsl_tac [`src4`, `tops`, `External`] >>
  Cases_on `src6 = NoneT` >>
      fs[update_cenv_ret_abi_def, update_cenv_nonreentrant_def,
           build_compile_env_ce_func_defaults, entry_code_build_defaults]
QED
*)
Theorem entry_code_packaged_fallback:
  supported_program tops /\ module_consts_env tops [] = [] ==>
  (case set_fallback_package_target target
     (package_fallback_fn tops T (K global_nonreentrant_slot)
       (FST (SND (SND (classify_functions tops))))) of
     NONE => T
   | SOME (ce,pay,nr,key,tr,vw,fb,rt) =>
       entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
         (compile_fallback_body ce pay nr key tr vw fb rt))
Proof
  cheat
QED
