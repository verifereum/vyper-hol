(* TOP-LEVEL: the complete checked dynamic-array dispatcher contract.
   Equal element types use the verified bulk path; distinct element types
   need only the actual recursive child's contract. *)
Theory typedDynStoreContract
Ancestors
  vyperEventArgCompat
  typedDynArrayContract typedDynBulkContract typedDynStoreProps typedCopyContract
  typedDynLoopCode checkedCopyAcyclic context compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_compile_typed_dynarray_contract:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv dst_capacity src aty atv src_capacity cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    src_capacity <= dst_capacity /\ dst_capacity < dimword(:256) /\
    compile_store_memory_typed cenv dst (ArrayT fty (Dynamic dst_capacity))
      src (ArrayT aty (Dynamic src_capacity)) cs = (ret,cs') /\
    (fty <> aty ==> !after.
      compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
        (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty dst_capacity src aty cs) = ((),after) ==>
      typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
        (Var (compiler_var_name cs.cs_next_var 10)) ftv atv (dynarray_copy_start cenv dst fty dst_capacity src aty cs) after) ==>
    typed_copy_contract ctx func dst src (ArrayTV ftv (Dynamic dst_capacity)) (ArrayTV atv (Dynamic src_capacity)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `fty = aty`
  >- (qpat_x_assum `fty = aty` SUBST_ALL_TAC >>
      `ftv = atv` by (qpat_x_assum `evaluate_type _ aty = SOME ftv` mp_tac >> simp[]) >>
      pop_assum SUBST_ALL_TAC >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `aty`, `atv`,
        `dst_capacity`, `src`, `src_capacity`, `cs`, `ret`, `cs'`] checked_compile_typed_dynarray_bulk_contract) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
  `compile_copy_dynarray_typed cenv dst fty dst_capacity src aty cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory_typed _ _ (ArrayT _ _) _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_typed_dynarray_dispatch]) >>
  qabbrev_tac `after = SND (compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
    (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty dst_capacity src aty cs))` >>
  `compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
    (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty dst_capacity src aty cs) = ((),after)` by
    (simp_tac bool_ss [Abbr`after`] >>
     Cases_on `compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
       (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty dst_capacity src aty cs)` >> simp[]) >>
  qpat_x_assum `fty <> aty ==> _` mp_tac >> impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspec_then `after` mp_tac) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `dst_capacity`, `src`, `aty`, `atv`, `src_capacity`, `cs`, `ret`, `cs'`, `after`] checked_compile_copy_dynarray_contract) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED
