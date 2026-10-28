(* TOP-LEVEL: the verified fixed-array and dynamic-array dispatcher cases
   lift child type-pair contracts to array type-pair contracts. Actual
   compiler branches decide whether the child assumption is needed. *)
Theory typedCopyArrayTypeContracts
Ancestors
  typedCopyTypeContract typedSArrayStoreContract typedDynStoreContract
  typedSArrayLoop typedDynLoopCode typedCopyContract abiBytestringCode abiStaticLoopCode
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem typed_copy_type_contract_sarray:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv copy_count.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    copy_count < dimword(:256) /\
    (~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) ==>
    typed_copy_type_contract ctx func cenv (ArrayT fty (Fixed copy_count)) (ArrayT aty (Fixed copy_count))
      (ArrayTV ftv (Fixed copy_count)) (ArrayTV atv (Fixed copy_count))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`] checked_compile_typed_sarray_contract) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        DISCH_TAC >> qx_gen_tac `after` >> DISCH_TAC >>
        qpat_x_assum `_ ==> typed_copy_type_contract _ _ _ _ _ _ _` mp_tac >>
        impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
        drule_all typed_copy_type_contract_result >> simp[]]) >> simp[]
QED

Theorem typed_copy_type_contract_dynarray:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv dst_capacity src_capacity.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    src_capacity <= dst_capacity /\ dst_capacity < dimword(:256) /\
    (fty <> aty ==> typed_copy_type_contract ctx func cenv fty aty ftv atv) ==>
    typed_copy_type_contract ctx func cenv (ArrayT fty (Dynamic dst_capacity)) (ArrayT aty (Dynamic src_capacity))
      (ArrayTV ftv (Dynamic dst_capacity)) (ArrayTV atv (Dynamic src_capacity))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `dst_capacity`, `src`, `aty`, `atv`, `src_capacity`, `cs`, `ret`, `cs'`] checked_compile_typed_dynarray_contract) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        DISCH_TAC >> qx_gen_tac `after` >> DISCH_TAC >>
        qpat_x_assum `_ ==> typed_copy_type_contract _ _ _ _ _ _ _` mp_tac >>
        impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
        drule_all typed_copy_type_contract_result >> simp[]]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed array type-pair copy contracts: " ^ name)
  end) (DB.thms "typedCopyArrayTypeContracts")
