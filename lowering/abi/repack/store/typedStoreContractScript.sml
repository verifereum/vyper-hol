(* TOP-LEVEL: the outer memory-store dispatcher has a raw-pointer
   contract for every non-word type. Only its recursive branch needs
   a recursive typed-copy contract; bulk and bytes branches are closed. *)
Theory typedStoreContract
Ancestors
  typedStoreLayout typedCopyTypeContract typedCopyContract typedBytesStoreProps
  bytesCopyProps eventTopicValueProps
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue

Definition memory_store_type_contract_def:
  memory_store_type_contract ctx func cenv fty aty ftv atv <=>
    !dst src cs ret cs'.
      compile_store_memory cenv src dst fty aty cs = (ret,cs') ==>
      typed_copy_contract ctx func dst src ftv atv cs cs'
End

Theorem memory_store_type_contract_result:
  !ctx func cenv fty aty ftv atv dst src cs ret cs'.
    memory_store_type_contract ctx func cenv fty aty ftv atv /\
    compile_store_memory cenv src dst fty aty cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  simp[memory_store_type_contract_def]
QED

Theorem compile_store_memory_bytes_contract:
  !tenv ctx func cenv dst src fty aty ftv atv cs ret cs'.
    is_bytestring_type fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv /\
    compile_store_memory cenv src dst fty aty cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  `~is_word_type fty` by (irule bytestring_type_not_word >> first_assum MATCH_ACCEPT_TAC) >>
  `is_bytestring_type aty` by (drule_all event_arg_compatible_bytestring >> simp[]) >>
  `compile_store_memory_typed cenv dst fty src aty cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_store_memory_def, compile_store_memory_typed_bytes_dispatch]) >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`, `src`, `aty`, `atv`, `cs`, `ret`, `cs'`]
    compile_store_memory_typed_bytes_contract) >> simp[]
QED

Theorem checked_compile_store_memory_contract:
  !tops in_deploy layouts addr art ctx func cenv dst src fty aty ftv atv cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    ~is_word_type fty /\
    (fty <> aty /\ ~tuple_memory_layout_eq fty aty /\ ~is_bytestring_type fty ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) /\
    compile_store_memory cenv src dst fty aty cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `is_bytestring_type fty`
  >- (mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `dst`, `src`, `fty`, `aty`, `ftv`, `atv`,
        `cs`, `ret`, `cs'`] compile_store_memory_bytes_contract) >> simp[]) >>
  Cases_on `fty <> aty /\ ~tuple_memory_layout_eq fty aty`
  >- (`typed_copy_type_contract ctx func cenv fty aty ftv atv` by fs[] >>
      `compile_store_memory_typed cenv dst fty src aty cs = (ret,cs')` by
        (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
         asm_simp_tac bool_ss [compile_store_memory_def]) >>
      drule_all typed_copy_type_contract_result >> simp[]) >>
  `compile_copy_memory dst src (type_memory_bytes cenv fty) cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_store_memory_def]) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `src`,
    `fty`, `aty`, `ftv`, `atv`, `cs`, `ret`, `cs'`] checked_compile_copy_layout_contract) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, fs[] >> NO_TAC]) >> simp[]
QED

Theorem memory_store_type_contract_checked:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    ~is_word_type fty /\
    (fty <> aty /\ ~tuple_memory_layout_eq fty aty /\ ~is_bytestring_type fty ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) ==>
    memory_store_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  simp_tac bool_ss [memory_store_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `src`,
    `fty`, `aty`, `ftv`, `atv`, `cs`, `ret`, `cs'`] checked_compile_store_memory_contract) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete outer memory store contract: " ^ name)
  end) (DB.thms "typedStoreContract")
