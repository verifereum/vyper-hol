(* TOP-LEVEL: the actual fixed-array bulk branch satisfies the complete
   typed copy contract. Static compatibility identifies source and target
   element types; checked metadata gives the exact physical copy length. *)
Theory typedSArrayBulkContract
Ancestors
  typedCopyBulkContract typedStaticCompatibility typedCopyContract typedSArrayDynInvariant
  typeLayoutProps typedCopyProducer memoryValueDefs valueEncoding
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_compile_copy_sarray_bulk_contract:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src (ArrayTV ftv (Fixed copy_count)) (ArrayTV atv (Fixed copy_count)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `fty = aty` by
    (drule (CONJUNCT1 event_arg_compatible_static_type) >>
     disch_then (qspec_then `cenv.ce_struct_fields` mp_tac) >> simp[]) >>
  pop_assum (SUBST_ALL_TAC o SYM) >>
  `atv = ftv` by (qpat_x_assum `evaluate_type _ fty = SOME atv` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `type_memory_bytes cenv fty = type_memory_size ftv` by
    (drule_all type_memory_bytes_evaluated >> simp[]) >>
  `compile_copy_memory dst src (type_memory_size (ArrayTV ftv (Fixed copy_count))) cs = (ret,cs')` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac (srw_ss()) [Once compile_store_memory_typed_def, LET_THM, type_memory_size_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `ArrayTV ftv (Fixed copy_count)`, `cs`, `ret`, `cs'`]
    compile_copy_memory_contract) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed fixed-array bulk-copy contract: " ^ name)
  end) (DB.thms "typedSArrayBulkContract")
