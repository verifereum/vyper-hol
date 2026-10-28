(* TOP-LEVEL: the complete checked fixed-array dispatcher contract.
   The bulk branch needs no child contract. The recursive branch uses
   only the actual child's contract, cuts and allocated-name range. *)
Theory typedSArrayStoreContract
Ancestors
  typedSArrayContract typedSArrayBulkContract typedSArrayChildContract typedCopyContract
  typedSArrayLoop checkedCopyAcyclic context compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_compile_typed_sarray_contract:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    copy_count < dimword(:256) /\
    compile_store_memory_typed cenv dst (ArrayT fty (Fixed copy_count))
      src (ArrayT aty (Fixed copy_count)) cs = (ret,cs') /\
    (~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) ==>
      !after. compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
        (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) ==>
      typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
        (Var (compiler_var_name cs.cs_next_var 5)) ftv atv (sarray_copy_start cenv dst fty src aty copy_count cs) after) ==>
    typed_copy_contract ctx func dst src (ArrayTV ftv (Fixed copy_count)) (ArrayTV atv (Fixed copy_count)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty`
  >- (qpat_x_assum `_ /\ _` strip_assume_tac >>
      `acyclic_struct_metadata cenv.ce_struct_fields` by
        (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
      `compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs')` by
        (qpat_x_assum `compile_store_memory_typed _ _ (ArrayT _ _) _ _ _ = _` mp_tac >>
         asm_simp_tac bool_ss [compile_typed_sarray_dispatch]) >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
        `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`] checked_compile_copy_sarray_bulk_contract) >>
      impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `~(_ /\ _) ==> _` mp_tac >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`] checked_compile_typed_sarray_recursive_contract) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked fixed-array dispatcher contract: " ^ name)
  end) (DB.thms "typedSArrayStoreContract")
