(* TOP-LEVEL: all fixed-array iterations execute under the actual
   recursive child's typed copy contract, preserving full typed prefixes. *)
Theory typedSArrayRun
Ancestors
  typedSArrayElement typedDynLoopRun typedDynLoopValues typedDynLoopInvariant
  typedSArrayChildContract typedCopyContract typedSArrayLoop typedSArrayDynInvariant
  memoryValueDefs valueEncoding abiBytestringCode abiStaticLoopCode
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_sarray_copy_loop_run:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs' after child_names
      at_index src_data dst_data initial start.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 7) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
      (Var (compiler_var_name cs.cs_next_var 5)) ftv atv (sarray_copy_start cenv dst fty src aty copy_count cs) after /\
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\ fn_has_code cs cs' func /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) /\
    copy_count < dimword(:256) /\
    eval_operand dst initial = SOME dst_data /\
    eval_operand src initial = SOME src_data /\
    (!j. j < copy_count ==> value_has_type atv (at_index j)) /\
    w2n src_data + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_data + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) /\
    array_copy_loop_inv (compiler_var_name cs.cs_next_var 0) (fresh_label_output "typed_sa_cond" cs.cs_next_label)
      (compiler_var_names cs.cs_next_var (8 + child_names)) ftv atv at_index copy_count src_data dst_data initial 0 start ==>
    ?out. fragment_path ctx func start out /\
      array_copy_loop_inv (compiler_var_name cs.cs_next_var 0) (fresh_label_output "typed_sa_cond" cs.cs_next_label)
        (compiler_var_names cs.cs_next_var (8 + child_names)) ftv atv at_index copy_count src_data dst_data initial copy_count out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all array_copy_compatible_values_wf >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `compiler_var_name cs.cs_next_var 0`,
    `fresh_label_output "typed_sa_cond" cs.cs_next_label`, `compiler_var_names cs.cs_next_var (8 + child_names)`,
    `ftv`, `atv`, `at_index`, `copy_count`, `src_data`, `dst_data`, `initial`, `start`] array_copy_loop_run) >> impl_tac
  >- (asm_simp_tac bool_ss [] >> MAP_EVERY qx_gen_tac [`i`, `current`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
      `value_has_type atv (at_index i)` by
        (qpat_x_assum `!j. j < copy_count ==> value_has_type _ _` (qspec_then `i` mp_tac) >> simp[]) >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
        `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`, `after`, `child_names`, `at_index`, `src_data`, `dst_data`, `initial`, `i`, `current`]
        checked_sarray_copy_element_path) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC]) >> simp[]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked arbitrary-child fixed-array loop: " ^ name)
  end) (DB.thms "typedSArrayRun")
