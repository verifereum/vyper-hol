(* TOP-LEVEL: the actual checked dynamic-array loop executes every live
   element using a verified recursive child contract. The strides, name
   range and child compiler cut are tied to the real compiler metadata. *)
Theory typedDynLoopCheckedRun
Ancestors
  typedDynLoopElement typedDynLoopRun typedDynLoopValues typedDynLoopInvariant typedDynChildContract
  typedCopyContract typedDynLoopCode typedDynLoopStructure typedSArrayDynInvariant
  memoryValueDefs valueEncoding abiBytestringCode abiStaticLoopCode
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_dynarray_copy_loop_run:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv capacity src aty atv cs after child_names
      at_index copy_count src_data dst_data initial start.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 12) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
      (Var (compiler_var_name cs.cs_next_var 10)) ftv atv (dynarray_copy_start cenv dst fty capacity src aty cs) after /\
    fn_has_code (dyn_copy_prefix_state cs dst src capacity) (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    fn_has_code (dynarray_copy_start cenv dst fty capacity src aty cs) after func /\
    fn_has_code after (dynarray_copy_finish cs after) func /\
    copy_count < dimword(:256) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) initial = SOME (n2w copy_count) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 4)) initial = SOME dst_data /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 3)) initial = SOME src_data /\
    (!j. j < copy_count ==> value_has_type atv (at_index j)) /\
    w2n src_data + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_data + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) /\
    array_copy_loop_inv (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
      (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ftv atv at_index copy_count src_data dst_data initial 0 start ==>
    ?out. fragment_path ctx func start out /\
      array_copy_loop_inv (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
        (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ftv atv at_index copy_count src_data dst_data initial copy_count out
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all array_copy_compatible_values_wf >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `compiler_var_name cs.cs_next_var 5`,
    `fresh_label_output "typed_dyn_cond" cs.cs_next_label`, `compiler_var_names (cs.cs_next_var + 5) (8 + child_names)`,
    `ftv`, `atv`, `at_index`, `copy_count`, `src_data`, `dst_data`, `initial`, `start`] array_copy_loop_run) >> impl_tac
  >- (asm_simp_tac bool_ss [] >> MAP_EVERY qx_gen_tac [`i`, `current`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
      `value_has_type atv (at_index i)` by
        (qpat_x_assum `!j. j < copy_count ==> value_has_type _ _` (qspec_then `i` mp_tac) >> simp[]) >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`, `capacity`,
        `src`, `aty`, `atv`, `cs`, `after`, `child_names`, `at_index`, `copy_count`, `src_data`, `dst_data`, `initial`, `i`, `current`]
        checked_dynarray_copy_element_path) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC]) >> simp[]) >> simp[]
QED
