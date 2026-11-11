(* TOP-LEVEL: the actual recursive fixed-array parent closes the same typed
   copy contract as its child. Sparse defaults, real continuation blocks,
   and the compiler-derived allocation range are preserved. *)
Theory typedSArrayContract
Ancestors
  vyperEventArgCompat
  typedSArraySource typedSArrayChildContract typedSArrayLoop typedArrayLoopValues
  typedCopyContract typedArrayLoopCode typedSArrayDynInvariant checkedCopyAcyclic
  memoryValueDefs valueEncoding context compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem sarray_copy_exit_continuation:
  !cs after func.
    cut_continuation_no_phi (sarray_copy_finish cs after) func ==>
    ?exit_bb. lookup_block (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
      phi_prefix_length exit_bb.bb_instructions = 0
Proof
  simp[cut_continuation_no_phi_def, sarray_copy_finish_def, typed_array_loop_finish_def]
QED

Theorem checked_compile_copy_sarray_contract:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs' after.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    copy_count < dimword(:256) /\
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
      (Var (compiler_var_name cs.cs_next_var 5)) ftv atv (sarray_copy_start cenv dst fty src aty copy_count cs) after ==>
    typed_copy_contract ctx func dst src (ArrayTV ftv (Fixed copy_count)) (ArrayTV atv (Fixed copy_count)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qabbrev_tac `child_names = after.cs_next_var - (cs.cs_next_var + 7)` >>
  `child_names = after.cs_next_var - (cs.cs_next_var + 7)` by simp[Abbr`child_names`] >>
  drule_all sarray_copy_child_counts >> strip_tac >>
  simp_tac bool_ss [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_copy_sarray_contains_child >> strip_tac >>
  `cs'.cs_next_var - cs.cs_next_var = 8 + child_names` by
    (qpat_assum `cs' = _` (fn th => PURE_REWRITE_TAC [th]) >> decide_tac) >>
  `EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names))` by
    (qpat_x_assum `EVERY _ (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var))` mp_tac >>
     qpat_assum `cs'.cs_next_var - cs.cs_next_var = _` (fn th => simp_tac bool_ss [th])) >>
  drule value_has_type_sarray_cases >> disch_then (qx_choose_then `sparse` SUBST_ALL_TAC) >>
  qpat_assum `cs' = _` (fn eq => qpat_assum `cut_continuation_no_phi cs' func`
    (mp_tac o MATCH_MP sarray_copy_exit_continuation o PURE_REWRITE_RULE [eq])) >>
  disch_then (qx_choose_then `exit_bb` strip_assume_tac) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`, `after`, `child_names`, `sparse`,
    `ss`, `dst_addr`, `src_addr`, `exit_bb`] checked_sarray_copy_memory_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_assum `cs'.cs_next_var - cs.cs_next_var = _` (fn eq =>
    qpat_assum `!arg_op. EVERY _ (compiler_var_names cs.cs_next_var (8 + child_names)) ==> _`
      (ASSUME_TAC o PURE_REWRITE_RULE [SYM eq])) >>
  qexists_tac `out` >> simp_tac bool_ss [array_copy_frame_def, MULT_CLAUSES] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_typed_sarray_recursive_contract:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    copy_count < dimword(:256) /\
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_store_memory_typed cenv dst (ArrayT fty (Fixed copy_count))
      src (ArrayT aty (Fixed copy_count)) cs = (ret,cs') /\
    (!after. compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
        (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) ==>
      typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
        (Var (compiler_var_name cs.cs_next_var 5)) ftv atv (sarray_copy_start cenv dst fty src aty copy_count cs) after) ==>
    typed_copy_contract ctx func dst src (ArrayTV ftv (Fixed copy_count)) (ArrayTV atv (Fixed copy_count)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
  qpat_x_assum `compile_store_memory_typed _ _ (ArrayT _ _) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_typed_sarray_dispatch] >> DISCH_TAC >>
  drule_all compile_copy_sarray_loop_split >> disch_then (qx_choose_then `after` strip_assume_tac) >>
  qpat_x_assum `!after. _` (qspec_then `after` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`, `after`] checked_compile_copy_sarray_contract) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED
