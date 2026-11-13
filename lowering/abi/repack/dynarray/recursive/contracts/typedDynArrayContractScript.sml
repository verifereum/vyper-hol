(* TOP-LEVEL: close the recursive dynamic-array parent contract from the
   actual child contract. Continuation and name-range obligations use the
   real compiler cuts, so the result can itself serve as a recursive child. *)
Theory typedDynArrayContract
Ancestors
  vyperEventArgCompat
  typedDynLoopSource typedDynChildContract typedDynLoopNames typedCopyContract
  typedDynLoopCode typedArrayLoopCode typedSArrayDynSafety typedSArrayDynInvariant
  memoryValueDefs valueEncoding context compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem dynarray_copy_exit_continuation:
  !cs after func.
    cut_continuation_no_phi (dynarray_copy_finish cs after) func ==>
    ?exit_bb. lookup_block (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
      phi_prefix_length exit_bb.bb_instructions = 0
Proof
  simp[cut_continuation_no_phi_def, dynarray_copy_finish_def, typed_array_loop_finish_def]
QED

Theorem checked_compile_copy_dynarray_contract:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv capacity src aty atv src_capacity cs ret cs' after.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\ fty <> aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    src_capacity <= capacity /\ capacity < dimword(:256) /\
    compile_copy_dynarray_typed cenv dst fty capacity src aty cs = (ret,cs') /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
      (Var (compiler_var_name cs.cs_next_var 10)) ftv atv (dynarray_copy_start cenv dst fty capacity src aty cs) after ==>
    typed_copy_contract ctx func dst src (ArrayTV ftv (Dynamic capacity)) (ArrayTV atv (Dynamic src_capacity)) cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all dynarray_copy_child_names >> disch_then (qx_choose_then `child_names` strip_assume_tac) >>
  `child_names = after.cs_next_var - (cs.cs_next_var + 12)` by decide_tac >>
  simp_tac bool_ss [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ fty = aty)` by simp[] >>
  drule_all compile_copy_dynarray_contains_child >> strip_tac >>
  `cs'.cs_next_var - cs.cs_next_var = 13 + child_names` by
    (qpat_assum `cs' = _` (fn th => PURE_REWRITE_TAC [th]) >> decide_tac) >>
  `EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (13 + child_names))` by
    (qpat_x_assum `EVERY _ (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var))` mp_tac >>
     qpat_assum `cs'.cs_next_var - cs.cs_next_var = _` (fn th => simp_tac bool_ss [th])) >>
  drule value_has_type_dynarray_cases >> disch_then (qx_choose_then `vs` SUBST_ALL_TAC) >>
  qpat_assum `cs' = _` (fn eq => qpat_assum `cut_continuation_no_phi cs' func`
    (mp_tac o MATCH_MP dynarray_copy_exit_continuation o PURE_REWRITE_RULE [eq])) >>
  disch_then (qx_choose_then `exit_bb` strip_assume_tac) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `capacity`, `src`, `aty`, `atv`, `src_capacity`, `vs`, `cs`, `ret`, `cs'`, `after`, `child_names`,
    `ss`, `dst_addr`, `src_addr`, `exit_bb`] checked_compile_copy_dynarray_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_assum `cs'.cs_next_var - cs.cs_next_var = _` (fn eq =>
    qpat_assum `!arg_op. EVERY _ (compiler_var_names cs.cs_next_var (13 + child_names)) ==> _`
      (ASSUME_TAC o PURE_REWRITE_RULE [SYM eq])) >>
  qexists_tac `out` >> simp_tac bool_ss [array_copy_frame_def, MULT_CLAUSES] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
