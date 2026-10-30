(* TOP-LEVEL: a checked dynamic-array body executes a recursive child
   satisfying the raw typed-copy contract. Actual compiler metadata and
   whole live-payload separation establish every child precondition. *)
Theory typedDynLoopElement
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame
  typedDynLoopSafety typedDynChildContract typedCopyContract typedDynLoopBody
  typedDynLoopIteration typedDynLoopValues typedDynLoopInvariant typedDynLoopNames
  typedDynLoopCode typedDynLoopStructure typedArrayCopyMemory typedSArrayDynInvariant
  memoryValueDefs valueEncoding abiBytestringCode abiStaticLoopCode
  context compileEnv compileVyper vyperTypeContract vyperContext vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_dynarray_copy_body_path:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv capacity src aty atv cs after child_names
      ss v i copy_count dst_data src_data.
    let dst_word = dst_data + n2w i * n2w (type_memory_bytes cenv fty) in
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 12) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
      (Var (compiler_var_name cs.cs_next_var 10)) ftv atv (dynarray_copy_start cenv dst fty capacity src aty cs) after /\
    fn_has_code (dyn_copy_prefix_state cs dst src capacity) (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    fn_has_code (dynarray_copy_start cenv dst fty capacity src aty cs) after func /\
    fn_has_code after (dynarray_copy_finish cs after) func /\
    ss.vs_current_bb = fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1) /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME (n2w i) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 4)) ss = SOME dst_data /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 3)) ss = SOME src_data /\
    i < copy_count /\ value_has_type atv v /\
    memory_value_rel atv v (w2n src_data + i * type_memory_size atv) ss.vs_memory /\
    w2n src_data + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_data + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
      out.vs_current_bb = fresh_label_output "typed_dyn_cond" cs.cs_next_label /\ out.vs_inst_idx = 0 /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 5)) out = SOME (n2w i + 1w) /\
      memory_value_rel ftv v (w2n dst_word) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `cenv`, `fty`, `aty`, `ftv`, `atv`,
    `src_data`, `dst_data`, `copy_count`, `i`] checked_dynarray_copy_element_safety) >> simp_tac bool_ss [LET_THM] >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`, `after`, `child_names`,
    `ss`, `v`, `ftv`, `(n2w i:bytes32)`, `dst_data`, `src_data`] dynarray_copy_body_path) >>
  simp_tac bool_ss [LET_THM] >> impl_tac
  >- (asm_simp_tac (srw_ss()) [] >> qx_gen_tac `child_ss` >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
      mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`, `after`, `ftv`, `atv`,
        `child_ss`, `v`, `dst_data + n2w i * n2w (type_memory_bytes cenv fty)`,
        `src_data + n2w i * n2w (type_memory_bytes cenv aty)`] dynarray_copy_child_contract_path) >>
      impl_tac >- asm_simp_tac (srw_ss()) [] >>
      disch_then (qx_choose_then `copied` strip_assume_tac) >>
      qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
      qpat_x_assum `memory_value_rel ftv _ _ copied.vs_memory` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
      qexists_tac `copied` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qpat_x_assum `memory_value_rel ftv _ _ out.vs_memory` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_dynarray_copy_element_path:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv capacity src aty atv cs after child_names
      at_index copy_count src_data dst_data initial i current.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 12) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 11))
      (Var (compiler_var_name cs.cs_next_var 10)) ftv atv (dynarray_copy_start cenv dst fty capacity src aty cs) after /\
    fn_has_code (dyn_copy_prefix_state cs dst src capacity) (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    fn_has_code (dynarray_copy_start cenv dst fty capacity src aty cs) after func /\
    fn_has_code after (dynarray_copy_finish cs after) func /\
    i < copy_count /\ copy_count < dimword(:256) /\ value_has_type atv (at_index i) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) initial = SOME (n2w copy_count) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 4)) initial = SOME dst_data /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 3)) initial = SOME src_data /\
    w2n src_data + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_data + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) /\
    array_copy_loop_inv (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
      (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ftv atv at_index copy_count src_data dst_data initial i current ==>
    ?out. fragment_path ctx func current out /\ copy_state_frame current out /\
      out.vs_current_bb = fresh_label_output "typed_dyn_cond" cs.cs_next_label /\ out.vs_inst_idx = 0 /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 5)) out = SOME (n2w (SUC i)) /\
      memory_value_rel ftv (at_index i) (w2n dst_data + i * type_memory_size ftv) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset current.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_data + i * type_memory_size ftv \/
          w2n dst_data + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op current)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule array_copy_loop_inv_saved_prefix >> DISCH_TAC >>
  qpat_x_assum `array_copy_loop_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_copy_loop_inv_def] >> strip_tac >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 0)) current = SOME (n2w copy_count) /\
   eval_operand (Var (compiler_var_name cs.cs_next_var 4)) current = SOME dst_data /\
   eval_operand (Var (compiler_var_name cs.cs_next_var 3)) current = SOME src_data` by
    (qpat_x_assum `!j. j < 5 ==> _` (fn th => MAP_EVERY mp_tac (map (fn j => Q.SPEC j th) [`0`,`4`,`3`])) >> simp[]) >>
  drule_all array_copy_memory_inv_source >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `cenv`, `fty`, `aty`, `ftv`, `atv`,
    `src_data`, `dst_data`, `copy_count`, `i`] checked_dynarray_copy_element_safety) >> simp_tac bool_ss [LET_THM] >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`, `child_names`,
    `current`, `(at_index:num -> value) i`, `ftv`, `i`, `copy_count`, `dst_data`, `src_data`] dynarray_copy_iteration_path) >>
  simp_tac bool_ss [LET_THM] >> impl_tac
  >- (asm_simp_tac (srw_ss()) [] >> qx_gen_tac `body_ss` >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`, `capacity`,
        `src`, `aty`, `atv`, `cs`, `after`, `child_names`, `body_ss`, `(at_index:num -> value) i`, `i`, `copy_count`,
        `dst_data`, `src_data`] checked_dynarray_copy_body_path) >> simp_tac bool_ss [LET_THM] >>
      impl_tac >- asm_simp_tac (srw_ss()) [] >>
      disch_then (qx_choose_then `copied` strip_assume_tac) >>
      qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
      qpat_x_assum `memory_value_rel ftv _ _ copied.vs_memory` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
      qexists_tac `copied` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qpat_x_assum `memory_value_rel ftv _ _ out.vs_memory` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
