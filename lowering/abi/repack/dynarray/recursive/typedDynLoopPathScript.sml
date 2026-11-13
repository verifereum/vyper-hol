(* TOP-LEVEL: compose the actual checked loop entry, arbitrary recursive
   children and the exit into a complete payload path. Continuation PHIs
   are checked at the real emitted exit block. *)
Theory typedDynLoopPath
Ancestors
  vyperEventArgCompat
  typedCopyStateFrame typedCopyLoopStateFrame
  typedDynLoopCheckedRun typedDynLoopEntry typedDynLoopValues typedDynLoopInvariant
  typedDynLoopBodyFrames typedDynLoopCode typedDynLoopControl typedDynLoopStructure
  typedDynChildContract typedCopyContract typedArrayLoopCode typedArrayLoopHeader typedSArrayDynInvariant
  abiBytestringCode abiStaticLoopCode abiStaticLoopBody memoryValueDefs valueEncoding
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem dynarray_copy_loop_end:
  !ctx func cenv dst fty capacity src aty cs after child_names ftv atv at_index copy_count
      src_data dst_data initial current exit_bb.
    fn_has_code (dyn_copy_prefix_state cs dst src capacity) (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) initial = SOME (n2w copy_count) /\
    array_copy_loop_inv (compiler_var_name cs.cs_next_var 5) (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
      (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ftv atv at_index copy_count src_data dst_data initial copy_count current /\
    lookup_block (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    ?out. fragment_path ctx func current out /\ copy_state_frame initial out /\ out.vs_current_bb = (dynarray_copy_finish cs after).cs_current_bb /\
      out.vs_inst_idx = LENGTH (dynarray_copy_finish cs after).cs_current_insts /\ ~out.vs_halted /\
      array_copy_memory_inv ftv atv at_index copy_count (w2n src_data) (w2n dst_data)
        initial.vs_memory copy_count out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op initial)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule array_copy_loop_inv_saved_prefix >> DISCH_TAC >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 0)) current = SOME (n2w copy_count)` by
    (qpat_x_assum `!j. j < 5 ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `array_copy_loop_inv _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_copy_loop_inv_def] >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`,
    `current`, `copy_count`, `exit_bb`] dynarray_copy_loop_exit) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qabbrev_tac `final_ss = jump_to (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2))
    (typed_array_loop_header_state (cs.cs_next_var + 5) (n2w copy_count) (n2w copy_count) current)` >>
  `final_ss.vs_current_bb = (dynarray_copy_finish cs after).cs_current_bb /\
   final_ss.vs_inst_idx = LENGTH (dynarray_copy_finish cs after).cs_current_insts /\
   final_ss.vs_halted = current.vs_halted /\ final_ss.vs_memory = current.vs_memory` by
    simp[Abbr`final_ss`, jump_to_def, dynarray_copy_finish_def, typed_array_loop_finish_def] >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
    eval_operand arg_op final_ss = eval_operand arg_op initial` by
    (qx_gen_tac `arg_op` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. _ ==> eval_operand _ current = _` (qspec_then `arg_op` mp_tac) >>
     impl_tac >- simp[] >> DISCH_TAC >>
     mp_tac (Q.SPECL [`cs.cs_next_var + 5`, `8 + child_names`, `(n2w copy_count:bytes32)`, `(n2w copy_count:bytes32)`,
       `fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)`, `current`, `arg_op`]
       typed_array_loop_header_names_frame) >> impl_tac >- simp[] >> simp[Abbr`final_ss`]) >>
  `copy_state_frame initial final_ss` by simp[Abbr`final_ss`] >>
  qexists_tac `final_ss` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_dynarray_copy_payload_path:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv capacity src aty atv cs after child_names
      at_index copy_count src_data dst_data ss exit_bb.
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
    ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH (dyn_copy_prefix_state cs dst src capacity).cs_current_insts /\ ~ss.vs_halted /\
    copy_count < dimword(:256) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME (n2w copy_count) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 4)) ss = SOME dst_data /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 3)) ss = SOME src_data /\
    (!j. j < copy_count ==> value_has_type atv (at_index j)) /\
    array_copy_prefix atv at_index copy_count (w2n src_data) ss.vs_memory /\
    w2n src_data + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_data + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_data + copy_count * type_memory_size atv <= w2n dst_data \/
      w2n dst_data + copy_count * type_memory_size ftv <= w2n src_data) /\
    lookup_block (fresh_label_output "typed_dyn_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = (dynarray_copy_finish cs after).cs_current_bb /\
      out.vs_inst_idx = LENGTH (dynarray_copy_finish cs after).cs_current_insts /\ ~out.vs_halted /\
      array_copy_memory_inv ftv atv at_index copy_count (w2n src_data) (w2n dst_data)
        ss.vs_memory copy_count out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`, `child_names`, `ftv`, `atv`,
    `at_index`, `copy_count`, `src_data`, `dst_data`, `ss`] dynarray_copy_loop_begin) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `start` strip_assume_tac) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`, `capacity`,
    `src`, `aty`, `atv`, `cs`, `after`, `child_names`, `at_index`, `copy_count`, `src_data`, `dst_data`, `ss`, `start`]
    checked_dynarray_copy_loop_run) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `header_ss` strip_assume_tac) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`, `after`, `child_names`, `ftv`, `atv`,
    `at_index`, `copy_count`, `src_data`, `dst_data`, `ss`, `header_ss`, `exit_bb`] dynarray_copy_loop_end) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `start` >> simp[] >>
     irule fragment_path_trans >> qexists_tac `header_ss` >> simp[]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
