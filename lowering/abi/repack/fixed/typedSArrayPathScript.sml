(* TOP-LEVEL: the complete actual recursive fixed-array loop reaches its
   continuation with full source, target-prefix and memory/operand frames. *)
Theory typedSArrayPath
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame
  typedSArrayRun typedSArrayLoop typedSArrayControl typedSArrayChildContract typedCopyContract
  typedDynLoopEntry typedDynLoopInvariant typedArrayLoopFrames typedArrayLoopCode
  typedArrayLoopNames typedSArrayDynInvariant abiBytestringCode abiStaticLoopCode
  memoryValueDefs valueEncoding context compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem checked_sarray_copy_path:
  !tops in_deploy layouts addr art ctx func cenv dst fty ftv src aty atv copy_count cs ret cs' after child_names
      at_index ss dst_addr src_addr exit_bb.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\ fn_has_code cs cs' func /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 7) /\
    typed_copy_contract ctx func (Var (compiler_var_name cs.cs_next_var 6))
      (Var (compiler_var_name cs.cs_next_var 5)) ftv atv (sarray_copy_start cenv dst fty src aty copy_count cs) after /\
    copy_count < dimword(:256) /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) /\
    (!j. j < copy_count ==> value_has_type atv (at_index j)) /\
    array_copy_prefix atv at_index copy_count (w2n src_addr) ss.vs_memory /\
    w2n src_addr + copy_count * type_memory_size atv < dimword(:256) /\
    w2n dst_addr + copy_count * type_memory_size ftv < dimword(:256) /\
    (w2n src_addr + copy_count * type_memory_size atv <= w2n dst_addr \/
      w2n dst_addr + copy_count * type_memory_size ftv <= w2n src_addr) /\
    lookup_block (fresh_label_output "typed_sa_exit" (cs.cs_next_label + 2)) func.fn_blocks = SOME exit_bb /\
    phi_prefix_length exit_bb.bb_instructions = 0 ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\ out.vs_current_bb = cs'.cs_current_bb /\
      out.vs_inst_idx = LENGTH cs'.cs_current_insts /\ ~out.vs_halted /\
      array_copy_memory_inv ftv atv at_index copy_count (w2n src_addr) (w2n dst_addr)
        ss.vs_memory copy_count out.vs_memory /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all_then (qspec_then `ctx` ASSUME_TAC) compile_copy_sarray_loop_entry >>
  `MEM (compiler_var_name cs.cs_next_var 0) (compiler_var_names cs.cs_next_var (8 + child_names))` by
    (simp[compiler_var_name_def, compiler_var_names_def, MEM_GENLIST] >> qexists_tac `0` >> simp[]) >>
  qabbrev_tac `entry_ss = jump_to (fresh_label_output "typed_sa_cond" cs.cs_next_label)
    (update_var (compiler_var_name cs.cs_next_var 0) 0w ss)` >>
  `array_copy_loop_inv (compiler_var_name cs.cs_next_var 0) (fresh_label_output "typed_sa_cond" cs.cs_next_label)
    (compiler_var_names cs.cs_next_var (8 + child_names)) ftv atv at_index copy_count src_addr dst_addr ss 0 entry_ss` by
    (simp_tac bool_ss [Abbr`entry_ss`] >> irule array_copy_loop_inv_initial >> simp[]) >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `dst`, `fty`, `ftv`,
    `src`, `aty`, `atv`, `copy_count`, `cs`, `ret`, `cs'`, `after`, `child_names`, `at_index`, `src_addr`, `dst_addr`,
    `ss`, `entry_ss`] checked_sarray_copy_loop_run) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `header_ss` strip_assume_tac) >>
  qpat_x_assum `array_copy_loop_inv _ _ _ _ _ _ _ _ _ _ _ header_ss` mp_tac >>
  PURE_REWRITE_TAC [array_copy_loop_inv_def] >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `src`, `aty`, `copy_count`, `cs`, `ret`, `cs'`,
    `header_ss`, `exit_bb`] compile_copy_sarray_loop_exit) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qabbrev_tac `final_ss = jump_to cs'.cs_current_bb
    (typed_array_loop_header_state cs.cs_next_var (n2w copy_count) (n2w copy_count) header_ss)` >>
  `fragment_path ctx func ss final_ss` by
    (irule fragment_path_trans >> qexists_tac `entry_ss` >> simp[] >>
     irule fragment_path_trans >> qexists_tac `header_ss` >> simp[]) >>
  `final_ss.vs_current_bb = cs'.cs_current_bb /\ final_ss.vs_inst_idx = 0 /\
   final_ss.vs_halted = header_ss.vs_halted /\ final_ss.vs_memory = header_ss.vs_memory` by
    simp[Abbr`final_ss`, jump_to_def] >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
    eval_operand arg_op final_ss = eval_operand arg_op ss` by
    (qx_gen_tac `arg_op` >> DISCH_TAC >>
     qpat_x_assum `!arg_op. _ ==> eval_operand _ header_ss = _` (qspec_then `arg_op` mp_tac) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
     mp_tac (Q.SPECL [`cs.cs_next_var`, `8 + child_names`, `(n2w copy_count:bytes32)`, `(n2w copy_count:bytes32)`,
       `cs'.cs_current_bb`, `header_ss`, `arg_op`] typed_array_loop_header_names_frame) >>
     impl_tac >- simp[] >> simp[Abbr`final_ss`]) >>
  `copy_state_frame ss final_ss` by simp[Abbr`final_ss`] >>
  qexists_tac `final_ss` >> asm_simp_tac bool_ss [LENGTH] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete recursive fixed-array path: " ^ name)
  end) (DB.thms "typedSArrayPath")
