(* TOP-LEVEL: compose the actual dynamic-array addresses, a verified
   recursive child path and the parent's counter/back edge. The child may
   allocate arbitrary names and emit arbitrary additional blocks. *)
Theory typedDynLoopBody
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame
  typedDynLoopBodyFrames typedDynLoopCode typedDynLoopControl typedDynLoopStructure
  typedDynLoopNames typedCopyVarFlow typedArrayLoopAddress typedArrayLoopCounter
  abiBytestringCode abiStaticLoopCode memoryValueDefs valueEncoding context compileEnv
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem dynarray_copy_body_path:
  !ctx func cenv dst fty capacity src aty cs after child_names ss v ftv counter_word dst_data src_data.
    let dst_word = dst_data + counter_word * n2w (type_memory_bytes cenv fty) in
    let src_word = src_data + counter_word * n2w (type_memory_bytes cenv aty) in
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 11)) fty
      (Var (compiler_var_name cs.cs_next_var 10)) aty
      (dynarray_copy_start cenv dst fty capacity src aty cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 12) /\
    fn_has_code (dyn_copy_prefix_state cs dst src capacity)
      (dynarray_copy_start cenv dst fty capacity src aty cs) func /\
    fn_has_code after (dynarray_copy_finish cs after) func /\
    ss.vs_current_bb = fresh_label_output "typed_dyn_body" (cs.cs_next_label + 1) /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 5)) ss = SOME counter_word /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 4)) ss = SOME dst_data /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 3)) ss = SOME src_data /\
    (!child_ss.
      child_ss.vs_current_bb = (dynarray_copy_start cenv dst fty capacity src aty cs).cs_current_bb /\
      child_ss.vs_inst_idx = LENGTH (dynarray_copy_start cenv dst fty capacity src aty cs).cs_current_insts /\
      ~child_ss.vs_halted /\ child_ss.vs_memory = ss.vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 10)) child_ss = SOME src_word /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 11)) child_ss = SOME dst_word ==>
      ?copied. fragment_path ctx func child_ss copied /\ copy_state_frame child_ss copied /\
        copied.vs_current_bb = after.cs_current_bb /\ copied.vs_inst_idx = LENGTH after.cs_current_insts /\
        ~copied.vs_halted /\ memory_value_rel ftv v (w2n dst_word) copied.vs_memory /\
        (!other_tv other_v offset.
          memory_value_rel other_tv other_v offset child_ss.vs_memory /\ val_wf other_tv other_v /\
          (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
          memory_value_rel other_tv other_v offset copied.vs_memory) /\
        (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 12) child_names) ==>
          eval_operand arg_op copied = eval_operand arg_op child_ss)) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
      out.vs_current_bb = fresh_label_output "typed_dyn_cond" cs.cs_next_label /\
      out.vs_inst_idx = 0 /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 5)) out = SOME (counter_word + 1w) /\
      memory_value_rel ftv v (w2n dst_word) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_then (ASSUME_TAC o SIMP_RULE (srw_ss()) []) compile_store_memory_typed_next_var >>
  `after.cs_next_var = cs.cs_next_var + 12 + child_names` by decide_tac >>
  qpat_x_assum `child_names = _` kall_tac >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) dynarray_copy_loop_child_entry >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 5)) child_ss = SOME counter_word` by
    (qpat_x_assum `!arg_op. EVERY _ [3;4;5;6] ==> _`
       (qspec_then `Var (compiler_var_name cs.cs_next_var 5)` mp_tac) >>
     impl_tac >- simp[compiler_var_name_add] >> simp[]) >>
  qpat_x_assum `!child_ss. _` (qspec_then `child_ss` mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `copied` strip_assume_tac) >>
  qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 5)) copied = SOME counter_word` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `12`, `child_names`, `child_ss`, `copied`, `5`]
       compiler_operands_frame_before) >> impl_tac >- simp[] >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `capacity`, `src`, `aty`, `cs`, `after`,
    `copied`, `counter_word`] dynarray_copy_loop_back_edge) >> impl_tac >- simp[] >> DISCH_TAC >>
  qabbrev_tac `final_ss = jump_to (fresh_label_output "typed_dyn_cond" cs.cs_next_label)
    (typed_array_loop_counter_state after.cs_next_var (compiler_var_name cs.cs_next_var 5) counter_word copied)` >>
  `fragment_path ctx func ss final_ss` by
    (irule fragment_path_trans >> qexists_tac `child_ss` >> simp[] >>
     irule fragment_path_trans >> qexists_tac `copied` >> simp[Abbr`final_ss`]) >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 5) (8 + child_names)) ==>
    eval_operand arg_op final_ss = eval_operand arg_op ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `child_names`, `fresh_label_output "typed_dyn_cond" cs.cs_next_label`,
       `counter_word`, `ss`, `child_ss`, `copied`] dynarray_copy_body_operand_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[Abbr`final_ss`]) >>
  `final_ss.vs_current_bb = fresh_label_output "typed_dyn_cond" cs.cs_next_label /\ final_ss.vs_inst_idx = 0 /\
   final_ss.vs_halted = copied.vs_halted /\ final_ss.vs_memory = copied.vs_memory /\
   eval_operand (Var (compiler_var_name cs.cs_next_var 5)) final_ss = SOME (counter_word + 1w)` by
    (mp_tac (Q.SPECL [`after.cs_next_var`, `compiler_var_name cs.cs_next_var 5`, `counter_word`,
       `fresh_label_output "typed_dyn_cond" cs.cs_next_label`, `copied`] typed_array_loop_counter_jump_fields) >>
     simp_tac bool_ss [LET_THM, Abbr`final_ss`]) >>
  `copy_state_frame ss final_ss` by
    (irule copy_state_frame_trans >> qexists_tac `child_ss` >> simp[Abbr`final_ss`]) >>
  qexists_tac `final_ss` >> asm_simp_tac bool_ss [] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  qpat_x_assum `!arg_op. EVERY _ (compiler_var_names _ (8 + child_names)) ==> _` mp_tac >> simp[ADD_ASSOC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary-child dynamic-array body path: " ^ name)
  end) (DB.thms "typedDynLoopBody")
