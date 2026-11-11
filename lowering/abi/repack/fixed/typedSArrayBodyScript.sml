(* TOP-LEVEL: the actual fixed-array address code, an arbitrary recursive
   child, and the parent back edge compose with full memory and operand frames. *)
Theory typedSArrayBody
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame
  typedSArrayChildContract typedSArrayLoop typedSArrayControl typedArrayLoopFrames
  typedDynLoopNames typedArrayLoopAddress typedArrayLoopCounter typedArrayLoopNames
  abiBytestringCode abiStaticLoopCode memoryValueDefs valueEncoding context compileEnv
  fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem sarray_copy_body_path:
  !ctx func cenv dst fty src aty copy_count cs ret cs' after child_names ss v ftv counter_word dst_data src_data.
    let dst_word = dst_data + counter_word * n2w (type_memory_bytes cenv fty) in
    let src_word = src_data + counter_word * n2w (type_memory_bytes cenv aty) in
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\ fn_has_code cs cs' func /\
    compile_store_memory_typed cenv (Var (compiler_var_name cs.cs_next_var 6)) fty
      (Var (compiler_var_name cs.cs_next_var 5)) aty
      (sarray_copy_start cenv dst fty src aty copy_count cs) = ((),after) /\
    child_names = after.cs_next_var - (cs.cs_next_var + 7) /\
    ss.vs_current_bb = fresh_label_output "typed_sa_body" (cs.cs_next_label + 1) /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_word /\
    eval_operand dst ss = SOME dst_data /\ eval_operand src ss = SOME src_data /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) /\
    (!child_ss.
      child_ss.vs_current_bb = (sarray_copy_start cenv dst fty src aty copy_count cs).cs_current_bb /\
      child_ss.vs_inst_idx = LENGTH (sarray_copy_start cenv dst fty src aty copy_count cs).cs_current_insts /\
      ~child_ss.vs_halted /\ child_ss.vs_memory = ss.vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 5)) child_ss = SOME src_word /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 6)) child_ss = SOME dst_word ==>
      ?copied. fragment_path ctx func child_ss copied /\ copy_state_frame child_ss copied /\
        copied.vs_current_bb = after.cs_current_bb /\ copied.vs_inst_idx = LENGTH after.cs_current_insts /\
        ~copied.vs_halted /\ memory_value_rel ftv v (w2n dst_word) copied.vs_memory /\
        (!other_tv other_v offset.
          memory_value_rel other_tv other_v offset child_ss.vs_memory /\ val_wf other_tv other_v /\
          (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
          memory_value_rel other_tv other_v offset copied.vs_memory) /\
        (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (cs.cs_next_var + 7) child_names) ==>
          eval_operand arg_op copied = eval_operand arg_op child_ss)) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
      out.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\
      out.vs_inst_idx = 0 /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 0)) out = SOME (counter_word + 1w) /\
      memory_value_rel ftv v (w2n dst_word) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all sarray_copy_child_counts >> strip_tac >> qpat_x_assum `child_names = _` kall_tac >>
  drule_all compile_copy_sarray_contains_child >> strip_tac >>
  `fn_has_code after (sarray_copy_finish cs after) func` by
    (qpat_assum `cs' = _` (fn th => PURE_REWRITE_TAC [SYM th]) >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `EVERY _ (compiler_var_names cs.cs_next_var (8 + child_names))`
    (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`dst`, `cs.cs_next_var`, `8 + child_names`, `[3;4;5]`] compiler_var_names_avoid_indices) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  mp_tac (Q.SPECL [`src`, `cs.cs_next_var`, `8 + child_names`, `[3;4]`] compiler_var_names_avoid_indices) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) compile_copy_sarray_loop_child_entry >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 0)) child_ss = SOME counter_word` by
    (qpat_x_assum `!arg_op. EVERY _ [3;4;5;6] ==> _`
       (qspec_then `Var (compiler_var_name cs.cs_next_var 0)` mp_tac) >> simp[]) >>
  qpat_x_assum `!child_ss. _` (qspec_then `child_ss` mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `copied` strip_assume_tac) >>
  qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `eval_operand (Var (compiler_var_name cs.cs_next_var 0)) copied = SOME counter_word` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `7`, `child_names`, `child_ss`, `copied`, `0`]
       compiler_operands_frame_before) >> impl_tac >- simp[] >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `fty`, `src`, `aty`, `copy_count`, `cs`, `after`,
    `copied`, `counter_word`] sarray_copy_loop_back_edge) >> impl_tac >- simp[] >> DISCH_TAC >>
  qabbrev_tac `final_ss = jump_to (fresh_label_output "typed_sa_cond" cs.cs_next_label)
    (typed_array_loop_counter_state after.cs_next_var (compiler_var_name cs.cs_next_var 0) counter_word copied)` >>
  `fragment_path ctx func ss final_ss` by
    (irule fragment_path_trans >> qexists_tac `child_ss` >> simp[] >>
     irule fragment_path_trans >> qexists_tac `copied` >> simp[Abbr`final_ss`]) >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
    eval_operand arg_op final_ss = eval_operand arg_op ss` by
    (mp_tac (Q.SPECL [`cs.cs_next_var`, `child_names`, `fresh_label_output "typed_sa_cond" cs.cs_next_label`,
       `counter_word`, `ss`, `child_ss`, `copied`] typed_array_loop_body_operand_frame) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[Abbr`final_ss`]) >>
  `final_ss.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\ final_ss.vs_inst_idx = 0 /\
   final_ss.vs_halted = copied.vs_halted /\ final_ss.vs_memory = copied.vs_memory /\
   eval_operand (Var (compiler_var_name cs.cs_next_var 0)) final_ss = SOME (counter_word + 1w)` by
    (mp_tac (Q.SPECL [`after.cs_next_var`, `compiler_var_name cs.cs_next_var 0`, `counter_word`,
       `fresh_label_output "typed_sa_cond" cs.cs_next_label`, `copied`] typed_array_loop_counter_jump_fields) >>
     simp_tac bool_ss [LET_THM, Abbr`final_ss`]) >>
  `copy_state_frame ss final_ss` by
    (irule copy_state_frame_trans >> qexists_tac `child_ss` >> simp[Abbr`final_ss`]) >>
  qexists_tac `final_ss` >> asm_simp_tac bool_ss [] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
