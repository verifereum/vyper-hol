(* TOP-LEVEL: the actual fixed-array header composes with any verified
   recursive body, retaining its full element and operand frames. *)
Theory typedSArrayIteration
Ancestors
  typedCopyStateFrame typedCopyLoopStateFrame
  typedSArrayLoop typedArrayLoopFrames typedArrayLoopHeader typedSArrayDynInvariant
  abiBytestringCode abiStaticLoopCode abiStaticLoopBody memoryValueDefs valueEncoding
  context compileEnv fragBlockPath fragExec venomState venomInst list words arithmetic

Theorem sarray_copy_iteration_path:
  !ctx func cenv dst fty src aty copy_count cs ret cs' child_names ss v ftv i dst_data src_data.
    let dst_word = dst_data + n2w i * n2w (type_memory_bytes cenv fty) in
    ~(type_memory_bytes cenv fty = type_memory_bytes cenv aty /\ ~is_abi_dynamic cenv.ce_struct_fields fty) /\
    compile_copy_sarray_typed cenv dst fty src aty copy_count cs = (ret,cs') /\ fn_has_code cs cs' func /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) /\
    ss.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME (n2w i) /\
    eval_operand dst ss = SOME dst_data /\
    eval_operand src ss = SOME src_data /\
    i < copy_count /\ copy_count < dimword(:256) /\
    (!body_ss.
      body_ss.vs_current_bb = fresh_label_output "typed_sa_body" (cs.cs_next_label + 1) /\
      body_ss.vs_inst_idx = 0 /\ ~body_ss.vs_halted /\ body_ss.vs_memory = ss.vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 0)) body_ss = SOME (n2w i) /\
      eval_operand dst body_ss = SOME dst_data /\
      eval_operand src body_ss = SOME src_data ==>
      ?out. fragment_path ctx func body_ss out /\ copy_state_frame body_ss out /\
        out.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\
        out.vs_inst_idx = 0 /\ ~out.vs_halted /\
        eval_operand (Var (compiler_var_name cs.cs_next_var 0)) out = SOME (n2w i + 1w) /\
        memory_value_rel ftv v (w2n dst_word) out.vs_memory /\
        (!other_tv other_v offset.
          memory_value_rel other_tv other_v offset body_ss.vs_memory /\ val_wf other_tv other_v /\
          (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
          memory_value_rel other_tv other_v offset out.vs_memory) /\
        (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
          eval_operand arg_op out = eval_operand arg_op body_ss)) ==>
    ?out. fragment_path ctx func ss out /\ copy_state_frame ss out /\
      out.vs_current_bb = fresh_label_output "typed_sa_cond" cs.cs_next_label /\
      out.vs_inst_idx = 0 /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 0)) out = SOME (n2w (SUC i)) /\
      memory_value_rel ftv v (w2n dst_word) out.vs_memory /\
      (!other_tv other_v offset.
        memory_value_rel other_tv other_v offset ss.vs_memory /\ val_wf other_tv other_v /\
        (offset + type_memory_size other_tv <= w2n dst_word \/ w2n dst_word + type_memory_size ftv <= offset) ==>
        memory_value_rel other_tv other_v offset out.vs_memory) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all_then (qspec_then `ctx` ASSUME_TAC) compile_copy_sarray_loop_enter_body >>
  qabbrev_tac `body_ss = jump_to (fresh_label_output "typed_sa_body" (cs.cs_next_label + 1))
    (typed_array_loop_header_state cs.cs_next_var (n2w i) (n2w copy_count) ss)` >>
  `fragment_path ctx func ss body_ss` by simp[Abbr`body_ss`] >>
  `copy_state_frame ss body_ss` by simp[Abbr`body_ss`] >>
  `!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var (8 + child_names)) ==>
    eval_operand arg_op body_ss = eval_operand arg_op ss` by
    (qx_gen_tac `arg_op` >> DISCH_TAC >>
     mp_tac (Q.SPECL [`cs.cs_next_var`, `8 + child_names`, `(n2w i:bytes32)`, `(n2w copy_count:bytes32)`,
       `fresh_label_output "typed_sa_body" (cs.cs_next_label + 1)`, `ss`, `arg_op`]
       typed_array_loop_header_names_frame) >> impl_tac >- simp[] >> simp_tac bool_ss [Abbr`body_ss`]) >>
  drule_all compiler_operands_frame_pair >> strip_tac >>
  `body_ss.vs_current_bb = fresh_label_output "typed_sa_body" (cs.cs_next_label + 1) /\
   body_ss.vs_inst_idx = 0 /\ ~body_ss.vs_halted /\ body_ss.vs_memory = ss.vs_memory /\
   eval_operand (Var (compiler_var_name cs.cs_next_var 0)) body_ss = SOME (n2w i) /\
   eval_operand dst body_ss = SOME dst_data /\ eval_operand src body_ss = SOME src_data` by
    (asm_simp_tac bool_ss [] >>
     simp[Abbr`body_ss`, jump_to_def, eval_operand_jump_to_eq, typed_array_loop_header_operand_frame]) >>
  qpat_x_assum `!body_ss. _` (qspec_then `body_ss` mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qpat_x_assum `!other_tv other_v offset. _` mp_tac >> asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `body_ss` >> simp[]) >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `body_ss` >> simp[]) >>
  mp_tac (Q.SPECL [`compiler_var_names cs.cs_next_var (8 + child_names)`, `ss`, `body_ss`, `out`]
    compiler_operands_frame_trans) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss [word_add_n2w, ADD1] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary-child fixed-array iteration: " ^ name)
  end) (DB.thms "typedSArrayIteration")
