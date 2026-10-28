(* TOP-LEVEL: shared operand and control-field frames for array loops.
   The recursive child's exact name count may be zero, and its code may
   introduce arbitrary blocks. *)
Theory typedArrayLoopFrames
Ancestors
  typedArrayLoopNames typedArrayLoopHeader typedArrayLoopCounter abiStaticLoopCode abiStaticLoopBody
  abiBytestringCode compileEnv venomState venomInst list words arithmetic

Theorem typed_array_loop_counter_jump_fields:
  !var_base counter counter_word cond_label ss.
    let out = jump_to cond_label (typed_array_loop_counter_state var_base counter counter_word ss) in
    out.vs_current_bb = cond_label /\ out.vs_inst_idx = 0 /\
    out.vs_halted = ss.vs_halted /\ out.vs_memory = ss.vs_memory /\
    eval_operand (Var counter) out = SOME (counter_word + 1w)
Proof
  simp[LET_THM, eval_operand_jump_to_eq, typed_array_loop_counter_value, jump_to_def]
QED

Theorem typed_array_loop_header_names_frame:
  !var_base num_names counter_word len_word label ss arg_op.
    3 <= num_names /\ EVERY (\name. arg_op <> Var name) (compiler_var_names var_base num_names) ==>
    eval_operand arg_op (jump_to label (typed_array_loop_header_state var_base counter_word len_word ss)) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`arg_op`, `var_base`, `num_names`, `[1;2]`] compiler_var_names_avoid_indices) >>
  impl_tac >- simp[] >> disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  simp[eval_operand_jump_to_eq, typed_array_loop_header_operand_frame]
QED

Theorem typed_array_loop_body_operand_frame:
  !var_base child_names cond_label counter_word initial addressed copied.
    (!arg_op. EVERY (\j. arg_op <> Var (compiler_var_name var_base j)) [3;4;5;6] ==>
      eval_operand arg_op addressed = eval_operand arg_op initial) /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 7) child_names) ==>
      eval_operand arg_op copied = eval_operand arg_op addressed) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_base (8 + child_names)) ==>
      eval_operand arg_op
        (jump_to cond_label (typed_array_loop_counter_state (var_base + 7 + child_names)
          (compiler_var_name var_base 0) counter_word copied)) = eval_operand arg_op initial
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`arg_op`, `var_base`, `8 + child_names`, `[0;3;4;5;6;7 + child_names]`]
    compiler_var_names_avoid_indices) >> impl_tac >- simp[] >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [compiler_var_name_add, ADD_ASSOC]) >>
  `EVERY (\j. arg_op <> Var (compiler_var_name var_base j)) [3;4;5;6]` by simp[compiler_var_name_add] >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 7) child_names)` by
    (mp_tac (Q.SPECL [`arg_op`, `var_base`, `8 + child_names`, `7`, `child_names`]
       compiler_var_names_avoid_segment) >> simp[]) >>
  `eval_operand arg_op (jump_to cond_label (typed_array_loop_counter_state (var_base + 7 + child_names)
     (compiler_var_name var_base 0) counter_word copied)) = eval_operand arg_op copied` by
    (simp_tac (srw_ss()) [eval_operand_jump_to_eq] >>
     irule typed_array_loop_counter_operand_frame >> simp[compiler_var_name_add, ADD_ASSOC] >>
     qpat_x_assum `arg_op <> Var (compiler_var_name var_base (7 + child_names))` mp_tac >> simp[ADD_COMM]) >>
  qpat_x_assum `!arg_op. EVERY _ [3;4;5;6] ==> _` (qspec_then `arg_op` mp_tac) >>
  qpat_x_assum `!arg_op. EVERY _ (compiler_var_names _ _) ==> _` (qspec_then `arg_op` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed shared array-loop operand frames: " ^ name)
  end) (DB.thms "typedArrayLoopFrames")
