(* TOP-LEVEL: the actual recursive dynamic-array body preserves operands
   outside its parent/address names, arbitrary child range and footer.
   The child's allocation count may be zero. *)
Theory typedDynLoopBodyFrames
Ancestors
  typedArrayLoopFrames typedArrayLoopNames typedArrayLoopHeader typedArrayLoopCounter abiStaticLoopCode abiStaticLoopBody
  abiBytestringCode compileEnv venomState venomInst list words arithmetic

Theorem typed_array_loop_counter_jump_fields = typedArrayLoopFramesTheory.typed_array_loop_counter_jump_fields;

Theorem typed_array_loop_header_names_frame = typedArrayLoopFramesTheory.typed_array_loop_header_names_frame;

Theorem dynarray_copy_body_operand_frame:
  !var_base child_names cond_label counter_word initial addressed copied.
    (!arg_op. EVERY (\j. arg_op <> Var (compiler_var_name (var_base + 5) j)) [3;4;5;6] ==>
      eval_operand arg_op addressed = eval_operand arg_op initial) /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 12) child_names) ==>
      eval_operand arg_op copied = eval_operand arg_op addressed) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 5) (8 + child_names)) ==>
      eval_operand arg_op
        (jump_to cond_label (typed_array_loop_counter_state (var_base + 12 + child_names)
          (compiler_var_name var_base 5) counter_word copied)) = eval_operand arg_op initial
Proof
  rpt gen_tac >>
  `var_base + 5 + 7 = var_base + 12` by decide_tac >>
  `compiler_var_name (var_base + 5) 0 = compiler_var_name var_base 5` by simp[compiler_var_name_add] >>
  mp_tac (Q.SPECL [`var_base + 5`, `child_names`, `cond_label`, `counter_word`,
    `initial`, `addressed`, `copied`] typed_array_loop_body_operand_frame) >>
  asm_simp_tac bool_ss []
QED
