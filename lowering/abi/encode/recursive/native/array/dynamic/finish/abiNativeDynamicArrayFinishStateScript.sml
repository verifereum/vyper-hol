(* TOP-LEVEL: the actual completed-loop exit changes only control and new
   SSA temporaries. Memory, allocator state, external state and earlier
   operands are preserved for the enclosing native result. *)
Theory abiNativeDynamicArrayFinishState
Ancestors
  abiDynamicLoopFinish abiAllocatorLoopState abiAllocatorState abiStateLoopFrame abiStateFrame
  abiMemoryFrame abiFieldOperands abiStaticLoopCode abiBytestringCode compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_finish_context:
  !mid cs root_addr counter_addr dyn_addr length_word ss.
    (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label root_addr counter_addr dyn_addr length_word ss).vs_memory =
      ss.vs_memory /\
    abi_allocator_state (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
      root_addr counter_addr dyn_addr length_word ss) = abi_allocator_state ss /\
    abi_state_frame ss (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
      root_addr counter_addr dyn_addr length_word ss) /\
    abi_memory_frame [] ss (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
      root_addr counter_addr dyn_addr length_word ss)
Proof
  rpt gen_tac >>
  qspecl_then [`mid.cs_next_var`, `cs.cs_next_var`, `cs.cs_next_label`, `root_addr`, `counter_addr`, `dyn_addr`, `length_word`, `ss`]
    mp_tac abi_dynamic_loop_finish_values >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_state_frame_def, abi_memory_frame_def, read_memory_def]
QED

Theorem abi_native_dynamic_array_finish_old_operand:
  !mid cs root_addr counter_addr dyn_addr length_word ss arg_op.
    cs.cs_next_var + 15 <= mid.cs_next_var /\ abi_operand_before (cs.cs_next_var + 3) arg_op ==>
    eval_operand arg_op (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
      root_addr counter_addr dyn_addr length_word ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs.cs_next_var + 3`, `arg_op`, `cs.cs_next_var + 3`, `3`] mp_tac abi_operand_before_names >>
  impl_tac >- simp[] >>
  simp_tac (srw_ss()) [compiler_var_names_def, GENLIST, compiler_var_name_def, GSYM ADD_ASSOC] >> strip_tac >>
  `EVERY (\name. arg_op <> Var name) (compiler_var_names (mid.cs_next_var + 2) 3)` by
    (irule abi_operand_before_names >> qexists_tac `cs.cs_next_var + 3` >> asm_simp_tac bool_ss [] >> decide_tac) >>
  irule abi_dynamic_loop_finish_operand_frame >> asm_simp_tac (srw_ss()) [compiler_var_name_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual completed array exit state and operand frames: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayFinishState")
