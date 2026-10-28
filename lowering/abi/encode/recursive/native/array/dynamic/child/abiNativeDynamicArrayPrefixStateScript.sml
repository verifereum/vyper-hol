(* TOP-LEVEL: actual array header/address execution changes only control
   and reserved SSA temporaries. Memory and allocator observations are
   unchanged, and all operands before its temporary interval survive. *)
Theory abiNativeDynamicArrayPrefixState
Ancestors
  abiDynamicLoopStep abiDynamicLoopCode abiAllocatorLoopState abiAllocatorState abiStateLoopFrame abiStateFrame
  abiMemoryFrame abiFieldOperands abiStaticLoopCode compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_prefix_context:
  !cs dst_addr root_addr width stride counter_addr dyn_addr length_word ss.
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride counter_addr dyn_addr length_word ss).vs_memory =
      ss.vs_memory /\
    abi_allocator_state (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr length_word ss) = abi_allocator_state ss /\
    abi_state_frame ss (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr length_word ss)
Proof
  rpt gen_tac >>
  qspecl_then [`cs.cs_next_var`, `cs.cs_next_label`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`,
    `length_word`, `ss`] mp_tac abi_dynamic_loop_child_state_values >>
  simp[LET_THM, abi_state_frame_def]
QED

Theorem abi_native_dynamic_array_prefix_old_operand:
  !cs dst_addr root_addr width stride counter_addr dyn_addr length_word ss arg_op.
    abi_operand_before (cs.cs_next_var + 3) arg_op ==>
    eval_operand arg_op (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr length_word ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> irule abi_dynamic_loop_child_state_operand_frame >>
  irule abi_operand_before_names >> qexists_tac `cs.cs_next_var + 3` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed runtime array child prefix state frame: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayPrefixState")
