(* TOP-LEVEL: the two separately allocated cells contain the initialized
   index and tail values, and their actual SSA pointers reach the header. *)
Theory abiNativeDynamicArrayStartValues
Ancestors
  abiNativeDynamicArrayStartState abiDynamicLoopEntryFrames abiDynamicLoopEntry abiDynamicLoopRun abiDynamicLoopCode
  abiAllocatedWindows abiStaticLoopBody abiStaticLoopEntry abiStaticLoopCode abiFieldOperands
  compileEnv fragExec venomMemDefs venomState list pair words arithmetic

Theorem abi_native_dynamic_array_start_values:
  !cs width length_word ss.
    alloca_inv (abi_native_dynamic_array_start_state cs width length_word ss) /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width length_word ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width length_word ss) (cs.cs_next_id + 2)
      (w2n (abi_native_dynamic_array_tail_addr cs ss)) 32 ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) (abi_native_dynamic_array_start_state cs width length_word ss) =
      SOME (abi_static_loop_counter_addr cs.cs_next_id ss) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) (abi_native_dynamic_array_start_state cs width length_word ss) =
      SOME (abi_native_dynamic_array_tail_addr cs ss) /\
    mload (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) (abi_native_dynamic_array_start_state cs width length_word ss) = 0w /\
    mload (w2n (abi_native_dynamic_array_tail_addr cs ss)) (abi_native_dynamic_array_start_state cs width length_word ss) = length_word * n2w width
Proof
  rpt gen_tac >> strip_tac >>
  `allocas_non_overlapping (abi_native_dynamic_array_start_state cs width length_word ss)` by fs[alloca_inv_def] >>
  `regions_disjoint (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32
    (w2n (abi_native_dynamic_array_tail_addr cs ss)) 32` by
    (qspecl_then [`abi_native_dynamic_array_start_state cs width length_word ss`,
       `(cs.cs_next_id,(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32))`,
       `(cs.cs_next_id + 2,(w2n (abi_native_dynamic_array_tail_addr cs ss),32))`]
       mp_tac abi_allocated_window_disjoint >> impl_tac >- simp[] >> simp[]) >>
  qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`, `width`, `length_word`, `ss`] mp_tac abi_dynamic_loop_entry_values >>
  impl_tac >- first_assum (MATCH_ACCEPT_TAC o PURE_REWRITE_RULE [abi_native_dynamic_array_tail_addr_def]) >>
  simp_tac bool_ss [abi_native_dynamic_array_start_state_def, abi_native_dynamic_array_tail_addr_def,
    eval_operand_jump_to_eq, memory_reads_jump_to]
QED

Theorem abi_native_dynamic_array_start_ready:
  !cs dst src len_op dst_addr root_addr width loop_count ss.
    alloca_inv (abi_native_dynamic_array_start_state cs width (n2w loop_count) ss) /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w loop_count) ss) cs.cs_next_id
      (w2n (abi_static_loop_counter_addr cs.cs_next_id ss)) 32 /\
    abi_allocated_window (abi_native_dynamic_array_start_state cs width (n2w loop_count) ss) (cs.cs_next_id + 2)
      (w2n (abi_native_dynamic_array_tail_addr cs ss)) 32 /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand len_op ss = SOME (n2w loop_count) /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var len_op ==>
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_dynamic_array_tail_addr cs ss) loop_count 0 (abi_native_dynamic_array_start_state cs width (n2w loop_count) ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_start_values >> strip_tac >>
  qspecl_then [`cs`, `width`, `n2w loop_count`, `ss`] strip_assume_tac abi_native_dynamic_array_start_control >>
  qspecl_then [`cs`, `width`, `n2w loop_count`, `ss`] ASSUME_TAC abi_native_dynamic_array_start_old_operand >>
  asm_simp_tac (srw_ss()) [abi_dynamic_loop_ready_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array setup values and header readiness: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayStartValues")
