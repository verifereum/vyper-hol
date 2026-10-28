(* TOP-LEVEL: the actual head/tail stores and latch return to the generated
   header. They retain allocator/external state and earlier SSA operands,
   with an exact three-word memory frame. *)
Theory abiNativeDynamicArrayUpdateState
Ancestors
  abiDynamicLoopUpdate abiDynamicLoopLatch abiChildSuffix abiStaticLoopBody abiStaticLoopCode
  abiAllocatorLoopState abiAllocatorState abiStateLoopFrame abiStateFrame abiMemoryFrame abiFieldOperands
  compileEnv fragExec instIdxIndep venomMemDefs venomState list words arithmetic

Definition abi_native_dynamic_array_next_state_def:
  abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss =
    jump_to (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
      (abi_dynamic_loop_update_state mid (dst_addr + 32w + n2w index * n2w width) dyn_addr counter_addr
        (n2w index) tail_offset child_size ss)
End

Theorem abi_native_dynamic_array_next_frame:
  !cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss.
    abi_allocator_state (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) =
      abi_allocator_state ss /\
    abi_state_frame ss (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) /\
    abi_memory_frame [(w2n (dst_addr + 32w + n2w index * n2w width),32);(w2n dyn_addr,32);(w2n counter_addr,32)] ss
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)
Proof
  rpt gen_tac >>
  `abi_memory_frame [(w2n (dst_addr + 32w + n2w index * n2w width),32);(w2n dyn_addr,32);(w2n counter_addr,32)] ss
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)` by
    (qspecl_then [`mid`, `dst_addr + 32w + n2w index * n2w width`, `dyn_addr`, `counter_addr`, `n2w index`,
       `tail_offset`, `child_size`, `ss`] mp_tac abi_dynamic_loop_update_frame >>
     simp[abi_native_dynamic_array_next_state_def, abi_memory_frame_def, read_memory_def, jump_to_def]) >>
  rpt conj_tac
  >- simp[abi_native_dynamic_array_next_state_def]
  >- simp[abi_native_dynamic_array_next_state_def, abi_state_frame_def] >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_dynamic_array_next_control:
  !cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss.
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss).vs_current_bb =
      fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss).vs_inst_idx = 0 /\
    (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss).vs_halted = ss.vs_halted /\
    mload (w2n counter_addr) (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) =
      n2w (index + 1)
Proof
  rpt gen_tac >> rpt conj_tac
  >- simp[abi_native_dynamic_array_next_state_def, jump_to_def]
  >- simp[abi_native_dynamic_array_next_state_def, jump_to_def]
  >- simp[abi_native_dynamic_array_next_state_def, jump_to_def, abi_dynamic_loop_update_state_def,
      abi_dynamic_loop_latch_control] >>
  PURE_REWRITE_TAC [abi_native_dynamic_array_next_state_def, memory_reads_jump_to,
    abi_dynamic_loop_update_counter, word_add_n2w] >> REFL_TAC
QED

Theorem abi_native_dynamic_array_next_old_operand:
  !cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss arg_op.
    abi_operand_before mid.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `arg_op <> Var (compiler_var_name mid.cs_next_var 0) /\ arg_op <> Var (compiler_var_name (mid.cs_next_var + 1) 0)` by
    (qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >>
     simp_tac bool_ss [compiler_var_name_def] >> DISCH_TAC >> conj_tac >> first_x_assum irule >> decide_tac) >>
  simp[abi_native_dynamic_array_next_state_def, abi_dynamic_loop_update_state_def, eval_operand_jump_to_eq,
    eval_op_inst_idx, abi_dynamic_loop_latch_operand_frame, abi_child_suffix_operand_frame]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array update/latch state: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayUpdateState")
