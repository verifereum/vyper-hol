(* TOP-LEVEL: the exact dynamic-child entry preserves source memory and
   reserves the saved head/tail operands before an arbitrary recursive call.
   Helpers recover those operands from the common native encoder result. *)
Theory abiMemoryChildEntry
Ancestors
  abiMemoryLeafRun abiChildCode abiChildPrefix abiChildFlatCode
  abiFieldOperands abiStateFrameOps abiStateFrame abiAllocatorState abiMemoryFrame
  abiStaticLoopCode instIdxIndep compileEnv venomState list words arithmetic

Definition abi_child_entry_state_def:
  abi_child_entry_state cs head_offset dst_addr dyn_addr ss =
    (abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss)
      with vs_inst_idx := LENGTH cs.cs_current_insts + 3
End

Theorem abi_child_entry_cut:
  !cs dst dyn_ptr head_offset dst_addr dyn_addr ss.
    abi_child_entry_state cs head_offset dst_addr dyn_addr ss =
      (abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss)
        with vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts
Proof
  simp[abi_child_entry_state_def, abi_child_prefix_cut_def, abi_child_prefix_insts_def]
QED

Theorem abi_child_entry_frame:
  !cs head_offset dst_addr dyn_addr ss.
    (abi_child_entry_state cs head_offset dst_addr dyn_addr ss).vs_memory = ss.vs_memory /\
    (abi_child_entry_state cs head_offset dst_addr dyn_addr ss).vs_current_bb = ss.vs_current_bb /\
    (abi_child_entry_state cs head_offset dst_addr dyn_addr ss).vs_halted = ss.vs_halted /\
    abi_memory_frame [] ss (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) /\
    abi_state_frame ss (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) /\
    abi_allocator_state (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) = abi_allocator_state ss
Proof
  simp[abi_child_entry_state_def, abi_child_prefix_frame, abi_memory_frame_def,
    read_memory_def, abi_state_frame_def]
QED

Theorem abi_child_entry_values:
  !cs head_offset dst_addr dyn_addr ss.
    eval_operand (Var (compiler_var_name cs.cs_next_var 0))
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) = SOME (dst_addr + n2w head_offset) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1))
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 2))
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) = SOME (dst_addr + mload (w2n dyn_addr) ss)
Proof
  simp[abi_child_entry_state_def, eval_op_inst_idx, abi_child_prefix_values]
QED

Theorem abi_child_entry_operand:
  !cs head_offset dst_addr dyn_addr ss arg_op.
    abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [abi_child_entry_state_def, eval_op_inst_idx] >>
  irule abi_child_prefix_operand_frame >>
  irule abi_operand_before_names >> qexists_tac `cs.cs_next_var` >> simp[]
QED

Theorem abi_child_entry_reserved:
  !cs.
    abi_operand_before (cs.cs_next_var + 3) (Var (compiler_var_name cs.cs_next_var 0)) /\
    abi_operand_before (cs.cs_next_var + 3) (Var (compiler_var_name cs.cs_next_var 1))
Proof
  gen_tac >> conj_tac >> irule abi_operand_before_generated >> simp[]
QED

Theorem abi_child_entry_result_frame:
  !ctx func cs dst dyn_ptr head_offset mid ret dst_addr dyn_addr payload scratch ss child_out.
    abi_encoding_result ctx func (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid ret
      (dst_addr + mload (w2n dyn_addr) ss) payload scratch
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) child_out ==>
    !arg_op. abi_operand_before (cs.cs_next_var + 3) arg_op ==>
      eval_operand arg_op child_out =
        eval_operand arg_op (abi_child_entry_state cs head_offset dst_addr dyn_addr ss)
Proof
  simp_tac bool_ss [abi_encoding_result_def, abi_child_prefix_cut_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_child_entry_result_values:
  !ctx func cs dst dyn_ptr head_offset mid ret dst_addr dyn_addr payload scratch ss child_out.
    abi_encoding_result ctx func (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid ret
      (dst_addr + mload (w2n dyn_addr) ss) payload scratch
      (abi_child_entry_state cs head_offset dst_addr dyn_addr ss) child_out /\
    abi_operand_before cs.cs_next_var dyn_ptr /\ eval_operand dyn_ptr ss = SOME dyn_addr ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) child_out = SOME (dst_addr + n2w head_offset) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) child_out = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand dyn_ptr child_out = SOME dyn_addr
Proof
  rpt gen_tac >> strip_tac >> drule abi_child_entry_result_frame >> DISCH_TAC >>
  strip_assume_tac (Q.SPEC `cs` abi_child_entry_reserved) >>
  `abi_operand_before (cs.cs_next_var + 3) dyn_ptr` by
    (irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!arg_op. _` (qspec_then `Var (compiler_var_name cs.cs_next_var 0)` mp_tac) >>
      simp[abi_child_entry_values]) >> conj_tac
  >- (qpat_x_assum `!arg_op. _` (qspec_then `Var (compiler_var_name cs.cs_next_var 1)` mp_tac) >>
      simp[abi_child_entry_values]) >>
  qpat_x_assum `!arg_op. _` (qspec_then `dyn_ptr` mp_tac) >> simp[abi_child_entry_operand]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive ABI child entry: " ^ name)
  end) (DB.thms "abiMemoryChildEntry")
