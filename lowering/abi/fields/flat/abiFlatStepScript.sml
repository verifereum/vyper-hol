(* TOP-LEVEL: every concrete field constructor executes a real traversal
   step. No child callback remains; source and output invariants are advanced. *)
Theory abiFlatStep
Ancestors
  abiAllocatorState
  abiStateFrame
  abiFlatStaticStep abiFlatBytesStep abiFlatFieldsDefs abiFieldOperands abiFieldLayoutDefs
  abiMemoryFrame abiStaticLoopCode compileEnv fragExec fragBlockPath venomState list words arithmetic

Theorem compile_abi_flat_field_step:
  !ctx func dst src dyn_ptr row rest source_offset fields tail_offset capacity
      cs ret cs' ss dst_addr dyn_addr root_addr.
    abi_flat_valid row /\
    compile_abi_encode_complex_elems dst src (MAP abi_flat_entry (row::rest))
      source_offset (abi_field_head_size fields) dyn_ptr cs = (ret,cs') /\ fn_has_code cs cs' func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    abi_operand_before cs.cs_next_var src /\ abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var dyn_ptr /\
    abi_flat_state fields (row::rest) tail_offset dst_addr dyn_addr root_addr source_offset capacity ss ==>
    ?mid out.
      compile_abi_encode_complex_elems dst src (MAP abi_flat_entry rest) (source_offset + abi_flat_mem_size row)
        (abi_field_head_size (fields ++ [abi_flat_output row])) dyn_ptr mid = (ret,cs') /\ fn_has_code mid cs' func /\
      cs.cs_next_var <= mid.cs_next_var /\ fragment_path ctx func ss out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted /\
      eval_operand dst out = SOME dst_addr /\ eval_operand src out = SOME root_addr /\ eval_operand dyn_ptr out = SOME dyn_addr /\
      abi_flat_state (fields ++ [abi_flat_output row]) rest tail_offset dst_addr dyn_addr root_addr
        (source_offset + abi_flat_mem_size row) capacity out /\
      (!arg_op. abi_operand_before cs.cs_next_var arg_op ==> eval_operand arg_op out = eval_operand arg_op ss) /\
      abi_memory_frame [(w2n dst_addr,capacity);(w2n dyn_addr,32)] ss out /\ abi_state_frame ss out /\ abi_allocator_state out = abi_allocator_state ss
Proof
  rpt gen_tac >> Cases_on `row`
  >- (simp_tac bool_ss [abi_flat_output_def, abi_flat_mem_size_def] >>
      MATCH_ACCEPT_TAC compile_abi_flat_static_step) >>
  simp_tac bool_ss [abi_flat_output_def, abi_flat_mem_size_def, abi_flat_valid_def] >>
  MATCH_ACCEPT_TAC compile_abi_flat_bytes_step
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed uniform concrete ABI field traversal step: " ^ name)
  end) (DB.thms "abiFlatStep")
