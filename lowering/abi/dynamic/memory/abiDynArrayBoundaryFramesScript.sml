(* TOP-LEVEL: the array wrapper's setup writes its parent cell and output
   length word. Its epilogue writes the parent cell only. *)
Theory abiDynArrayBoundaryFrames
Ancestors
  abiDynArrayCode abiDynArrayEnds abiDynamicLoopEntryFrames abiStaticLoopEntry abiStaticLoopCode abiStaticLoopBody
  abiMemoryFrame memoryReadProps memoryValueAbiExec abiEncoderPathProps ssaOperandFrame instIdxIndep
  compileEnv venomState venomExecSemantics list pair words arithmetic

Definition abi_dynarray_entry_boundary_def:
  abi_dynarray_entry_boundary cs dst_addr src_addr ss =
    (abi_dynarray_entry_state cs.cs_next_id cs.cs_next_var dst_addr src_addr ss)
      with vs_inst_idx := LENGTH cs.cs_current_insts + 4
End

Theorem abi_dynarray_entry_tail_memory_frame:
  !id var_base dst_addr src_addr ss.
    abi_memory_frame [(w2n dst_addr,32)] (abi_static_loop_entry_state id var_base ss)
      (abi_dynarray_entry_state id var_base dst_addr src_addr ss)
Proof
  simp[abi_dynarray_entry_state_def, LET_THM, mstore_update_var,
    abi_memory_frame_update_var, abi_memory_frame_mstore]
QED

Theorem abi_dynarray_entry_memory_frame:
  !id var_base dst_addr src_addr ss.
    abi_memory_frame [(w2n (abi_static_loop_counter_addr id ss),32);(w2n dst_addr,32)] ss
      (abi_dynarray_entry_state id var_base dst_addr src_addr ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`[(w2n (abi_static_loop_counter_addr id ss),32)]`, `[(w2n (dst_addr:bytes32),32)]`, `ss`,
    `abi_static_loop_entry_state id var_base ss`, `abi_dynarray_entry_state id var_base dst_addr src_addr ss`]
    abi_memory_frame_trans) >>
  impl_tac >- simp[abi_static_loop_entry_memory_frame, abi_dynarray_entry_tail_memory_frame] >> simp[]
QED

Theorem abi_dynarray_exit_memory_frame:
  !var_base parent_addr encoded_word ss.
    abi_memory_frame [(w2n parent_addr,32)] ss (abi_dynarray_exit_state var_base parent_addr encoded_word ss)
Proof
  simp[abi_dynarray_exit_state_def, LET_THM, mstore_update_var,
    abi_memory_frame_update_var, abi_memory_frame_mstore]
QED

Theorem abi_dynarray_entry_values:
  !id var_base dst_addr src_addr parent_addr length_word ss.
    parent_addr = abi_static_loop_counter_addr id ss /\ mload (w2n src_addr) ss = length_word /\
    regions_disjoint (w2n src_addr) 32 (w2n parent_addr) 32 /\
    regions_disjoint (w2n parent_addr) 32 (w2n dst_addr) 32 ==>
    eval_operand (Var (compiler_var_name var_base 0)) (abi_dynarray_entry_state id var_base dst_addr src_addr ss) =
      SOME parent_addr /\
    eval_operand (Var (compiler_var_name var_base 1)) (abi_dynarray_entry_state id var_base dst_addr src_addr ss) =
      SOME length_word /\
    mload (w2n dst_addr) (abi_dynarray_entry_state id var_base dst_addr src_addr ss) = length_word /\
    mload (w2n parent_addr) (abi_dynarray_entry_state id var_base dst_addr src_addr ss) = 0w
Proof
  rpt gen_tac >> strip_tac >>
  `mload (w2n src_addr) (abi_static_loop_entry_state id var_base ss) = length_word` by
    (mp_tac (Q.SPECL [`[(w2n (parent_addr:bytes32),32)]`, `ss`,
       `abi_static_loop_entry_state id var_base ss`, `w2n (src_addr:bytes32)`] abi_memory_frame_mload) >>
     impl_tac >- simp[abi_static_loop_entry_memory_frame, abi_window_separated_def] >> simp[]) >>
  `mload (w2n parent_addr) (abi_dynarray_entry_state id var_base dst_addr src_addr ss) = 0w` by
    (mp_tac (Q.SPECL [`[(w2n (dst_addr:bytes32),32)]`, `abi_static_loop_entry_state id var_base ss`,
       `abi_dynarray_entry_state id var_base dst_addr src_addr ss`, `w2n (parent_addr:bytes32)`] abi_memory_frame_mload) >>
     impl_tac >- simp[abi_dynarray_entry_tail_memory_frame, abi_window_separated_def] >>
     simp[abi_static_loop_entry_counter]) >>
  simp[abi_dynarray_entry_length, abi_dynarray_entry_state_def, LET_THM,
    eval_operand_mstore_eq, eval_operand_update_var_avoids, abi_static_loop_entry_counter]
QED

Theorem abi_dynarray_entry_boundary_frame:
  !cs dst_addr src_addr ss.
    abi_memory_frame [(w2n (abi_static_loop_counter_addr cs.cs_next_id ss),32);(w2n dst_addr,32)] ss
      (abi_dynarray_entry_boundary cs dst_addr src_addr ss) /\
    (abi_dynarray_entry_boundary cs dst_addr src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynarray_entry_boundary cs dst_addr src_addr ss).vs_inst_idx = LENGTH cs.cs_current_insts + 4 /\
    (abi_dynarray_entry_boundary cs dst_addr src_addr ss).vs_halted = ss.vs_halted
Proof
  simp[abi_dynarray_entry_boundary_def, abi_memory_frame_inst_idx, abi_dynarray_entry_memory_frame]
QED

Theorem abi_dynarray_entry_boundary_operand:
  !cs dst_addr src_addr ss arg_op.
    arg_op <> Var (compiler_var_name cs.cs_next_var 0) /\ arg_op <> Var (compiler_var_name cs.cs_next_var 1) ==>
    eval_operand arg_op (abi_dynarray_entry_boundary cs dst_addr src_addr ss) = eval_operand arg_op ss
Proof
  simp[abi_dynarray_entry_boundary_def, eval_op_inst_idx, abi_dynarray_entry_operand_frame]
QED

Theorem abi_dynarray_entry_boundary_values:
  !cs dst_addr src_addr parent_addr length_word ss.
    parent_addr = abi_static_loop_counter_addr cs.cs_next_id ss /\ mload (w2n src_addr) ss = length_word /\
    regions_disjoint (w2n src_addr) 32 (w2n parent_addr) 32 /\
    regions_disjoint (w2n parent_addr) 32 (w2n dst_addr) 32 ==>
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) (abi_dynarray_entry_boundary cs dst_addr src_addr ss) =
      SOME parent_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) (abi_dynarray_entry_boundary cs dst_addr src_addr ss) =
      SOME length_word /\
    mload (w2n dst_addr) (abi_dynarray_entry_boundary cs dst_addr src_addr ss) = length_word /\
    mload (w2n parent_addr) (abi_dynarray_entry_boundary cs dst_addr src_addr ss) = 0w
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `dst_addr`, `src_addr`, `parent_addr`, `length_word`, `ss`]
    abi_dynarray_entry_values) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[abi_dynarray_entry_boundary_def, eval_op_inst_idx, mload_inst_idx]
QED

Theorem abi_dynarray_entry_boundary_path:
  !ctx func dst src cs ss dst_addr src_addr.
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 0) /\
    dst <> Var (compiler_var_name cs.cs_next_var 0) /\ dst <> Var (compiler_var_name cs.cs_next_var 1) ==>
    fragment_path ctx func ss (abi_dynarray_entry_boundary cs dst_addr src_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `cs`, `ss`, `dst_addr`, `src_addr`] abi_dynarray_entry_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[abi_dynarray_entry_boundary_def, abi_dynarray_entry_cut_def, abi_dynarray_entry_insts_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-array wrapper memory frames: " ^ name)
  end) (DB.thms "abiDynArrayBoundaryFrames")
