(* TOP-LEVEL: actual dynamic-array setup and epilogue execute at their compiler
   cuts. The parent allocation may be fresh or reused on a later loop visit.
   Helpers record operand, control and total-memory-read frames. *)
Theory abiDynArrayEnds
Ancestors
  abiDynArrayCode abiStaticLoopCode abiStaticLoopEntry abiEncoderPathProps
  memoryReadProps ssaOperandFrame fragBlockPath fragExec compileEnv exprLoweringProps
  emitHelperProps instIdxIndep venomExecSemantics venomState venomInst venomMemProps
  list rich_list words arithmetic

Definition abi_dynarray_entry_state_def:
  abi_dynarray_entry_state id var_base (dst_addr:bytes32) (src_addr:bytes32) ss =
    let allocated = abi_static_loop_entry_state id var_base ss in
    let length_word = mload (w2n src_addr) allocated in
    mstore (w2n dst_addr) length_word
      (update_var (compiler_var_name var_base 1) length_word allocated)
End

Definition abi_dynarray_exit_state_def:
  abi_dynarray_exit_state var_base (parent_addr:bytes32) (encoded_word:bytes32) ss =
    let parent_word = mload (w2n parent_addr) ss in
    let size_word = parent_word + encoded_word in
    update_var (compiler_var_name var_base 2) size_word
      (mstore (w2n parent_addr) size_word
        (update_var (compiler_var_name var_base 1) size_word
          (update_var (compiler_var_name var_base 0) parent_word ss)))
End

val end_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``MSTORE``, ``ADD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem read_memory_update_var[local]:
  !offset read_len name value ss.
    read_memory offset read_len (update_var name value ss) = read_memory offset read_len ss
Proof
  simp[read_memory_def, update_var_def]
QED

Theorem abi_dynarray_entry_execution:
  !id var_base dst src ss dst_addr src_addr.
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name var_base 0) /\
    dst <> Var (compiler_var_name var_base 0) /\ dst <> Var (compiler_var_name var_base 1) ==>
    run_inst_seq (abi_dynarray_entry_insts id var_base dst src) ss =
      OK (abi_dynarray_entry_state id var_base dst_addr src_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_dynarray_entry_insts id var_base dst src =
    TAKE 2 (abi_static_loop_entry id var_base 0) ++
    [mk_inst (id + 2) MLOAD [src] [compiler_var_name var_base 1];
     mk_inst (id + 3) MSTORE [dst; Var (compiler_var_name var_base 1)] []]` by
    simp[abi_dynarray_entry_insts_def, abi_static_loop_entry_def] >>
  pop_assum SUBST1_TAC >>
  mp_tac (Q.SPECL [`TAKE 2 (abi_static_loop_entry id var_base 0)`,
    `[mk_inst (id + 2) MLOAD [src] [compiler_var_name var_base 1];
      mk_inst (id + 3) MSTORE [dst; Var (compiler_var_name var_base 1)] []]`,
    `ss`, `abi_static_loop_entry_state id var_base ss`] run_inst_seq_append) >>
  simp[abi_static_loop_entry_execution] >> DISCH_THEN SUBST1_TAC >>
  asm_simp_tac (srw_ss()) (end_steps @
    [abi_dynarray_entry_state_def, run_inst_seq_def, mk_inst_def, exec_read1_def,
     exec_write2_def, eval_operand_update_var, eval_operand_update_var_avoids,
     abi_static_loop_entry_operand_frame, LET_THM])
QED

Theorem abi_dynarray_entry_operand_frame:
  !id var_base dst_addr src_addr ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) /\
    arg_op <> Var (compiler_var_name var_base 1) ==>
    eval_operand arg_op (abi_dynarray_entry_state id var_base dst_addr src_addr ss) =
      eval_operand arg_op ss
Proof
  simp[abi_dynarray_entry_state_def, LET_THM, eval_operand_mstore_eq,
    eval_operand_update_var_avoids, abi_static_loop_entry_operand_frame]
QED

Theorem abi_dynarray_entry_length:
  !id var_base dst_addr src_addr ss.
    eval_operand (Var (compiler_var_name var_base 1))
      (abi_dynarray_entry_state id var_base dst_addr src_addr ss) =
        SOME (mload (w2n src_addr) (abi_static_loop_entry_state id var_base ss)) /\
    mload (w2n dst_addr) (abi_dynarray_entry_state id var_base dst_addr src_addr ss) =
      mload (w2n src_addr) (abi_static_loop_entry_state id var_base ss)
Proof
  simp[abi_dynarray_entry_state_def, LET_THM, eval_operand_mstore_eq,
    eval_operand_update_var, mload_mstore_same]
QED

Theorem abi_dynarray_entry_control[simp]:
  !id var_base dst_addr src_addr ss.
    (abi_dynarray_entry_state id var_base dst_addr src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynarray_entry_state id var_base dst_addr src_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (abi_dynarray_entry_state id var_base dst_addr src_addr ss).vs_halted = ss.vs_halted
Proof
  simp[abi_dynarray_entry_state_def, LET_THM, update_var_def, mstore_def,
    write_memory_with_expansion_def]
QED

Theorem abi_static_loop_entry_read_frame:
  !id var_base ss offset read_len.
    offset + read_len <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= offset ==>
    read_memory offset read_len (abi_static_loop_entry_state id var_base ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory offset read_len (abi_static_loop_alloc_frame id ss) =
    read_memory offset read_len ss` by
    (simp[abi_static_loop_alloc_frame_def, read_memory_def] >> rw[]) >>
  PURE_REWRITE_TAC [abi_static_loop_entry_state_def] >>
  irule EQ_TRANS >> qexists_tac `read_memory offset read_len
    (update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
      (abi_static_loop_alloc_frame id ss))` >>
  conj_tac >- (irule read_memory_mstore_disjoint >> fs[]) >>
  simp[read_memory_update_var]
QED

Theorem abi_dynarray_entry_read_frame:
  !id var_base dst_addr src_addr ss offset read_len.
    (offset + read_len <= w2n (abi_static_loop_counter_addr id ss) \/
      w2n (abi_static_loop_counter_addr id ss) + 32 <= offset) /\
    (offset + read_len <= w2n dst_addr \/ w2n dst_addr + 32 <= offset) ==>
    read_memory offset read_len (abi_dynarray_entry_state id var_base dst_addr src_addr ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  `read_memory offset read_len (abi_static_loop_entry_state id var_base ss) =
    read_memory offset read_len ss` by
    (irule abi_static_loop_entry_read_frame >> fs[]) >>
  PURE_REWRITE_TAC [abi_dynarray_entry_state_def, LET_THM] >> BETA_TAC >>
  irule EQ_TRANS >> qexists_tac `read_memory offset read_len
    (update_var (compiler_var_name var_base 1)
      (mload (w2n src_addr) (abi_static_loop_entry_state id var_base ss))
      (abi_static_loop_entry_state id var_base ss))` >>
  conj_tac >- (irule read_memory_mstore_disjoint >> simp[]) >>
  simp[read_memory_update_var]
QED

Theorem abi_dynarray_entry_path:
  !ctx func dst src cs ss dst_addr src_addr.
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    src <> Var (compiler_var_name cs.cs_next_var 0) /\
    dst <> Var (compiler_var_name cs.cs_next_var 0) /\
    dst <> Var (compiler_var_name cs.cs_next_var 1) ==>
    fragment_path ctx func ss
      ((abi_dynarray_entry_state cs.cs_next_id cs.cs_next_var dst_addr src_addr ss)
        with vs_inst_idx := LENGTH (abi_dynarray_entry_cut dst src cs).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `abi_dynarray_entry_cut dst src cs`, `ss`,
     `abi_dynarray_entry_state cs.cs_next_id cs.cs_next_var dst_addr src_addr ss`]
     fragment_path_emitted) >>
   simp[abi_dynarray_entry_cut_def, emitted_insts_def, same_blocks_def,
     DROP_LENGTH_APPEND, abi_dynarray_insts_straight, abi_dynarray_entry_execution]
QED

Theorem abi_dynarray_exit_execution:
  !id var_base parent_ptr encoded_size ss parent_addr encoded_word.
    eval_operand parent_ptr ss = SOME parent_addr /\
    eval_operand encoded_size ss = SOME encoded_word /\
    parent_ptr <> Var (compiler_var_name var_base 0) /\
    parent_ptr <> Var (compiler_var_name var_base 1) /\
    encoded_size <> Var (compiler_var_name var_base 0) ==>
    run_inst_seq (abi_dynarray_exit_insts id var_base parent_ptr encoded_size) ss =
      OK (abi_dynarray_exit_state var_base parent_addr encoded_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) (end_steps @
    [abi_dynarray_exit_insts_def, abi_dynarray_exit_state_def, run_inst_seq_def,
     mk_inst_def, exec_read1_def, exec_write2_def, exec_pure2_def,
     eval_operand_update_var, eval_operand_update_var_avoids,
     eval_operand_mstore_eq, mload_update_var, mload_mstore_same, LET_THM])
QED

Theorem abi_dynarray_exit_value:
  !var_base parent_addr encoded_word ss.
    eval_operand (Var (compiler_var_name var_base 2))
      (abi_dynarray_exit_state var_base parent_addr encoded_word ss) =
        SOME (mload (w2n parent_addr) ss + encoded_word)
Proof
  simp[abi_dynarray_exit_state_def, LET_THM, eval_operand_update_var]
QED

Theorem abi_dynarray_exit_operand_frame:
  !var_base parent_addr encoded_word ss arg_op.
    EVERY (\name. arg_op <> Var name)
      [compiler_var_name var_base 0; compiler_var_name var_base 1; compiler_var_name var_base 2] ==>
    eval_operand arg_op (abi_dynarray_exit_state var_base parent_addr encoded_word ss) =
      eval_operand arg_op ss
Proof
  simp[abi_dynarray_exit_state_def, LET_THM, eval_operand_mstore_eq,
    eval_operand_update_var_avoids]
QED

Theorem abi_dynarray_exit_read_frame:
  !var_base parent_addr encoded_word ss offset read_len.
    offset + read_len <= w2n parent_addr \/ w2n parent_addr + 32 <= offset ==>
    read_memory offset read_len (abi_dynarray_exit_state var_base parent_addr encoded_word ss) =
      read_memory offset read_len ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[abi_dynarray_exit_state_def, LET_THM, mstore_update_var, read_memory_update_var] >>
  irule read_memory_mstore_disjoint >> simp[]
QED

Theorem abi_dynarray_exit_control[simp]:
  !var_base parent_addr encoded_word ss.
    (abi_dynarray_exit_state var_base parent_addr encoded_word ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynarray_exit_state var_base parent_addr encoded_word ss).vs_inst_idx = ss.vs_inst_idx /\
    (abi_dynarray_exit_state var_base parent_addr encoded_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_dynarray_exit_state_def, LET_THM, update_var_def, mstore_def,
    write_memory_with_expansion_def]
QED

Theorem abi_dynarray_exit_path:
  !ctx func parent_ptr encoded_size cs ss parent_addr encoded_word.
    fn_has_code cs (abi_dynarray_exit_cut parent_ptr encoded_size cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand parent_ptr ss = SOME parent_addr /\ eval_operand encoded_size ss = SOME encoded_word /\
    parent_ptr <> Var (compiler_var_name cs.cs_next_var 0) /\
    parent_ptr <> Var (compiler_var_name cs.cs_next_var 1) /\
    encoded_size <> Var (compiler_var_name cs.cs_next_var 0) ==>
    fragment_path ctx func ss
      ((abi_dynarray_exit_state cs.cs_next_var parent_addr encoded_word ss)
        with vs_inst_idx := LENGTH (abi_dynarray_exit_cut parent_ptr encoded_size cs).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `abi_dynarray_exit_cut parent_ptr encoded_size cs`, `ss`,
    `abi_dynarray_exit_state cs.cs_next_var parent_addr encoded_word ss`] fragment_path_emitted) >>
  simp[abi_dynarray_exit_cut_def, emitted_insts_def, same_blocks_def,
    DROP_LENGTH_APPEND, abi_dynarray_insts_straight, abi_dynarray_exit_execution]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI dynamic-array boundary theorem: " ^ name)
  end) (DB.thms "abiDynArrayEnds")
