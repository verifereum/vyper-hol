(* TOP-LEVEL: loop setup writes only its two counter cells. Their disjointness
   gives index zero and the initial head size; operand frames allow replay. *)
Theory abiDynamicLoopEntryFrames
Ancestors
  abiDynamicLoopEntry abiStaticLoopEntry abiStaticLoopCode abiComplexMemory abiMemoryFrame memoryReadProps
  ssaOperandFrame compileEnv emitHelperProps venomState list words arithmetic

Theorem abi_static_loop_entry_memory_frame:
  !id var_base ss.
    abi_memory_frame [(w2n (abi_static_loop_counter_addr id ss),32)] ss (abi_static_loop_entry_state id var_base ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`w2n (abi_static_loop_counter_addr id ss)`, `0w:bytes32`,
    `update_var (compiler_var_name var_base 0) (abi_static_loop_counter_addr id ss)
      (abi_static_loop_alloc_frame id ss)`] abi_memory_frame_mstore) >>
  simp[abi_static_loop_entry_state_def, abi_memory_frame_def, read_memory_def,
    update_var_def, abi_static_loop_alloc_frame_memory]
QED

Theorem abi_dynamic_loop_entry_tail_memory_frame:
  !id var_base abi_sz len_word ss.
    abi_memory_frame [(w2n (abi_static_loop_counter_addr (id + 2) ss),32)] ss
      (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`w2n (abi_static_loop_counter_addr (id + 2) ss)`, `len_word * n2w abi_sz:bytes32`,
    `update_var (compiler_var_name var_base 2) (len_word * n2w abi_sz)
      (update_var (compiler_var_name var_base 1) (abi_static_loop_counter_addr (id + 2) ss)
        (abi_static_loop_alloc_frame (id + 2) ss))`] abi_memory_frame_mstore) >>
  simp[abi_dynamic_loop_entry_tail_state_def, LET_THM, abi_memory_frame_def, read_memory_def,
    update_var_def, abi_static_loop_alloc_frame_memory]
QED

Theorem abi_dynamic_loop_entry_memory_frame:
  !id var_base abi_sz len_word ss.
    abi_memory_frame
      [(w2n (abi_static_loop_counter_addr id ss),32);
       (w2n (abi_static_loop_counter_addr (id + 2) (abi_static_loop_entry_state id var_base ss)),32)] ss
      (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`[(w2n (abi_static_loop_counter_addr id ss),32)]`,
    `[(w2n (abi_static_loop_counter_addr (id + 2) (abi_static_loop_entry_state id var_base ss)),32)]`,
    `ss`, `abi_static_loop_entry_state id var_base ss`, `abi_dynamic_loop_entry_state id var_base abi_sz len_word ss`]
    abi_memory_frame_trans) >>
  impl_tac >- simp[abi_dynamic_loop_entry_state_def,
    abi_static_loop_entry_memory_frame, abi_dynamic_loop_entry_tail_memory_frame] >> simp[]
QED

Theorem abi_dynamic_loop_entry_tail_operand_frame:
  !id var_base abi_sz len_word ss arg_op.
    arg_op <> Var (compiler_var_name var_base 1) /\ arg_op <> Var (compiler_var_name var_base 2) ==>
    eval_operand arg_op (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss) = eval_operand arg_op ss
Proof
  simp[abi_dynamic_loop_entry_tail_state_def, LET_THM, eval_operand_mstore_eq,
    eval_operand_update_var_avoids, abi_static_loop_alloc_frame_operand]
QED

Theorem abi_dynamic_loop_entry_operand_frame:
  !id var_base abi_sz len_word ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) /\ arg_op <> Var (compiler_var_name var_base 1) /\
    arg_op <> Var (compiler_var_name var_base 2) ==>
    eval_operand arg_op (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss) = eval_operand arg_op ss
Proof
  simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_operand_frame, abi_static_loop_entry_operand_frame]
QED

Theorem abi_dynamic_loop_entry_tail_values:
  !id var_base abi_sz len_word ss.
    eval_operand (Var (compiler_var_name var_base 1))
      (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss) = SOME (abi_static_loop_counter_addr (id + 2) ss) /\
    eval_operand (Var (compiler_var_name var_base 2))
      (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss) = SOME (len_word * n2w abi_sz) /\
    mload (w2n (abi_static_loop_counter_addr (id + 2) ss))
      (abi_dynamic_loop_entry_tail_state id var_base abi_sz len_word ss) = len_word * n2w abi_sz
Proof
  simp[abi_dynamic_loop_entry_tail_state_def, LET_THM, eval_operand_mstore_eq,
    eval_operand_update_var, eval_operand_update_var_avoids, venomMemPropsTheory.mload_mstore_same]
QED

Theorem abi_dynamic_loop_entry_values:
  !id var_base abi_sz len_word ss.
    regions_disjoint (w2n (abi_static_loop_counter_addr id ss)) 32
      (w2n (abi_static_loop_counter_addr (id + 2) (abi_static_loop_entry_state id var_base ss))) 32 ==>
    eval_operand (Var (compiler_var_name var_base 0)) (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss) =
      SOME (abi_static_loop_counter_addr id ss) /\
    eval_operand (Var (compiler_var_name var_base 1)) (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss) =
      SOME (abi_static_loop_counter_addr (id + 2) (abi_static_loop_entry_state id var_base ss)) /\
    mload (w2n (abi_static_loop_counter_addr id ss)) (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss) = 0w /\
    mload (w2n (abi_static_loop_counter_addr (id + 2) (abi_static_loop_entry_state id var_base ss)))
      (abi_dynamic_loop_entry_state id var_base abi_sz len_word ss) = len_word * n2w abi_sz
Proof
  rpt gen_tac >> DISCH_TAC >> rpt conj_tac
  >- simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_operand_frame, abi_static_loop_entry_counter]
  >- simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_values]
  >- (mp_tac (Q.SPECL
        [`[(w2n (abi_static_loop_counter_addr (id + 2) (abi_static_loop_entry_state id var_base ss)),32)]`,
         `abi_static_loop_entry_state id var_base ss`, `abi_dynamic_loop_entry_state id var_base abi_sz len_word ss`,
         `w2n (abi_static_loop_counter_addr id ss)`] abi_memory_frame_mload) >>
      impl_tac >- simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_memory_frame,
        abi_window_separated_def] >> simp[abi_static_loop_entry_counter]) >>
  simp[abi_dynamic_loop_entry_state_def, abi_dynamic_loop_entry_tail_values]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop setup resource frames: " ^ name)
  end) (DB.thms "abiDynamicLoopEntryFrames")
