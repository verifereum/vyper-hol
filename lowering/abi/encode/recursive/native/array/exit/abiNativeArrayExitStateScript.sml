(* TOP-LEVEL: the actual parent-cell epilogue returns the accumulated size
   and writes only its owned parent word. Its compiler cut retains fresh
   instruction history and its runtime cut preserves old operands. *)
Theory abiNativeArrayExitState
Ancestors
  abiDynArrayCode abiDynArrayEnds abiDynArrayBoundaryFrames abiAllocatorLoopState abiAllocatorState
  abiStateLoopFrame abiStateFrame abiMemoryFrame abiFieldOperands abiStaticLoopCode
  compileAllocaProvenance compileIdFlow compileEnv fragExec instIdxIndep venomMemDefs venomState venomInst list words arithmetic

Definition abi_native_array_exit_boundary_def:
  abi_native_array_exit_boundary cs parent_addr encoded_word ss =
    (abi_dynarray_exit_state cs.cs_next_var parent_addr encoded_word ss)
      with vs_inst_idx := LENGTH cs.cs_current_insts + 4
End

Theorem abi_native_array_exit_history:
  !cs parent_ptr encoded_size.
    compiler_id_history cs ==> compiler_id_history (abi_dynarray_exit_cut parent_ptr encoded_size cs)
Proof
  rpt gen_tac >> simp[compiler_id_history_def, abi_dynarray_exit_cut_def,
    abi_dynarray_exit_insts_def, mk_inst_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem abi_native_array_exit_old_operand:
  !cs parent_addr encoded_word ss arg_op.
    abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_native_array_exit_boundary cs parent_addr encoded_word ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac (srw_ss()) [abi_native_array_exit_boundary_def, eval_op_inst_idx] >>
  irule abi_dynarray_exit_operand_frame >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [compiler_var_name_def]) >>
  simp_tac (srw_ss()) [compiler_var_name_def] >> DISCH_TAC >>
  rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Theorem abi_native_array_exit_context:
  !cs parent_ptr encoded_size parent_addr encoded_word ss.
    ss.vs_current_bb = cs.cs_current_bb ==>
    (abi_native_array_exit_boundary cs parent_addr encoded_word ss).vs_current_bb =
      (abi_dynarray_exit_cut parent_ptr encoded_size cs).cs_current_bb /\
    (abi_native_array_exit_boundary cs parent_addr encoded_word ss).vs_inst_idx =
      LENGTH (abi_dynarray_exit_cut parent_ptr encoded_size cs).cs_current_insts /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 2)) (abi_native_array_exit_boundary cs parent_addr encoded_word ss) =
      SOME (mload (w2n parent_addr) ss + encoded_word) /\
    abi_allocator_state (abi_native_array_exit_boundary cs parent_addr encoded_word ss) = abi_allocator_state ss /\
    abi_state_frame ss (abi_native_array_exit_boundary cs parent_addr encoded_word ss) /\
    abi_memory_frame [(w2n parent_addr,32)] ss (abi_native_array_exit_boundary cs parent_addr encoded_word ss)
Proof
  rpt gen_tac >> DISCH_TAC >>
  qspecl_then [`cs.cs_next_var`, `parent_addr`, `encoded_word`, `ss`]
    strip_assume_tac abi_dynarray_exit_memory_frame >>
  asm_simp_tac (srw_ss()) [abi_native_array_exit_boundary_def, abi_dynarray_exit_cut_def,
    abi_dynarray_exit_insts_def, abi_state_frame_def, abi_memory_frame_inst_idx, abi_dynarray_exit_value, eval_op_inst_idx]
QED

Theorem abi_native_array_exit_path:
  !ctx func parent_ptr encoded_size cs ss parent_addr encoded_word.
    fn_has_code cs (abi_dynarray_exit_cut parent_ptr encoded_size cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand parent_ptr ss = SOME parent_addr /\ eval_operand encoded_size ss = SOME encoded_word /\
    abi_operand_before cs.cs_next_var parent_ptr /\ abi_operand_before cs.cs_next_var encoded_size ==>
    fragment_path ctx func ss (abi_native_array_exit_boundary cs parent_addr encoded_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ctx`, `func`, `parent_ptr`, `encoded_size`, `cs`, `ss`, `parent_addr`, `encoded_word`]
    mp_tac abi_dynarray_exit_path >>
  impl_tac >- (asm_simp_tac bool_ss [] >> fs[abi_operand_before_def, compiler_var_name_def] >>
    rpt conj_tac >> first_assum irule >> decide_tac) >>
  simp[abi_native_array_exit_boundary_def, abi_dynarray_exit_cut_def, abi_dynarray_exit_insts_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native array epilogue state: " ^ name)
  end) (DB.thms "abiNativeArrayExitState")
