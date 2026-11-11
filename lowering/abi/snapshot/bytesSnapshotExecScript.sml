(* TOP-LEVEL: bytes/string materialization executes allocation plus a copy
   of the rounded live range. The allocation and SSA outputs may be reused.
   Helpers expose its exact memory image and operand/control frames. *)
Theory bytesSnapshotExec
Ancestors
  bytesSnapshotCode memoryValueSnapshot abiBytestringCode abiBytestringExec
  ssaOperandFrame exprLoweringProps emitHelperProps compileEnv instIdxIndep
  venomState venomExecSemantics venomInst list words arithmetic
Libs intReduce wordsLib

val () = computeLib.upd_compset intReduce.add_int_compset

Definition bytes_snapshot_result_def:
  bytes_snapshot_result id var_base capacity (src_addr:bytes32) ss =
    let names = compiler_var_names var_base 6 in
    let length_word = mload (w2n src_addr) ss in
    let rounded = bytestring_round_word length_word in
    let copy_word = rounded + 32w in
    mcopy (w2n (memory_snapshot_addr id ss)) (w2n src_addr) (w2n copy_word)
      (update_var (EL 5 names) copy_word
        (update_var (EL 4 names) rounded
          (update_var (EL 3 names) (length_word + 31w)
            (update_var (EL 2 names) (word_1comp 31w)
              (update_var (EL 1 names) length_word
                (memory_snapshot_allocated id var_base capacity ss))))))
End

Theorem memory_snapshot_allocated_mload[simp]:
  !offset id var_base capacity ss.
    mload offset (memory_snapshot_allocated id var_base capacity ss) = mload offset ss
Proof
  simp[mload_def]
QED

val byte_snapshot_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``NOT``, ``ADD``, ``AND``, ``MCOPY``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem bytes_snapshot_execution:
  !id var_base capacity src ss src_addr.
    capacity < dimword(:256) /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name) (compiler_var_names var_base 6) ==>
    run_inst_seq (bytes_snapshot_insts id (compiler_var_names var_base 6) capacity src) ss =
      OK (bytes_snapshot_result id var_base capacity src_addr ss)
Proof
  rpt gen_tac >> strip_tac >> fs[compiler_var_names_six] >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w capacity)]
    [EL 0 (compiler_var_names var_base 6)]) ss =
      OK (memory_snapshot_allocated id var_base capacity ss)` by
    simp[compiler_var_names_EL, memory_snapshot_allocation_step] >>
  fs[compiler_var_names_EL, mk_inst_def] >>
  asm_simp_tac (srw_ss()) (byte_snapshot_steps @
    [bytes_snapshot_insts_def, bytes_snapshot_result_def, run_inst_seq_def,
     compiler_var_names_EL, mk_inst_def, exec_read1_def, exec_pure1_def, exec_pure2_def,
     memory_snapshot_allocated_operand, memory_snapshot_allocated_result,
     eval_operand_update_var_avoids, eval_operand_update_var, eval_operand_lit,
     mload_update_var, bytestring_ceil32_round, bytestring_ceil32_round_lit, LET_THM])
QED

Theorem bytes_snapshot_result_operand:
  !id var_base capacity src_addr ss.
    eval_operand (Var (EL 0 (compiler_var_names var_base 6)))
      (bytes_snapshot_result id var_base capacity src_addr ss) = SOME (memory_snapshot_addr id ss)
Proof
  simp[bytes_snapshot_result_def, LET_THM, compiler_var_names_EL,
    eval_operand_mcopy_eq, eval_operand_update_var, eval_operand_update_var_avoids,
    memory_snapshot_allocated_result]
QED

Theorem bytes_snapshot_result_operand_frame:
  !id var_base capacity src_addr ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 6) ==>
    eval_operand arg_op (bytes_snapshot_result id var_base capacity src_addr ss) =
      eval_operand arg_op ss
Proof
  rpt strip_tac >> fs[compiler_var_names_six] >>
  simp[bytes_snapshot_result_def, LET_THM, compiler_var_names_EL,
    eval_operand_mcopy_eq, eval_operand_update_var_avoids, memory_snapshot_allocated_operand]
QED

Theorem bytes_snapshot_result_memory:
  !id var_base capacity src_addr ss.
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_memory =
      (mcopy (w2n (memory_snapshot_addr id ss)) (w2n src_addr)
        (w2n (bytestring_round_word (mload (w2n src_addr) ss) + 32w)) ss).vs_memory
Proof
  simp[bytes_snapshot_result_def, LET_THM, mcopy_def, read_memory_def,
    write_memory_with_expansion_def, update_var_def]
QED

Theorem memory_snapshot_allocated_control[simp]:
  !id var_base capacity ss.
    (memory_snapshot_allocated id var_base capacity ss).vs_current_bb = ss.vs_current_bb /\
    (memory_snapshot_allocated id var_base capacity ss).vs_inst_idx = ss.vs_inst_idx /\
    (memory_snapshot_allocated id var_base capacity ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> Cases_on `FLOOKUP ss.vs_allocas id` >>
  simp[memory_snapshot_allocated_def, memory_snapshot_alloc_frame_def, update_var_def]
QED

Theorem bytes_snapshot_result_control[simp]:
  !id var_base capacity src_addr ss.
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (bytes_snapshot_result id var_base capacity src_addr ss).vs_halted = ss.vs_halted
Proof
  rpt gen_tac >> simp_tac std_ss [bytes_snapshot_result_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `mcopy dst_off src_off copy_len (update_var n5 v5 (update_var n4 v4
       (update_var n3 v3 (update_var n2 v2 (update_var n1 v1 _)))))` >>
  simp[mcopy_def, write_memory_with_expansion_def, update_var_def]
QED
