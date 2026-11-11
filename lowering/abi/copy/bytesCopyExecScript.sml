(* TOP-LEVEL: actual execution, memory image, and operand/control frames of
   the bytes/string copy. The generated SSA names may already be present. *)
Theory bytesCopyExec
Ancestors
  typedCopyStateFrame bytesCopyCode bytesSnapshotExec abiBytestringCode abiBytestringExec
  ssaOperandFrame exprLoweringProps emitHelperProps compileEnv
  venomState venomExecSemantics venomInst list words arithmetic

Definition bytes_copy_result_def:
  bytes_copy_result var_base (dst_addr:bytes32) (src_addr:bytes32) ss =
    let names = compiler_var_names var_base 5 in
    let length_word = mload (w2n src_addr) ss in
    let rounded = bytestring_round_word length_word in
    let copy_word = rounded + 32w in
    mcopy (w2n dst_addr) (w2n src_addr) (w2n copy_word)
      (update_var (EL 4 names) copy_word
        (update_var (EL 3 names) rounded
          (update_var (EL 2 names) (length_word + 31w)
            (update_var (EL 1 names) (word_1comp 31w)
              (update_var (EL 0 names) length_word ss)))))
End

Theorem bytes_copy_result_state_frame[simp]:
  !var_base dst_addr src_addr before after.
    copy_state_frame before (bytes_copy_result var_base dst_addr src_addr after) <=>
    copy_state_frame before after
Proof
  simp[bytes_copy_result_def, LET_THM]
QED

val bytes_copy_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``NOT``, ``ADD``, ``AND``, ``MCOPY``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem bytes_copy_execution:
  !id var_base dst src ss dst_addr src_addr.
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names var_base 5) ==>
    run_inst_seq (bytes_copy_insts id (compiler_var_names var_base 5) dst src) ss =
      OK (bytes_copy_result var_base dst_addr src_addr ss)
Proof
  rpt gen_tac >> strip_tac >> fs[compiler_var_names_five] >>
  asm_simp_tac (srw_ss()) (bytes_copy_steps @
    [bytes_copy_insts_def, bytes_copy_result_def, run_inst_seq_def,
     compiler_var_names_EL, mk_inst_def, exec_read1_def, exec_pure1_def, exec_pure2_def,
     eval_operand_update_var_avoids, eval_operand_update_var, eval_operand_lit,
     mload_update_var, bytestring_ceil32_round, bytestring_ceil32_round_lit, LET_THM])
QED

Theorem bytes_copy_result_operand_frame:
  !var_base dst_addr src_addr ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 5) ==>
    eval_operand arg_op (bytes_copy_result var_base dst_addr src_addr ss) = eval_operand arg_op ss
Proof
  rpt strip_tac >> fs[compiler_var_names_five] >>
  simp[bytes_copy_result_def, LET_THM, compiler_var_names_EL,
    eval_operand_mcopy_eq, eval_operand_update_var_avoids]
QED

Theorem bytes_copy_result_memory:
  !var_base dst_addr src_addr ss.
    (bytes_copy_result var_base dst_addr src_addr ss).vs_memory =
      (mcopy (w2n dst_addr) (w2n src_addr)
        (w2n (bytestring_round_word (mload (w2n src_addr) ss) + 32w)) ss).vs_memory
Proof
  simp[bytes_copy_result_def, LET_THM, mcopy_def, read_memory_def,
    write_memory_with_expansion_def, update_var_def]
QED

Theorem bytes_copy_result_control[simp]:
  !var_base dst_addr src_addr ss.
    (bytes_copy_result var_base dst_addr src_addr ss).vs_current_bb = ss.vs_current_bb /\
    (bytes_copy_result var_base dst_addr src_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (bytes_copy_result var_base dst_addr src_addr ss).vs_halted = ss.vs_halted /\
    (bytes_copy_result var_base dst_addr src_addr ss).vs_allocas = ss.vs_allocas /\
    (bytes_copy_result var_base dst_addr src_addr ss).vs_alloca_next = ss.vs_alloca_next
Proof
  rpt gen_tac >> simp_tac std_ss [bytes_copy_result_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `mcopy dst_off src_off copy_len (update_var n4 v4 (update_var n3 v3
       (update_var n2 v2 (update_var n1 v1 (update_var n0 v0 _)))))` >>
  simp[mcopy_def, write_memory_with_expansion_def, update_var_def]
QED
