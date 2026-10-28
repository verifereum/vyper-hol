(* TOP-LEVEL: execution and exact memory image of the checked live-element
   array copy. Operand frames allow reused generated SSA outputs. *)
Theory dynCopyExec
Ancestors
  typedCopyStateFrame dynCopyCode abiBytestringCode ssaOperandFrame exprLoweringProps emitHelperProps
  compileEnv venomState venomExecSemantics venomInst list words arithmetic

Definition dyn_copy_result_def:
  dyn_copy_result var_base elem_size (dst_addr:bytes32) (src_addr:bytes32) n ss =
    let names = compiler_var_names var_base 6 in
    mcopy (w2n (dst_addr + 32w)) (w2n (src_addr + 32w)) (w2n (n2w n * n2w elem_size : bytes32))
      (update_var (EL 5 names) (n2w n * n2w elem_size)
        (update_var (EL 4 names) (dst_addr + 32w)
          (update_var (EL 3 names) (src_addr + 32w)
            (mstore (w2n dst_addr) (n2w n)
              (update_var (EL 2 names) 1w
                (update_var (EL 1 names) 0w
                  (update_var (EL 0 names) (n2w n) ss)))))))
End

Theorem dyn_copy_result_state_frame[simp]:
  !var_base elem_size dst_addr src_addr n before after.
    copy_state_frame before (dyn_copy_result var_base elem_size dst_addr src_addr n after) <=>
    copy_state_frame before after
Proof
  simp[dyn_copy_result_def, LET_THM]
QED

val dyn_copy_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
    [``MLOAD``, ``GT``, ``ISZERO``, ``ASSERT``, ``MSTORE``, ``ADD``, ``MUL``, ``MCOPY``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem dyn_copy_execution:
  !id var_base dst src capacity elem_size ss dst_addr src_addr n.
    n <= capacity /\ capacity < dimword(:256) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    mload (w2n src_addr) ss = n2w n /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names var_base 6) ==>
    run_inst_seq (dyn_copy_insts id (compiler_var_names var_base 6) dst src capacity elem_size) ss =
      OK (dyn_copy_result var_base elem_size dst_addr src_addr n ss)
Proof
  rpt gen_tac >> strip_tac >> fs[compiler_var_names_six] >>
  `n < dimword(:256)` by decide_tac >>
  `~(n > capacity)` by decide_tac >>
  asm_simp_tac (srw_ss()) (dyn_copy_steps @
    [dyn_copy_insts_def, dyn_copy_prefix_insts_def, dyn_copy_result_def, run_inst_seq_def,
     compiler_var_names_EL, mk_inst_def, exec_read1_def, exec_pure1_def, exec_pure2_def,
     exec_write2_def,
     eval_operand_update_var_avoids, eval_operand_update_var, eval_operand_lit,
     eval_operand_mstore_eq, mload_update_var, bool_to_word_def, LET_THM])
QED

Theorem dyn_copy_result_operand_frame:
  !var_base elem_size dst_addr src_addr n ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 6) ==>
    eval_operand arg_op (dyn_copy_result var_base elem_size dst_addr src_addr n ss) =
      eval_operand arg_op ss
Proof
  rpt strip_tac >> fs[compiler_var_names_six] >>
  simp[dyn_copy_result_def, LET_THM, compiler_var_names_EL,
    eval_operand_mcopy_eq, eval_operand_mstore_eq, eval_operand_update_var_avoids]
QED

Theorem dyn_copy_result_memory:
  !var_base elem_size dst_addr src_addr n ss.
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_memory =
      (mcopy (w2n (dst_addr + 32w)) (w2n (src_addr + 32w)) (w2n (n2w n * n2w elem_size : bytes32))
        (mstore (w2n dst_addr) (n2w n) ss)).vs_memory
Proof
  simp[dyn_copy_result_def, LET_THM, mstore_update_var, mcopy_update_var,
    update_var_def, mstore_reset_vars, mcopy_reset_vars]
QED

Theorem mstore_control_fields[simp]:
  !offset word ss.
    (mstore offset word ss).vs_current_bb = ss.vs_current_bb /\
    (mstore offset word ss).vs_inst_idx = ss.vs_inst_idx /\
    (mstore offset word ss).vs_halted = ss.vs_halted /\
    (mstore offset word ss).vs_allocas = ss.vs_allocas /\
    (mstore offset word ss).vs_alloca_next = ss.vs_alloca_next
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem mcopy_control_fields[simp]:
  !dst src byte_count ss.
    (mcopy dst src byte_count ss).vs_current_bb = ss.vs_current_bb /\
    (mcopy dst src byte_count ss).vs_inst_idx = ss.vs_inst_idx /\
    (mcopy dst src byte_count ss).vs_halted = ss.vs_halted /\
    (mcopy dst src byte_count ss).vs_allocas = ss.vs_allocas /\
    (mcopy dst src byte_count ss).vs_alloca_next = ss.vs_alloca_next
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem dyn_copy_result_control[simp]:
  !var_base elem_size dst_addr src_addr n ss.
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_current_bb = ss.vs_current_bb /\
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_inst_idx = ss.vs_inst_idx /\
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_halted = ss.vs_halted /\
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_allocas = ss.vs_allocas /\
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_alloca_next = ss.vs_alloca_next
Proof
  simp[dyn_copy_result_def, LET_THM, update_var_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-array copy execution theorem: " ^ name)
  end) (DB.thms "dynCopyExec")
