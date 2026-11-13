(* TOP-LEVEL: the real dynamic-array prefix checks its live length, writes
   the destination header and saves both payload pointers. Generated SSA
   outputs may already be defined when this code is replayed. *)
Theory dynCopyPrefixExec
Ancestors
  dynCopyCode dynCopyExec abiBytestringCode abiStaticLoopCode ssaOperandFrame
  exprLoweringProps emitHelperProps compileEnv venomState venomExecSemantics venomInst
  list words arithmetic

Definition dyn_copy_prefix_result_def:
  dyn_copy_prefix_result var_base (dst_addr:bytes32) (src_addr:bytes32) n ss =
    update_var (compiler_var_name var_base 4) (dst_addr + 32w)
      (update_var (compiler_var_name var_base 3) (src_addr + 32w)
        (mstore (w2n dst_addr) (n2w n)
          (update_var (compiler_var_name var_base 2) 1w
            (update_var (compiler_var_name var_base 1) 0w
              (update_var (compiler_var_name var_base 0) (n2w n) ss)))))
End

Theorem compiler_var_names_five:
  !var_base. compiler_var_names var_base 5 =
    [STRING #"%" (toString var_base); STRING #"%" (toString (var_base + 1));
     STRING #"%" (toString (var_base + 2)); STRING #"%" (toString (var_base + 3));
     STRING #"%" (toString (var_base + 4))]
Proof
  simp[compiler_var_names_def, GENLIST_CONS]
QED

val dyn_prefix_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
    [``MLOAD``, ``GT``, ``ISZERO``, ``ASSERT``, ``MSTORE``, ``ADD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem dyn_copy_prefix_execution:
  !id var_base dst src capacity ss dst_addr src_addr n.
    n <= capacity /\ capacity < dimword(:256) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    mload (w2n src_addr) ss = n2w n /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names var_base 5) ==>
    run_inst_seq (dyn_copy_prefix_insts id (compiler_var_names var_base 5) dst src capacity) ss =
      OK (dyn_copy_prefix_result var_base dst_addr src_addr n ss)
Proof
  rpt gen_tac >> strip_tac >> fs[compiler_var_names_five] >>
  `n < dimword(:256)` by decide_tac >> `~(n > capacity)` by decide_tac >>
  asm_simp_tac (srw_ss()) (dyn_prefix_steps @
    [dyn_copy_prefix_insts_def, dyn_copy_prefix_result_def, run_inst_seq_def,
     compiler_var_names_EL, compiler_var_name_def, mk_inst_def, exec_read1_def,
     exec_pure1_def, exec_pure2_def, exec_write2_def,
     eval_operand_update_var_avoids, eval_operand_update_var, eval_operand_lit,
     eval_operand_mstore_eq, mload_update_var, bool_to_word_def])
QED

Theorem dyn_copy_prefix_straight:
  !id names dst src capacity.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (dyn_copy_prefix_insts id names dst src capacity) /\
    LENGTH (dyn_copy_prefix_insts id names dst src capacity) = 7
Proof
  simp[dyn_copy_prefix_insts_def, mk_inst_def, is_terminator_def]
QED

Theorem dyn_copy_prefix_result_control[simp]:
  !var_base dst_addr src_addr n ss.
    (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_current_bb = ss.vs_current_bb /\
    (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_inst_idx = ss.vs_inst_idx /\
    (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_halted = ss.vs_halted /\
    (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_allocas = ss.vs_allocas /\
    (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_alloca_next = ss.vs_alloca_next
Proof
  simp[dyn_copy_prefix_result_def, update_var_def]
QED

Theorem dyn_copy_prefix_result_values:
  !var_base dst_addr src_addr n ss.
    eval_operand (Var (compiler_var_name var_base 0))
      (dyn_copy_prefix_result var_base dst_addr src_addr n ss) = SOME (n2w n) /\
    eval_operand (Var (compiler_var_name var_base 3))
      (dyn_copy_prefix_result var_base dst_addr src_addr n ss) = SOME (src_addr + 32w) /\
    eval_operand (Var (compiler_var_name var_base 4))
      (dyn_copy_prefix_result var_base dst_addr src_addr n ss) = SOME (dst_addr + 32w)
Proof
  simp[dyn_copy_prefix_result_def, eval_operand_update_var, eval_operand_update_var_avoids,
    eval_operand_mstore_eq]
QED

Theorem dyn_copy_prefix_result_memory:
  !var_base dst_addr src_addr n ss.
    (dyn_copy_prefix_result var_base dst_addr src_addr n ss).vs_memory =
      (mstore (w2n dst_addr) (n2w n) ss).vs_memory
Proof
  simp[dyn_copy_prefix_result_def, mstore_update_var, update_var_def]
QED

Theorem dyn_copy_prefix_result_operand_frame:
  !var_base dst_addr src_addr n ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 5) ==>
    eval_operand arg_op (dyn_copy_prefix_result var_base dst_addr src_addr n ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> fs[compiler_var_names_five, compiler_var_name_def] >>
  simp[dyn_copy_prefix_result_def, compiler_var_name_def,
    eval_operand_update_var_avoids, eval_operand_mstore_eq]
QED

Theorem dyn_copy_result_prefix:
  !var_base elem_size dst_addr src_addr n ss.
    dyn_copy_result var_base elem_size dst_addr src_addr n ss =
      mcopy (w2n (dst_addr + 32w)) (w2n (src_addr + 32w))
        (w2n (n2w n * n2w elem_size : bytes32))
        (update_var (compiler_var_name var_base 5) (n2w n * n2w elem_size)
          (dyn_copy_prefix_result var_base dst_addr src_addr n ss))
Proof
  simp[dyn_copy_result_def, dyn_copy_prefix_result_def, LET_THM,
    compiler_var_names_EL, compiler_var_name_def]
QED
