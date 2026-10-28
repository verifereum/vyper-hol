(* TOP-LEVEL: the static-element ABI loop's open exit computes
   32 + length * element_size and preserves payload memory. *)
Theory abiStaticLoopExit
Ancestors
  abiStaticLoopCode abiStaticLoopCodeProps ssaOperandFrame fragBlockPath fragExec
  compileEnv exprLoweringProps emitHelperProps instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words arithmetic
Libs wordsLib

Definition abi_static_loop_exit_state_def:
  abi_static_loop_exit_state var_base (src_addr:bytes32) info abi_sz ss =
    let length_word = mload (w2n src_addr) ss in
    let payload_size = length_word * n2w abi_sz in
    update_var (compiler_var_name var_base (14 + static_info_var_count info))
      (32w + payload_size)
      (update_var (compiler_var_name var_base (13 + static_info_var_count info))
        payload_size
        (update_var (compiler_var_name var_base (12 + static_info_var_count info))
          length_word ss))
End

Definition abi_static_loop_exit_names_def:
  abi_static_loop_exit_names var_base info =
    [compiler_var_name var_base (12 + static_info_var_count info);
     compiler_var_name var_base (13 + static_info_var_count info);
     compiler_var_name var_base (14 + static_info_var_count info)]
End

val exit_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``MUL``, ``ADD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_static_loop_exit_length[simp]:
  !id var_base src info abi_sz.
    LENGTH (abi_static_loop_exit id var_base src info abi_sz) = 3
Proof
  simp[abi_static_loop_exit_def]
QED

Theorem abi_static_loop_exit_execution:
  !id var_base src info abi_sz ss src_addr.
    eval_operand src ss = SOME src_addr ==>
    run_inst_seq (abi_static_loop_exit id var_base src info abi_sz) ss =
      OK (abi_static_loop_exit_state var_base src_addr info abi_sz ss)
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) (exit_steps @
    [abi_static_loop_exit_def, abi_static_loop_exit_state_def,
     run_inst_seq_def, mk_inst_def, exec_read1_def, exec_pure2_def,
     eval_operand_update_var, eval_operand_lit, LET_THM])
QED

Theorem abi_static_loop_exit_value:
  !var_base src_addr info abi_sz ss.
    eval_operand (Var (compiler_var_name var_base (14 + static_info_var_count info)))
      (abi_static_loop_exit_state var_base src_addr info abi_sz ss) =
      SOME (32w + mload (w2n src_addr) ss * n2w abi_sz)
Proof
  simp[abi_static_loop_exit_state_def, LET_THM, eval_operand_update_var]
QED

Theorem abi_static_loop_exit_state_frame:
  !var_base src_addr info abi_sz ss.
    (abi_static_loop_exit_state var_base src_addr info abi_sz ss)
      with vs_vars := ss.vs_vars = ss
Proof
  simp[abi_static_loop_exit_state_def, LET_THM, update_var_reset_vars]
QED

Theorem abi_static_loop_exit_operand_frame:
  !var_base src_addr info abi_sz ss arg_op.
    EVERY (\name. arg_op <> Var name) (abi_static_loop_exit_names var_base info) ==>
    eval_operand arg_op (abi_static_loop_exit_state var_base src_addr info abi_sz ss) =
      eval_operand arg_op ss
Proof
  simp[abi_static_loop_exit_names_def, abi_static_loop_exit_state_def,
    LET_THM, eval_operand_update_var_avoids]
QED

Theorem abi_static_loop_exit_size_exact:
  !src_addr ss n abi_sz.
    mload (w2n src_addr) ss = n2w n /\ 32 + n * abi_sz < dimword(:256) ==>
    w2n (32w + mload (w2n src_addr) ss * n2w abi_sz) = 32 + n * abi_sz
Proof
  simp[word_mul_n2w, word_add_n2w, w2n_n2w]
QED

Theorem abi_static_loop_exit_path:
  !ctx func id var_base src info abi_sz ss src_addr exit_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME exit_bb /\
    isPREFIX (abi_static_loop_exit id var_base src info abi_sz) exit_bb.bb_instructions /\
    ss.vs_inst_idx = 0 /\ eval_operand src ss = SOME src_addr ==>
    fragment_path ctx func ss
      ((abi_static_loop_exit_state var_base src_addr info abi_sz ss) with vs_inst_idx := 3)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `abi_static_loop_exit_state var_base src_addr info abi_sz ss`, `exit_bb`,
    `abi_static_loop_exit id var_base src info abi_sz`] fragment_path_prefix) >>
  simp[abi_static_loop_exit_execution, abi_static_loop_exit_straight]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop exit theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopExit")
