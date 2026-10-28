(* TOP-LEVEL: the real loop exit reads its source header, loads the completed
   dynamic offset and returns 32 plus that offset without changing memory. *)
Theory abiDynamicLoopExit
Ancestors
  abiDynamicLoopCode abiStaticLoopCode ssaOperandFrame abiMemoryFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath
  venomExecSemantics venomState venomInst venomMemProps list words arithmetic
Libs wordsLib

Definition abi_dynamic_loop_exit_state_def:
  abi_dynamic_loop_exit_state var_base (src_addr:bytes32) (dyn_addr:bytes32) ss =
    update_var (compiler_var_name var_base 2) (32w + mload (w2n dyn_addr) ss)
      (update_var (compiler_var_name var_base 1) (mload (w2n dyn_addr) ss)
        (update_var (compiler_var_name var_base 0) (mload (w2n src_addr) ss) ss))
End

val dynamic_exit_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``ADD``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_dynamic_loop_exit_straight:
  !id var_base src dyn_ptr.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (abi_dynamic_loop_exit id var_base src dyn_ptr)
Proof
  simp[abi_dynamic_loop_exit_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_dynamic_loop_exit_execution:
  !id var_base src dyn_ptr ss src_addr dyn_addr.
    eval_operand src ss = SOME src_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    dyn_ptr <> Var (compiler_var_name var_base 0) ==>
    run_inst_seq (abi_dynamic_loop_exit id var_base src dyn_ptr) ss =
      OK (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss)
Proof
  rpt gen_tac >> strip_tac >> asm_simp_tac (srw_ss()) (dynamic_exit_steps @
    [abi_dynamic_loop_exit_def, abi_dynamic_loop_exit_state_def, run_inst_seq_def, mk_inst_def,
     exec_read1_def, exec_pure2_def, eval_operand_lit,
     eval_operand_update_var_avoids, eval_operand_update_var, mload_update_var])
QED

Theorem abi_dynamic_loop_exit_frame:
  !var_base src_addr dyn_addr ss.
    (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss) with vs_vars := ss.vs_vars = ss /\
    (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss).vs_halted = ss.vs_halted /\
    abi_memory_frame [] ss (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss)
Proof
  simp[abi_dynamic_loop_exit_state_def, update_var_reset_vars, update_var_def,
    abi_memory_frame_def, read_memory_def]
QED

Theorem abi_dynamic_loop_exit_value:
  !var_base src_addr dyn_addr ss.
    eval_operand (Var (compiler_var_name var_base 2)) (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss) =
      SOME (32w + mload (w2n dyn_addr) ss)
Proof
  simp[abi_dynamic_loop_exit_state_def, eval_operand_update_var]
QED

Theorem abi_dynamic_loop_exit_operand_frame:
  !var_base src_addr dyn_addr ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) /\ arg_op <> Var (compiler_var_name var_base 1) /\
    arg_op <> Var (compiler_var_name var_base 2) ==>
    eval_operand arg_op (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss) = eval_operand arg_op ss
Proof
  simp[abi_dynamic_loop_exit_state_def, eval_operand_update_var_avoids]
QED

Theorem abi_dynamic_loop_exit_path:
  !ctx func id var_base src dyn_ptr ss src_addr dyn_addr exit_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME exit_bb /\
    isPREFIX (abi_dynamic_loop_exit id var_base src dyn_ptr) exit_bb.bb_instructions /\ ss.vs_inst_idx = 0 /\
    eval_operand src ss = SOME src_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    dyn_ptr <> Var (compiler_var_name var_base 0) ==>
    fragment_path ctx func ss ((abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss) with vs_inst_idx := 3)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `src`, `dyn_ptr`, `ss`, `src_addr`, `dyn_addr`]
    abi_dynamic_loop_exit_execution) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss`, `exit_bb`,
    `abi_dynamic_loop_exit id var_base src dyn_ptr`] fragment_path_prefix) >>
  impl_tac >- simp[abi_dynamic_loop_exit_straight] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop exit execution: " ^ name)
  end) (DB.thms "abiDynamicLoopExit")
