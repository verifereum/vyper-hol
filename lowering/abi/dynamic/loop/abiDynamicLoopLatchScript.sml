(* TOP-LEVEL: the actual loop latch increments the saved index, writes its
   counter cell and jumps back to the header, preserving disjoint windows. *)
Theory abiDynamicLoopLatch
Ancestors
  abiDynamicLoopCode abiStaticLoopCode abiStaticLoopBody abiMemoryFrame memoryReadProps memoryValueAbiExec
  ssaOperandFrame compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath
  venomExecSemantics venomState venomInst venomMemProps list words arithmetic
Libs wordsLib

Definition abi_dynamic_loop_latch_state_def:
  abi_dynamic_loop_latch_state var_base (counter_addr:bytes32) (index:bytes32) ss =
    mstore (w2n counter_addr) (index + 1w)
      (update_var (compiler_var_name var_base 0) (index + 1w) ss)
End

val dynamic_latch_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``ADD``, ``MSTORE``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_dynamic_loop_latch_straight:
  !id var_base i_ptr i_op header_label.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 2 (abi_dynamic_loop_latch id var_base i_ptr i_op header_label))
Proof
  simp[abi_dynamic_loop_latch_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_dynamic_loop_latch_execution:
  !id var_base i_ptr i_op header_label ss counter_addr index.
    eval_operand i_ptr ss = SOME counter_addr /\ eval_operand i_op ss = SOME index /\
    i_ptr <> Var (compiler_var_name var_base 0) ==>
    run_inst_seq (TAKE 2 (abi_dynamic_loop_latch id var_base i_ptr i_op header_label)) ss =
      OK (abi_dynamic_loop_latch_state var_base counter_addr index ss)
Proof
  rpt gen_tac >> strip_tac >> asm_simp_tac (srw_ss()) (dynamic_latch_steps @
    [abi_dynamic_loop_latch_def, abi_dynamic_loop_latch_state_def, run_inst_seq_def, mk_inst_def,
     exec_pure2_def, exec_write2_def, eval_operand_lit, eval_operand_update_var_avoids, eval_operand_update_var])
QED

Theorem abi_dynamic_loop_latch_control:
  !var_base counter_addr index ss.
    (abi_dynamic_loop_latch_state var_base counter_addr index ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynamic_loop_latch_state var_base counter_addr index ss).vs_halted = ss.vs_halted /\
    mload (w2n counter_addr) (abi_dynamic_loop_latch_state var_base counter_addr index ss) = index + 1w
Proof
  simp[abi_dynamic_loop_latch_state_def, mload_mstore_same]
QED

Theorem abi_dynamic_loop_latch_memory_frame:
  !var_base counter_addr index ss.
    abi_memory_frame [(w2n counter_addr,32)] ss (abi_dynamic_loop_latch_state var_base counter_addr index ss)
Proof
  simp[abi_dynamic_loop_latch_state_def, mstore_update_var, abi_memory_frame_update_var, abi_memory_frame_mstore]
QED

Theorem abi_dynamic_loop_latch_operand_frame:
  !var_base counter_addr index ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) ==>
    eval_operand arg_op (abi_dynamic_loop_latch_state var_base counter_addr index ss) = eval_operand arg_op ss
Proof
  simp[abi_dynamic_loop_latch_state_def, eval_operand_mstore_eq, eval_operand_update_var_avoids]
QED

Theorem abi_dynamic_loop_latch_terminator:
  !id var_base i_ptr i_op header_label ss inst_idx.
    step_inst_base (EL 2 (abi_dynamic_loop_latch id var_base i_ptr i_op header_label))
      (ss with vs_inst_idx := inst_idx) = OK (jump_to header_label ss)
Proof
  simp[abi_dynamic_loop_latch_def, step_inst_base_jump_index]
QED

Theorem abi_dynamic_loop_latch_path:
  !ctx func id var_base i_ptr i_op header_label ss counter_addr index body_bb header_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME body_bb /\
    DROP ss.vs_inst_idx body_bb.bb_instructions = abi_dynamic_loop_latch id var_base i_ptr i_op header_label /\
    ~ss.vs_halted /\ eval_operand i_ptr ss = SOME counter_addr /\ eval_operand i_op ss = SOME index /\
    i_ptr <> Var (compiler_var_name var_base 0) /\
    lookup_block header_label func.fn_blocks = SOME header_bb /\ phi_prefix_length header_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss (jump_to header_label (abi_dynamic_loop_latch_state var_base counter_addr index ss))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `i_ptr`, `i_op`, `header_label`, `ss`, `counter_addr`, `index`]
    abi_dynamic_loop_latch_execution) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `abi_dynamic_loop_latch_state var_base counter_addr index ss`,
    `jump_to header_label (abi_dynamic_loop_latch_state var_base counter_addr index ss)`, `body_bb`, `header_bb`,
    `TAKE 2 (abi_dynamic_loop_latch id var_base i_ptr i_op header_label)`,
    `EL 2 (abi_dynamic_loop_latch id var_base i_ptr i_op header_label)`] fragment_path_block) >>
  impl_tac
  >- (simp[abi_dynamic_loop_latch_straight, abi_dynamic_loop_latch_terminator,
        abi_dynamic_loop_latch_control, jump_to_def] >>
      simp[abi_dynamic_loop_latch_def, mk_inst_def, is_terminator_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop latch execution: " ^ name)
  end) (DB.thms "abiDynamicLoopLatch")
