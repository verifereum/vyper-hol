(* TOP-LEVEL: execute the real dynamic-loop body prefix, computing its
   source, head and tail pointers while preserving the complete memory state. *)
Theory abiDynamicLoopBody
Ancestors
  abiDynamicLoopCode abiStaticLoopCode abiBytestringCode ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath
  venomExecSemantics venomState venomInst venomMemProps list words arithmetic
Libs wordsLib

Definition abi_dynamic_loop_body_state_def:
  abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz (counter_addr:bytes32) (dyn_addr:bytes32) ss =
    let index = mload (w2n counter_addr) ss in
    let tail_offset = mload (w2n dyn_addr) ss in
    update_var (compiler_var_name var_base 14) (dst_addr + 32w + tail_offset)
      (update_var (compiler_var_name var_base 13) tail_offset
        (update_var (compiler_var_name var_base 12) (dst_addr + 32w + index * n2w abi_sz)
          (update_var (compiler_var_name var_base 11) (index * n2w abi_sz)
            (update_var (compiler_var_name var_base 10) (dst_addr + 32w)
              (update_var (compiler_var_name var_base 9) (src_addr + 32w + index * n2w mem_sz)
                (update_var (compiler_var_name var_base 8) (index * n2w mem_sz)
                  (update_var (compiler_var_name var_base 7) (src_addr + 32w)
                    (update_var (compiler_var_name var_base 6) index ss))))))))
End

val dynamic_body_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``ADD``, ``MUL``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_dynamic_loop_body_straight:
  !id var_base dst src abi_sz mem_sz.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz)
Proof
  simp[abi_dynamic_loop_body_prefix_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_dynamic_loop_body_execution:
  !id var_base dst src abi_sz mem_sz ss dst_addr src_addr counter_addr dyn_addr.
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name var_base 1)) ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (var_base + 6) 9) ==>
    run_inst_seq (abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz) ss =
      OK (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss)
Proof
  rpt gen_tac >> strip_tac >> fs[compiler_var_names_def, GENLIST, compiler_var_name_def] >>
  asm_simp_tac (srw_ss()) (dynamic_body_steps @
    [abi_dynamic_loop_body_prefix_def, abi_dynamic_loop_body_state_def, compiler_var_name_def,
     run_inst_seq_def, mk_inst_def, exec_read1_def, exec_pure2_def,
     eval_operand_update_var_avoids, eval_operand_update_var, mload_update_var, eval_operand_lit, LET_THM])
QED

Theorem abi_dynamic_loop_body_values:
  !var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss.
    let boundary = abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss in
    eval_operand (Var (compiler_var_name var_base 6)) boundary = SOME (mload (w2n counter_addr) ss) /\
    eval_operand (Var (compiler_var_name var_base 9)) boundary =
      SOME (src_addr + 32w + mload (w2n counter_addr) ss * n2w mem_sz) /\
    eval_operand (Var (compiler_var_name var_base 12)) boundary =
      SOME (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) /\
    eval_operand (Var (compiler_var_name var_base 13)) boundary = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand (Var (compiler_var_name var_base 14)) boundary = SOME (dst_addr + 32w + mload (w2n dyn_addr) ss)
Proof
  simp[abi_dynamic_loop_body_state_def, LET_THM, eval_operand_update_var, eval_operand_update_var_avoids]
QED

Theorem abi_dynamic_loop_body_frame:
  !var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss.
    (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss)
      with vs_vars := ss.vs_vars = ss
Proof
  simp[abi_dynamic_loop_body_state_def, LET_THM, update_var_reset_vars]
QED

Theorem abi_dynamic_loop_body_operand_frame:
  !var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 6) 9) ==>
    eval_operand arg_op (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss) =
      eval_operand arg_op ss
Proof
  simp[abi_dynamic_loop_body_state_def, LET_THM, compiler_var_names_def, GENLIST,
    compiler_var_name_def, eval_operand_update_var_avoids]
QED

Theorem abi_dynamic_loop_body_path:
  !ctx func id var_base dst src abi_sz mem_sz ss dst_addr src_addr counter_addr dyn_addr body_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME body_bb /\
    isPREFIX (abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz) body_bb.bb_instructions /\
    ss.vs_inst_idx = 0 /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name var_base 1)) ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (var_base + 6) 9) ==>
    fragment_path ctx func ss
      ((abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss)
        with vs_inst_idx := 9)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `dst`, `src`, `abi_sz`, `mem_sz`, `ss`,
    `dst_addr`, `src_addr`, `counter_addr`, `dyn_addr`] abi_dynamic_loop_body_execution) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss`, `body_bb`,
    `abi_dynamic_loop_body_prefix id var_base dst src abi_sz mem_sz`] fragment_path_prefix) >>
  impl_tac >- simp[abi_dynamic_loop_body_straight] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop child-address prefix: " ^ name)
  end) (DB.thms "abiDynamicLoopBody")
