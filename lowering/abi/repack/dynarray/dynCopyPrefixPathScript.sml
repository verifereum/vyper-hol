(* TOP-LEVEL: the actual dynamic-array prefix executes to its compiler cut
   in the containing function. It saves the live length and payload pointers
   and preserves every operand outside its five generated names. *)
Theory dynCopyPrefixPath
Ancestors
  typedCopyStateFrame
  typedCopyLoopStateFrame typedDynLoopCode dynCopyPrefixExec dynCopyCode abiBytestringCode abiStaticLoopCode
  fragBlockPath fragExec compileEnv exprLoweringProps instIdxIndep venomState venomInst
  list rich_list words arithmetic

Theorem dyn_copy_prefix_code:
  !cs dst src capacity.
    same_blocks cs (dyn_copy_prefix_state cs dst src capacity) /\
    emitted_insts cs (dyn_copy_prefix_state cs dst src capacity) =
      dyn_copy_prefix_insts cs.cs_next_id (compiler_var_names cs.cs_next_var 5) dst src capacity /\
    (dyn_copy_prefix_state cs dst src capacity).cs_current_insts = cs.cs_current_insts ++
      emitted_insts cs (dyn_copy_prefix_state cs dst src capacity)
Proof
  simp[same_blocks_def, emitted_insts_def, dyn_copy_prefix_state_def, DROP_LENGTH_APPEND]
QED

Theorem dyn_copy_prefix_path:
  !ctx func cs dst src capacity ss dst_addr src_addr n.
    fn_has_code cs (dyn_copy_prefix_state cs dst src capacity) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    n <= capacity /\ capacity < dimword(:256) /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    mload (w2n src_addr) ss = n2w n /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
    ?entry_ss. fragment_path ctx func ss entry_ss /\ copy_state_frame ss entry_ss /\
      entry_ss.vs_current_bb = (dyn_copy_prefix_state cs dst src capacity).cs_current_bb /\
      entry_ss.vs_inst_idx = LENGTH (dyn_copy_prefix_state cs dst src capacity).cs_current_insts /\
      entry_ss.vs_halted = ss.vs_halted /\
      entry_ss.vs_memory = (mstore (w2n dst_addr) (n2w n) ss).vs_memory /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 0)) entry_ss = SOME (n2w n) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 3)) entry_ss = SOME (src_addr + 32w) /\
      eval_operand (Var (compiler_var_name cs.cs_next_var 4)) entry_ss = SOME (dst_addr + 32w) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 5) ==>
        eval_operand arg_op entry_ss = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `dyn_copy_prefix_state cs dst src capacity`, `ss`,
    `dyn_copy_prefix_result cs.cs_next_var dst_addr src_addr n ss`] fragment_path_emitted) >>
  impl_tac >- simp[dyn_copy_prefix_code, dyn_copy_prefix_straight, dyn_copy_prefix_execution] >> strip_tac >>
  qexists_tac `(dyn_copy_prefix_result cs.cs_next_var dst_addr src_addr n ss)
    with vs_inst_idx := LENGTH (dyn_copy_prefix_state cs dst src capacity).cs_current_insts` >>
  simp[eval_op_inst_idx, dyn_copy_prefix_result_memory,
    dyn_copy_prefix_result_values, dyn_copy_prefix_result_operand_frame]
QED
