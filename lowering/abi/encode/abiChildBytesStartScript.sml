(* TOP-LEVEL: the real dynamic-child prefix supplies every input and saved
   operand needed by the closed bytestring encoder and its parent suffix. *)
Theory abiChildBytesStart
Ancestors
  abiChildBytesReady abiChildPrefix abiChildCode abiBytestringCorrect abiBytestringCode
  abiStaticLoopCode instIdxIndep compileEnv venomState list words arithmetic

Theorem abi_child_bytes_start_ready:
  !dst src dyn_ptr head_offset cs ss dst_addr dyn_addr src_addr bs.
    eval_operand src ss = SOME src_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ dyn_ptr <> Var name) (compiler_var_names cs.cs_next_var 12) /\
    bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs ss ==>
    let addressed = (abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
      vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts in
    eval_operand src addressed = SOME src_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 2)) addressed = SOME (dst_addr + mload (w2n dyn_addr) ss) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) addressed = SOME (dst_addr + n2w head_offset) /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) addressed = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand dyn_ptr addressed = SOME dyn_addr /\
    EVERY (\name. src <> Var name /\ Var (compiler_var_name cs.cs_next_var 2) <> Var name)
      (compiler_var_names (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_next_var 8) /\
    EVERY (\name. Var (compiler_var_name cs.cs_next_var 0) <> Var name /\
      Var (compiler_var_name cs.cs_next_var 1) <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_next_var 8) /\
    bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs addressed /\
    dyn_ptr <> Var (compiler_var_name (cs.cs_next_var + 11) 0)
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `EVERY _ (compiler_var_names _ 12)`
    (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`src`, `cs.cs_next_var`] abi_child_bytes_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`dyn_ptr`, `cs.cs_next_var`] abi_child_bytes_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPEC `cs.cs_next_var` abi_child_bytes_saved_names) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `head_offset`, `dst_addr`, `dyn_addr`, `ss`, `src`]
    abi_child_prefix_operand_frame) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `head_offset`, `dst_addr`, `dyn_addr`, `ss`, `dyn_ptr`]
    abi_child_prefix_operand_frame) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  `bytestring_abi_pre (dst_addr + mload (w2n dyn_addr) ss) src_addr bs
    ((abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
      vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts)` by
    (mp_tac (Q.SPECL [`dst_addr + mload (w2n (dyn_addr:bytes32)) ss`, `src_addr`, `bs`, `ss`,
      `(abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss) with
        vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts`]
      bytestring_abi_pre_memory) >>
     impl_tac >- simp[abi_child_prefix_frame] >> simp[]) >>
  fs[abi_child_prefix_cut_def, eval_op_inst_idx, abi_child_prefix_values, EVERY_CONJ]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed bytestring child prefix preparation: " ^ name)
  end) (DB.thms "abiChildBytesStart")
