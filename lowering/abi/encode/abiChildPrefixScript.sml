(* TOP-LEVEL: execute the real dynamic-child prefix, retaining source memory
   and all operands outside its three generated names. Replayed names may
   already contain values, as required inside enclosing encoder loops. *)
Theory abiChildPrefix
Ancestors
  abiChildCode abiBytestringCode abiStaticLoopCode ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words arithmetic

Definition abi_child_prefix_state_def:
  abi_child_prefix_state var_base head_offset (dst_addr:bytes32) (dyn_addr:bytes32) ss =
    update_var (compiler_var_name var_base 2) (dst_addr + mload (w2n dyn_addr) ss)
      (update_var (compiler_var_name var_base 1) (mload (w2n dyn_addr) ss)
        (update_var (compiler_var_name var_base 0) (dst_addr + n2w head_offset) ss))
End

Theorem abi_child_prefix_frame:
  !var_base head_offset dst_addr dyn_addr ss.
    (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss).vs_memory = ss.vs_memory /\
    (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss).vs_halted = ss.vs_halted /\
    (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss).vs_current_bb = ss.vs_current_bb /\
    (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss).vs_inst_idx = ss.vs_inst_idx /\
    (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) with vs_vars := ss.vs_vars = ss
Proof
  simp[abi_child_prefix_state_def, update_var_def]
QED

Theorem abi_child_prefix_values:
  !var_base head_offset dst_addr dyn_addr ss.
    eval_operand (Var (compiler_var_name var_base 0))
      (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) = SOME (dst_addr + n2w head_offset) /\
    eval_operand (Var (compiler_var_name var_base 1))
      (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand (Var (compiler_var_name var_base 2))
      (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) = SOME (dst_addr + mload (w2n dyn_addr) ss)
Proof
  simp[abi_child_prefix_state_def, eval_operand_update_var, eval_operand_update_var_avoids, compiler_var_name_def]
QED

Theorem abi_child_prefix_operand_frame:
  !var_base head_offset dst_addr dyn_addr ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 3) ==>
    eval_operand arg_op (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss) =
      eval_operand arg_op ss
Proof
  simp[compiler_var_names_def, GENLIST_CONS, abi_child_prefix_state_def,
    compiler_var_name_def, eval_operand_update_var_avoids]
QED

Theorem abi_child_prefix_execution:
  !id var_base dst dyn_ptr head_offset ss dst_addr dyn_addr.
    eval_operand dst ss = SOME dst_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name) (compiler_var_names var_base 3) ==>
    run_inst_seq (abi_child_prefix_insts dst dyn_ptr head_offset id var_base) ss =
      OK (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compiler_var_names_def, GENLIST_CONS, compiler_var_name_def] >>
  strip_tac >>
  qabbrev_tac `after_head = update_var (compiler_var_name var_base 0) (dst_addr + n2w head_offset) ss` >>
  qabbrev_tac `after_offset = update_var (compiler_var_name var_base 1) (mload (w2n dyn_addr) ss) after_head` >>
  `abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss =
    update_var (compiler_var_name var_base 2) (dst_addr + mload (w2n dyn_addr) ss) after_offset` by
    simp[abi_child_prefix_state_def, Abbr`after_offset`, Abbr`after_head`] >>
  `step_inst_base (mk_inst id ADD [dst; Lit (n2w head_offset)] [compiler_var_name var_base 0]) ss =
    OK after_head` by
    (simp_tac bool_ss [Abbr`after_head`] >> irule step_ADD >> simp[eval_operand_lit]) >>
  `step_inst_base (mk_inst (id + 1) MLOAD [dyn_ptr] [compiler_var_name var_base 1]) after_head =
    OK after_offset` by
    (mp_tac (Q.SPECL [`dyn_ptr`, `dyn_addr`, `id + 1`, `compiler_var_name var_base 1`, `after_head`]
       step_MLOAD) >> impl_tac
     >- asm_simp_tac (srw_ss()) [Abbr`after_head`, eval_operand_update_var_avoids, compiler_var_name_def] >>
     simp[Abbr`after_offset`, Abbr`after_head`, mload_update_var]) >>
  `step_inst_base (mk_inst (id + 2) ADD [dst; Var (compiler_var_name var_base 1)]
    [compiler_var_name var_base 2]) after_offset =
    OK (abi_child_prefix_state var_base head_offset dst_addr dyn_addr ss)` by
    (asm_simp_tac bool_ss [] >>
     irule step_ADD >> asm_simp_tac (srw_ss()) [Abbr`after_offset`, Abbr`after_head`,
       eval_operand_update_var, eval_operand_update_var_avoids, compiler_var_name_def]) >>
  asm_simp_tac (srw_ss()) [abi_child_prefix_insts_def, run_inst_seq_def]
QED

Theorem abi_child_prefix_path:
  !ctx func dst dyn_ptr head_offset cs ss dst_addr dyn_addr.
    fn_has_code cs (abi_child_prefix_cut dst dyn_ptr head_offset cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name) (compiler_var_names cs.cs_next_var 3) ==>
    fragment_path ctx func ss
      ((abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss)
        with vs_inst_idx := LENGTH (abi_child_prefix_cut dst dyn_ptr head_offset cs).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `dst`, `dyn_ptr`, `head_offset`, `ss`, `dst_addr`, `dyn_addr`]
    abi_child_prefix_execution) >> impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `abi_child_prefix_cut dst dyn_ptr head_offset cs`, `ss`,
    `abi_child_prefix_state cs.cs_next_var head_offset dst_addr dyn_addr ss`] fragment_path_emitted) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [abi_child_prefix_cut_def, emitted_insts_def,
        same_blocks_def, DROP_LENGTH_APPEND] >>
      simp[abi_child_prefix_insts_def, mk_inst_def, is_terminator_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI child prefix execution: " ^ name)
  end) (DB.thms "abiChildPrefix")
