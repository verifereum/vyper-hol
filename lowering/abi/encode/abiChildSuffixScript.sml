(* TOP-LEVEL: the real dynamic-child suffix records its relative head offset
   and advances the parent's tail cell by the child's encoded length.
   Its exact state effect supplies memory and operand frames for composition. *)
Theory abiChildSuffix
Ancestors
  abiChildCode abiStaticLoopCode ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words arithmetic

Definition abi_child_suffix_state_def:
  abi_child_suffix_state var_base (head_addr:bytes32) (dyn_addr:bytes32) tail_offset child_len ss =
    mstore (w2n dyn_addr) (tail_offset + child_len)
      (update_var (compiler_var_name var_base 0) (tail_offset + child_len)
        (mstore (w2n head_addr) tail_offset ss))
End

Theorem abi_child_suffix_control[simp]:
  !var_base head_addr dyn_addr tail_offset child_len ss.
    (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss).vs_current_bb = ss.vs_current_bb /\
    (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss).vs_inst_idx = ss.vs_inst_idx /\
    (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss).vs_halted = ss.vs_halted
Proof
  simp_tac (pure_ss ++ boolSimps.BOOL_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM, LET_THM])
    [abi_child_suffix_state_def, mstore_def, write_memory_with_expansion_def, update_var_def]
QED

Theorem abi_child_suffix_operand_frame:
  !var_base head_addr dyn_addr tail_offset child_len ss arg_op.
    arg_op <> Var (compiler_var_name var_base 0) ==>
    eval_operand arg_op (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss) =
      eval_operand arg_op ss
Proof
  simp[abi_child_suffix_state_def, eval_operand_mstore_eq, eval_operand_update_var_avoids]
QED

Theorem abi_child_suffix_execution:
  !id var_base head_ptr tail_op dyn_ptr len_op ss head_addr dyn_addr tail_offset child_len.
    eval_operand head_ptr ss = SOME head_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    eval_operand tail_op ss = SOME tail_offset /\ eval_operand len_op ss = SOME child_len /\
    dyn_ptr <> Var (compiler_var_name var_base 0) ==>
    run_inst_seq (abi_child_suffix_insts head_ptr tail_op dyn_ptr len_op id var_base) ss =
      OK (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `written = mstore (w2n head_addr) tail_offset ss` >>
  qabbrev_tac `advanced = update_var (compiler_var_name var_base 0) (tail_offset + child_len) written` >>
  `abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss =
    mstore (w2n dyn_addr) (tail_offset + child_len) advanced` by
    simp[abi_child_suffix_state_def, Abbr`advanced`, Abbr`written`] >>
  `step_inst_base (mk_inst id MSTORE [head_ptr; tail_op] []) ss = OK written` by
    (simp_tac bool_ss [Abbr`written`] >> irule step_MSTORE >> simp[]) >>
  `step_inst_base (mk_inst (id + 1) ADD [tail_op; len_op] [compiler_var_name var_base 0]) written =
    OK advanced` by
    (simp_tac bool_ss [Abbr`advanced`] >> irule step_ADD >> simp[Abbr`written`, eval_operand_mstore_eq]) >>
  `step_inst_base (mk_inst (id + 2) MSTORE [dyn_ptr; Var (compiler_var_name var_base 0)] []) advanced =
    OK (abi_child_suffix_state var_base head_addr dyn_addr tail_offset child_len ss)` by
    (asm_simp_tac bool_ss [] >>
     irule step_MSTORE >> simp[Abbr`advanced`, Abbr`written`, eval_operand_mstore_eq,
       eval_operand_update_var, eval_operand_update_var_avoids]) >>
  asm_simp_tac (srw_ss()) [abi_child_suffix_insts_def, run_inst_seq_def]
QED

Theorem abi_child_suffix_path:
  !ctx func head_ptr tail_op dyn_ptr len_op cs ss head_addr dyn_addr tail_offset child_len.
    fn_has_code cs (abi_child_suffix_cut head_ptr tail_op dyn_ptr len_op cs) func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\
    eval_operand head_ptr ss = SOME head_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    eval_operand tail_op ss = SOME tail_offset /\ eval_operand len_op ss = SOME child_len /\
    dyn_ptr <> Var (compiler_var_name cs.cs_next_var 0) ==>
    fragment_path ctx func ss
      ((abi_child_suffix_state cs.cs_next_var head_addr dyn_addr tail_offset child_len ss)
        with vs_inst_idx := LENGTH (abi_child_suffix_cut head_ptr tail_op dyn_ptr len_op cs).cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_id`, `cs.cs_next_var`, `head_ptr`, `tail_op`, `dyn_ptr`, `len_op`, `ss`,
    `head_addr`, `dyn_addr`, `tail_offset`, `child_len`] abi_child_suffix_execution) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs`, `abi_child_suffix_cut head_ptr tail_op dyn_ptr len_op cs`, `ss`,
    `abi_child_suffix_state cs.cs_next_var head_addr dyn_addr tail_offset child_len ss`] fragment_path_emitted) >>
  impl_tac
  >- (asm_simp_tac (srw_ss()) [abi_child_suffix_cut_def, emitted_insts_def,
        same_blocks_def, DROP_LENGTH_APPEND] >>
      simp[abi_child_suffix_insts_def, mk_inst_def, is_terminator_def]) >> simp[]
QED
