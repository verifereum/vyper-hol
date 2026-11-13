(* TOP-LEVEL: the real typed-copy suffix increments its SSA counter and
   jumps from the recursive child's final block back to the parent header.
   Helpers allow replayed outputs and preserve all memory and other operands. *)
Theory typedArrayLoopCounter
Ancestors
  typedArrayLoopCode typedArrayLoopStructure abiStaticLoopCode
  ssaOperandFrame fragBlockPath fragExec compileEnv exprLoweringProps emitHelperProps
  venomExecSemantics venomState venomInst list rich_list words arithmetic finite_map

Definition typed_array_loop_counter_state_def:
  typed_array_loop_counter_state var_base counter (counter_word:bytes32) ss =
    update_var counter (counter_word + 1w)
      (update_var (compiler_var_name var_base 0) (counter_word + 1w) ss)
End

val typed_counter_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``ADD``, ``ASSIGN``, ``JMP``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem typed_array_loop_counter_split:
  !id var_base counter cond_label.
    typed_array_loop_counter id var_base counter cond_label =
      TAKE 2 (typed_array_loop_counter id var_base counter cond_label) ++
      [EL 2 (typed_array_loop_counter id var_base counter cond_label)]
Proof
  simp[typed_array_loop_counter_def]
QED

Theorem typed_array_loop_counter_prefix_straight:
  !id var_base counter cond_label.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 2 (typed_array_loop_counter id var_base counter cond_label)) /\
    LENGTH (TAKE 2 (typed_array_loop_counter id var_base counter cond_label)) = 2
Proof
  simp[typed_array_loop_counter_def, mk_inst_def, is_terminator_def]
QED

Theorem typed_array_loop_counter_execution:
  !id var_base counter cond_label ss counter_word.
    eval_operand (Var counter) ss = SOME counter_word ==>
    run_inst_seq (TAKE 2 (typed_array_loop_counter id var_base counter cond_label)) ss =
      OK (typed_array_loop_counter_state var_base counter counter_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  asm_simp_tac (srw_ss()) (typed_counter_steps @
    [typed_array_loop_counter_def, typed_array_loop_counter_state_def,
     run_inst_seq_def, mk_inst_def, exec_pure2_def, eval_operand_lit, eval_operand_update_var])
QED

Theorem typed_array_loop_counter_terminator:
  !id var_base counter cond_label ss counter_word index.
    step_inst_base (EL 2 (typed_array_loop_counter id var_base counter cond_label))
      ((typed_array_loop_counter_state var_base counter counter_word ss) with vs_inst_idx := index) =
    OK (jump_to cond_label (typed_array_loop_counter_state var_base counter counter_word ss))
Proof
  rpt gen_tac >> asm_simp_tac (srw_ss()) (typed_counter_steps @
    [typed_array_loop_counter_def, typed_array_loop_counter_state_def, mk_inst_def,
     jump_to_def, update_var_def, venom_state_component_equality])
QED

Theorem typed_array_loop_counter_control[simp]:
  !var_base counter counter_word ss.
    (typed_array_loop_counter_state var_base counter counter_word ss).vs_current_bb = ss.vs_current_bb /\
    (typed_array_loop_counter_state var_base counter counter_word ss).vs_inst_idx = ss.vs_inst_idx /\
    (typed_array_loop_counter_state var_base counter counter_word ss).vs_halted = ss.vs_halted /\
    (typed_array_loop_counter_state var_base counter counter_word ss).vs_memory = ss.vs_memory
Proof
  simp[typed_array_loop_counter_state_def, update_var_def]
QED

Theorem typed_array_loop_counter_operand_frame:
  !var_base counter counter_word ss arg_op.
    arg_op <> Var counter /\ arg_op <> Var (compiler_var_name var_base 0) ==>
    eval_operand arg_op (typed_array_loop_counter_state var_base counter counter_word ss) =
      eval_operand arg_op ss
Proof
  simp[typed_array_loop_counter_state_def, eval_operand_update_var_avoids]
QED

Theorem typed_array_loop_counter_value:
  !var_base counter counter_word ss.
    eval_operand (Var counter) (typed_array_loop_counter_state var_base counter counter_word ss) =
      SOME (counter_word + 1w)
Proof
  simp[typed_array_loop_counter_state_def, eval_operand_update_var]
QED

Theorem typed_array_loop_counter_path:
  !ctx func after counter cond_label exit_label ss counter_word header_bb.
    fn_has_code after (typed_array_loop_finish counter cond_label exit_label after) func /\
    ss.vs_current_bb = after.cs_current_bb /\ ss.vs_inst_idx = LENGTH after.cs_current_insts /\
    ~ss.vs_halted /\ eval_operand (Var counter) ss = SOME counter_word /\
    lookup_block cond_label func.fn_blocks = SOME header_bb /\
    phi_prefix_length header_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to cond_label (typed_array_loop_counter_state after.cs_next_var counter counter_word ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_array_loop_suffix_contains >> DISCH_TAC >>
  mp_tac (Q.SPECL [`after.cs_next_id`, `after.cs_next_var`, `counter`, `cond_label`, `ss`, `counter_word`]
    typed_array_loop_counter_execution) >> impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `typed_array_loop_counter_state after.cs_next_var counter counter_word ss`,
    `jump_to cond_label (typed_array_loop_counter_state after.cs_next_var counter counter_word ss)`,
    `<| bb_label := after.cs_current_bb;
        bb_instructions := after.cs_current_insts ++
          typed_array_loop_counter after.cs_next_id after.cs_next_var counter cond_label |>`,
    `header_bb`, `TAKE 2 (typed_array_loop_counter after.cs_next_id after.cs_next_var counter cond_label)`,
    `EL 2 (typed_array_loop_counter after.cs_next_id after.cs_next_var counter cond_label)`]
    fragment_path_block) >> impl_tac
  >- (simp[typed_array_loop_counter_split, typed_array_loop_counter_prefix_straight,
        typed_array_loop_counter_terminator, DROP_LENGTH_APPEND] >>
      simp[typed_array_loop_counter_def, mk_inst_def, is_terminator_def, jump_to_def]) >> simp[]
QED
