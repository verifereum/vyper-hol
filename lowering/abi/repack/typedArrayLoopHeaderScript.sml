(* TOP-LEVEL: the actual typed array-copy header branches on its SSA counter
   and saved bound. Earlier iterations may already have written its outputs.
   Helpers preserve memory, the counter and operands outside those outputs. *)
Theory typedArrayLoopHeader
Ancestors
  typedArrayLoopCode abiStaticLoopCode ssaOperandFrame fragBlockPath fragExec
  compileEnv exprLoweringProps emitHelperProps venomExecSemantics venomState venomInst
  list rich_list words arithmetic finite_map

Definition typed_array_loop_header_state_def:
  typed_array_loop_header_state var_base (counter_word:bytes32) (len_word:bytes32) ss =
    let more = (w2n counter_word < w2n len_word) in
    update_var (compiler_var_name var_base 2) (bool_to_word (~more))
      (update_var (compiler_var_name var_base 1) (bool_to_word more) ss)
End

val typed_header_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``LT``, ``ISZERO``, ``JNZ``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem typed_array_loop_header_split:
  !id var_base body_label exit_label len_op.
    typed_array_loop_header id var_base body_label exit_label len_op =
      TAKE 2 (typed_array_loop_header id var_base body_label exit_label len_op) ++
      [EL 2 (typed_array_loop_header id var_base body_label exit_label len_op)]
Proof
  simp[typed_array_loop_header_def]
QED

Theorem typed_array_loop_header_prefix_straight:
  !id var_base body_label exit_label len_op.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 2 (typed_array_loop_header id var_base body_label exit_label len_op))
Proof
  simp[typed_array_loop_header_def, mk_inst_def, is_terminator_def]
QED

Theorem typed_array_loop_header_prefix_length[simp]:
  !id var_base body_label exit_label len_op.
    LENGTH (TAKE 2 (typed_array_loop_header id var_base body_label exit_label len_op)) = 2
Proof
  simp[typed_array_loop_header_def]
QED

Theorem typed_array_loop_header_no_phi:
  !id var_base body_label exit_label len_op.
    phi_prefix_length (typed_array_loop_header id var_base body_label exit_label len_op) = 0
Proof
  simp[typed_array_loop_header_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem typed_array_loop_body_no_phi:
  !id var_base dst src dst_size src_size insts.
    isPREFIX (typed_array_loop_addresses id var_base dst src dst_size src_size) insts ==>
    phi_prefix_length insts = 0
Proof
  simp[IS_PREFIX_APPEND, typed_array_loop_addresses_def] >> rpt strip_tac >>
  gvs[phi_prefix_length_def, mk_inst_def]
QED

Theorem typed_array_loop_header_execution:
  !id var_base body_label exit_label len_op ss counter_word len_word.
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_word /\
    eval_operand len_op ss = SOME len_word ==>
    run_inst_seq (TAKE 2 (typed_array_loop_header id var_base body_label exit_label len_op)) ss =
      OK (typed_array_loop_header_state var_base counter_word len_word ss)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `w2n counter_word < w2n len_word` >>
  asm_simp_tac (srw_ss()) (typed_header_steps @
    [typed_array_loop_header_def, typed_array_loop_header_state_def,
     run_inst_seq_def, mk_inst_def, exec_pure1_def, exec_pure2_def,
     eval_operand_update_var, bool_to_word_def, LET_THM])
QED

Theorem typed_array_loop_header_terminator:
  !id var_base body_label exit_label len_op ss counter_word len_word.
    step_inst_base (EL 2 (typed_array_loop_header id var_base body_label exit_label len_op))
      ((typed_array_loop_header_state var_base counter_word len_word ss) with vs_inst_idx := 2) =
    OK (jump_to (if w2n counter_word < w2n len_word then body_label else exit_label)
      (typed_array_loop_header_state var_base counter_word len_word ss))
Proof
  rpt gen_tac >> Cases_on `w2n counter_word < w2n len_word` >>
  asm_simp_tac (srw_ss()) (typed_header_steps @
    [typed_array_loop_header_def, typed_array_loop_header_state_def, mk_inst_def,
     eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, bool_to_word_def, LET_THM,
     jump_to_def, update_var_def, venom_state_component_equality])
QED

Theorem typed_array_loop_header_frame:
  !var_base counter_word len_word ss.
    (typed_array_loop_header_state var_base counter_word len_word ss) with vs_vars := ss.vs_vars = ss
Proof
  simp[typed_array_loop_header_state_def, LET_THM, update_var_reset_vars]
QED

Theorem typed_array_loop_header_control[simp]:
  !var_base counter_word len_word ss.
    (typed_array_loop_header_state var_base counter_word len_word ss).vs_current_bb = ss.vs_current_bb /\
    (typed_array_loop_header_state var_base counter_word len_word ss).vs_inst_idx = ss.vs_inst_idx /\
    (typed_array_loop_header_state var_base counter_word len_word ss).vs_halted = ss.vs_halted /\
    (typed_array_loop_header_state var_base counter_word len_word ss).vs_memory = ss.vs_memory
Proof
  simp[typed_array_loop_header_state_def, LET_THM, update_var_def]
QED

Theorem typed_array_loop_header_operand_frame:
  !var_base counter_word len_word ss arg_op.
    arg_op <> Var (compiler_var_name var_base 1) /\
    arg_op <> Var (compiler_var_name var_base 2) ==>
    eval_operand arg_op (typed_array_loop_header_state var_base counter_word len_word ss) =
      eval_operand arg_op ss
Proof
  simp[typed_array_loop_header_state_def, LET_THM, eval_operand_update_var_avoids]
QED

Theorem typed_array_loop_header_path:
  !ctx func id var_base body_label exit_label len_op ss counter_word len_word header_bb next_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = typed_array_loop_header id var_base body_label exit_label len_op /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_word /\
    eval_operand len_op ss = SOME len_word /\
    lookup_block (if w2n counter_word < w2n len_word then body_label else exit_label)
      func.fn_blocks = SOME next_bb /\ phi_prefix_length next_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to (if w2n counter_word < w2n len_word then body_label else exit_label)
        (typed_array_loop_header_state var_base counter_word len_word ss))
Proof
  rpt gen_tac >> strip_tac >> drule_all typed_array_loop_header_execution >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `typed_array_loop_header_state var_base counter_word len_word ss`,
    `jump_to (if w2n (counter_word:bytes32) < w2n (len_word:bytes32) then body_label else exit_label)
      (typed_array_loop_header_state var_base counter_word len_word ss)`,
    `header_bb`, `next_bb`,
    `TAKE 2 (typed_array_loop_header id var_base body_label exit_label len_op)`,
    `EL 2 (typed_array_loop_header id var_base body_label exit_label len_op)`]
    fragment_path_block) >> impl_tac
  >- (simp[typed_array_loop_header_prefix_straight, typed_array_loop_header_terminator] >>
      simp[typed_array_loop_header_def, mk_inst_def, is_terminator_def, jump_to_def]) >> simp[]
QED
