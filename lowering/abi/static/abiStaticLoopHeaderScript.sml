(* TOP-LEVEL: the generated ABI array-loop header loads the counter and
   branches to the body exactly when it is below the saved length.
   Generated header outputs may already be defined by earlier iterations. *)
Theory abiStaticLoopHeader
Ancestors
  abiStaticLoopCode ssaOperandFrame fragBlockPath fragExec compileEnv
  exprLoweringProps emitHelperProps venomExecSemantics venomState venomInst
  list rich_list words arithmetic finite_map
Libs wordsLib

Definition abi_static_loop_header_state_def:
  abi_static_loop_header_state base (counter_addr:bytes32) (len_word:bytes32) ss =
    let counter = mload (w2n counter_addr) ss in
    let more = (w2n counter < w2n len_word) in
    update_var (compiler_var_name base 3) (bool_to_word (~more))
      (update_var (compiler_var_name base 2) (bool_to_word more)
        (update_var (compiler_var_name base 1) counter ss))
End

val header_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc)
       [``MLOAD``, ``LT``, ``ISZERO``, ``JNZ``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_static_loop_header_prefix_straight:
  !id base labels len_op.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 3 (abi_static_loop_header id base labels len_op))
Proof
  simp[abi_static_loop_header_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_static_loop_header_split:
  !id base labels len_op.
    abi_static_loop_header id base labels len_op =
      TAKE 3 (abi_static_loop_header id base labels len_op) ++
      [EL 3 (abi_static_loop_header id base labels len_op)]
Proof
  simp[abi_static_loop_header_def]
QED

Theorem abi_static_loop_header_prefix_length[simp]:
  !id base labels len_op.
    LENGTH (TAKE 3 (abi_static_loop_header id base labels len_op)) = 3
Proof
  simp[abi_static_loop_header_def]
QED

Theorem abi_static_loop_header_execution:
  !id base labels len_op ss counter_addr len_word.
    eval_operand (Var (compiler_var_name base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME len_word /\
    len_op <> Var (compiler_var_name base 1) ==>
    run_inst_seq (TAKE 3 (abi_static_loop_header id base labels len_op)) ss =
      OK (abi_static_loop_header_state base counter_addr len_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `w2n (mload (w2n counter_addr) ss) < w2n len_word` >>
  asm_simp_tac (srw_ss()) (header_steps @
    [abi_static_loop_header_def, abi_static_loop_header_state_def,
     run_inst_seq_def, mk_inst_def, exec_read1_def, exec_pure1_def, exec_pure2_def,
     eval_operand_update_var_avoids, eval_operand_update_var,
     mload_update_var, bool_to_word_def, LET_THM])
QED

Theorem abi_static_loop_header_terminator:
  !id base labels len_op ss counter_addr len_word.
    step_inst_base (EL 3 (abi_static_loop_header id base labels len_op))
      ((abi_static_loop_header_state base counter_addr len_word ss)
        with vs_inst_idx := 3) =
      OK (jump_to
        (if w2n (mload (w2n counter_addr) ss) < w2n len_word then
           fresh_label_output "enc_dyn_body" (labels + 1)
         else fresh_label_output "enc_dyn_exit" (labels + 2))
        (abi_static_loop_header_state base counter_addr len_word ss))
Proof
  rpt gen_tac >>
  Cases_on `w2n (mload (w2n counter_addr) ss) < w2n len_word` >>
  asm_simp_tac (srw_ss()) (header_steps @
    [abi_static_loop_header_def, abi_static_loop_header_state_def, mk_inst_def,
     eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, bool_to_word_def, LET_THM,
     jump_to_def, update_var_def, venom_state_component_equality])
QED

Theorem abi_static_loop_header_state_frame:
  !base counter_addr len_word ss.
    (abi_static_loop_header_state base counter_addr len_word ss)
      with vs_vars := ss.vs_vars = ss
Proof
  simp[abi_static_loop_header_state_def, LET_THM, update_var_reset_vars]
QED

Theorem abi_static_loop_header_state_control[simp]:
  !base counter_addr len_word ss.
    (abi_static_loop_header_state base counter_addr len_word ss).vs_current_bb =
      ss.vs_current_bb /\
    (abi_static_loop_header_state base counter_addr len_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_static_loop_header_state_def, LET_THM, update_var_def]
QED

Theorem abi_static_loop_header_operand_frame:
  !base counter_addr len_word ss arg_op.
    arg_op <> Var (compiler_var_name base 1) /\
    arg_op <> Var (compiler_var_name base 2) /\
    arg_op <> Var (compiler_var_name base 3) ==>
    eval_operand arg_op (abi_static_loop_header_state base counter_addr len_word ss) =
      eval_operand arg_op ss
Proof
  simp[abi_static_loop_header_state_def, LET_THM, eval_operand_update_var_avoids]
QED

Theorem abi_static_loop_header_path:
  !ctx func id base labels len_op ss counter_addr len_word header_bb next_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_static_loop_header id base labels len_op /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME len_word /\
    len_op <> Var (compiler_var_name base 1) /\
    lookup_block
      (if w2n (mload (w2n counter_addr) ss) < w2n len_word then
         fresh_label_output "enc_dyn_body" (labels + 1)
       else fresh_label_output "enc_dyn_exit" (labels + 2)) func.fn_blocks = SOME next_bb /\
    phi_prefix_length next_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to
        (if w2n (mload (w2n counter_addr) ss) < w2n len_word then
           fresh_label_output "enc_dyn_body" (labels + 1)
         else fresh_label_output "enc_dyn_exit" (labels + 2))
        (abi_static_loop_header_state base counter_addr len_word ss))
Proof
  MAP_EVERY qx_gen_tac [`ctx`, `func`, `id`, `var_base`, `labels`, `len_op`, `ss`,
    `counter_addr`, `len_word`, `header_bb`, `next_bb`] >> strip_tac >>
  drule_all abi_static_loop_header_execution >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`,
    `abi_static_loop_header_state var_base counter_addr len_word ss`,
    `jump_to
      (if w2n (mload (w2n (counter_addr:bytes32)) ss) < w2n (len_word:bytes32) then
         fresh_label_output "enc_dyn_body" (labels + 1)
       else fresh_label_output "enc_dyn_exit" (labels + 2))
      (abi_static_loop_header_state var_base counter_addr len_word ss)`,
    `header_bb`, `next_bb`, `TAKE 3 (abi_static_loop_header id var_base labels len_op)`,
    `EL 3 (abi_static_loop_header id var_base labels len_op)`] fragment_path_block) >>
  impl_tac
  >- (simp[abi_static_loop_header_prefix_straight, abi_static_loop_header_terminator,
        jump_to_def] >>
      simp[abi_static_loop_header_def, mk_inst_def, is_terminator_def]) >> simp[]
QED
