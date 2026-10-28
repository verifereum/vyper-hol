(* TOP-LEVEL: the actual dynamic-child loop header branches on its index
   and saved length. Its register state reuses the established loop header. *)
Theory abiDynamicLoopHeader
Ancestors
  abiDynamicLoopCode abiStaticLoopHeader abiStaticLoopCode ssaOperandFrame
  compileEnv exprLoweringProps emitHelperProps fragExec fragBlockPath
  venomExecSemantics venomState venomInst venomMemProps list words arithmetic
Libs wordsLib

Definition abi_dynamic_loop_header_state_def:
  abi_dynamic_loop_header_state var_base counter_addr len_word ss =
    abi_static_loop_header_state (var_base + 2) counter_addr len_word ss
End

val dynamic_header_steps = List.filter (fn th =>
  let val guard = #1 (dest_imp (#2 (strip_forall (concl th))))
  in List.exists (fn opc => aconv (rhs guard) opc) [``MLOAD``, ``LT``, ``ISZERO``, ``JNZ``]
  end) (CONJUNCTS step_inst_base_opcode_eqs);

Theorem abi_dynamic_loop_header_straight:
  !id var_base labels len_op.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 3 (abi_dynamic_loop_header id var_base labels len_op))
Proof
  simp[abi_dynamic_loop_header_def, mk_inst_def, is_terminator_def]
QED

Theorem abi_dynamic_loop_header_execution:
  !id var_base labels len_op ss counter_addr len_word.
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name var_base 3) ==>
    run_inst_seq (TAKE 3 (abi_dynamic_loop_header id var_base labels len_op)) ss =
      OK (abi_dynamic_loop_header_state var_base counter_addr len_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `w2n (mload (w2n counter_addr) ss) < w2n len_word` >>
  asm_simp_tac (srw_ss()) (dynamic_header_steps @
    [abi_dynamic_loop_header_def, abi_dynamic_loop_header_state_def, abi_static_loop_header_state_def,
     compiler_var_name_add, run_inst_seq_def, mk_inst_def, exec_read1_def, exec_pure1_def, exec_pure2_def,
     eval_operand_update_var_avoids, eval_operand_update_var, mload_update_var, bool_to_word_def, LET_THM])
QED

Theorem abi_dynamic_loop_header_terminator:
  !id var_base labels len_op ss counter_addr len_word.
    step_inst_base (EL 3 (abi_dynamic_loop_header id var_base labels len_op))
      ((abi_dynamic_loop_header_state var_base counter_addr len_word ss) with vs_inst_idx := 3) =
    OK (jump_to
      (if w2n (mload (w2n counter_addr) ss) < w2n len_word then
        fresh_label_output "enc_dyn_body" (labels + 1)
       else fresh_label_output "enc_dyn_exit" (labels + 2))
      (abi_dynamic_loop_header_state var_base counter_addr len_word ss))
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`id + 3`, `var_base + 2`, `labels`, `len_op`, `ss`, `counter_addr`, `len_word`]
    abi_static_loop_header_terminator) >>
  simp[abi_dynamic_loop_header_def, abi_static_loop_header_def,
    abi_dynamic_loop_header_state_def, compiler_var_name_add]
QED

Theorem abi_dynamic_loop_header_frame:
  !var_base counter_addr len_word ss.
    (abi_dynamic_loop_header_state var_base counter_addr len_word ss) with vs_vars := ss.vs_vars = ss /\
    (abi_dynamic_loop_header_state var_base counter_addr len_word ss).vs_current_bb = ss.vs_current_bb /\
    (abi_dynamic_loop_header_state var_base counter_addr len_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_dynamic_loop_header_state_def, abi_static_loop_header_state_frame]
QED

Theorem abi_dynamic_loop_header_operand_frame:
  !var_base counter_addr len_word ss arg_op.
    arg_op <> Var (compiler_var_name var_base 3) /\ arg_op <> Var (compiler_var_name var_base 4) /\
    arg_op <> Var (compiler_var_name var_base 5) ==>
    eval_operand arg_op (abi_dynamic_loop_header_state var_base counter_addr len_word ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[abi_dynamic_loop_header_state_def] >>
  irule abi_static_loop_header_operand_frame >> fs[compiler_var_name_add]
QED

Theorem abi_dynamic_loop_header_path:
  !ctx func id var_base labels len_op ss counter_addr len_word header_bb next_bb.
    lookup_block ss.vs_current_bb func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_dynamic_loop_header id var_base labels len_op /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name var_base 3) /\
    lookup_block (if w2n (mload (w2n counter_addr) ss) < w2n len_word then
      fresh_label_output "enc_dyn_body" (labels + 1) else fresh_label_output "enc_dyn_exit" (labels + 2))
      func.fn_blocks = SOME next_bb /\ phi_prefix_length next_bb.bb_instructions = 0 ==>
    fragment_path ctx func ss
      (jump_to (if w2n (mload (w2n counter_addr) ss) < w2n len_word then
        fresh_label_output "enc_dyn_body" (labels + 1) else fresh_label_output "enc_dyn_exit" (labels + 2))
        (abi_dynamic_loop_header_state var_base counter_addr len_word ss))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`id`, `var_base`, `labels`, `len_op`, `ss`, `counter_addr`, `len_word`]
    abi_dynamic_loop_header_execution) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ss`, `abi_dynamic_loop_header_state var_base counter_addr len_word ss`,
    `jump_to (if w2n (mload (w2n (counter_addr:bytes32)) ss) < w2n (len_word:bytes32) then
       fresh_label_output "enc_dyn_body" (labels + 1) else fresh_label_output "enc_dyn_exit" (labels + 2))
      (abi_dynamic_loop_header_state var_base counter_addr len_word ss)`,
    `header_bb`, `next_bb`, `TAKE 3 (abi_dynamic_loop_header id var_base labels len_op)`,
    `EL 3 (abi_dynamic_loop_header id var_base labels len_op)`] fragment_path_block) >>
  impl_tac
  >- (simp[abi_dynamic_loop_header_straight, abi_dynamic_loop_header_terminator,
        abi_dynamic_loop_header_frame, jump_to_def] >>
      simp[abi_dynamic_loop_header_def, mk_inst_def, is_terminator_def]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-child ABI loop header execution: " ^ name)
  end) (DB.thms "abiDynamicLoopHeader")
