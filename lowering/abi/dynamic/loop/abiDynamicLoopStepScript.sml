(* TOP-LEVEL: the actual loop header and address prefix reach the recursive
   child with its source, head, tail and saved loop operands intact. *)
Theory abiDynamicLoopStep
Ancestors
  abiDynamicLoopCode abiDynamicLoopStructure abiDynamicLoopHeader abiDynamicLoopBody
  abiStaticLoopCode abiStaticLoopHeader abiStaticLoopBody abiBytestringCode ssaOperandFrame
  abiEncoderPathProps compileEnv fragExec fragBlockPath instIdxIndep venomState venomExecSemantics
  list words arithmetic

Definition abi_dynamic_loop_child_state_def:
  abi_dynamic_loop_child_state var_base labels dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr len_word ss =
    (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr
      (jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
        (abi_dynamic_loop_header_state var_base counter_addr len_word ss))) with vs_inst_idx := 9
End

Theorem abi_dynamic_loop_input_names:
  !var_base dst src.
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (var_base + 3) 12) ==>
    src <> Var (compiler_var_name var_base 3) /\ src <> Var (compiler_var_name var_base 4) /\
    src <> Var (compiler_var_name var_base 5) /\ dst <> Var (compiler_var_name var_base 3) /\
    dst <> Var (compiler_var_name var_base 4) /\ dst <> Var (compiler_var_name var_base 5) /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (var_base + 6) 9)
Proof
  simp[compiler_var_names_def, GENLIST, compiler_var_name_def]
QED

Theorem abi_dynamic_loop_phase_frames:
  (!var_base counter_addr len_word ss.
    (abi_dynamic_loop_header_state var_base counter_addr len_word ss).vs_memory = ss.vs_memory) /\
  (!var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss.
    (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss).vs_memory =
      ss.vs_memory /\
    (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss).vs_current_bb =
      ss.vs_current_bb /\
    (abi_dynamic_loop_body_state var_base dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr ss).vs_halted =
      ss.vs_halted)
Proof
  simp_tac (pure_ss ++ boolSimps.BOOL_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM, LET_THM])
    [abi_dynamic_loop_body_state_def, abi_dynamic_loop_header_state_def,
     abi_static_loop_header_state_def, update_var_def]
QED

Theorem abi_dynamic_loop_child_state_values:
  !var_base labels dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr len_word ss.
    let boundary = abi_dynamic_loop_child_state var_base labels dst_addr src_addr abi_sz mem_sz
      counter_addr dyn_addr len_word ss in
    boundary.vs_current_bb = fresh_label_output "enc_dyn_body" (labels + 1) /\
    boundary.vs_inst_idx = 9 /\ boundary.vs_halted = ss.vs_halted /\
    boundary.vs_memory = ss.vs_memory /\
    eval_operand (Var (compiler_var_name var_base 6)) boundary = SOME (mload (w2n counter_addr) ss) /\
    eval_operand (Var (compiler_var_name var_base 9)) boundary =
      SOME (src_addr + 32w + mload (w2n counter_addr) ss * n2w mem_sz) /\
    eval_operand (Var (compiler_var_name var_base 12)) boundary =
      SOME (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) /\
    eval_operand (Var (compiler_var_name var_base 13)) boundary = SOME (mload (w2n dyn_addr) ss) /\
    eval_operand (Var (compiler_var_name var_base 14)) boundary = SOME (dst_addr + 32w + mload (w2n dyn_addr) ss)
Proof
  simp[abi_dynamic_loop_child_state_def, LET_THM,
    SIMP_RULE bool_ss [LET_THM] abi_dynamic_loop_body_values, eval_op_inst_idx,
    abi_dynamic_loop_phase_frames, abi_dynamic_loop_header_frame, jump_to_def, mload_def]
QED

Theorem abi_dynamic_loop_child_state_operand_frame:
  !var_base labels dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr len_word ss arg_op.
    EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 3) 12) ==>
    eval_operand arg_op
      (abi_dynamic_loop_child_state var_base labels dst_addr src_addr abi_sz mem_sz counter_addr dyn_addr len_word ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`var_base`, `arg_op`, `arg_op`] abi_dynamic_loop_input_names) >>
  simp[abi_dynamic_loop_child_state_def, eval_op_inst_idx, abi_dynamic_loop_body_operand_frame,
    abi_dynamic_loop_header_operand_frame, eval_operand_jump_to_eq]
QED

Theorem abi_dynamic_loop_header_body_path:
  !ctx func dst src abi_sz mem_sz len_op cs ss dst_addr src_addr counter_addr dyn_addr len_word.
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) func /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) ss = SOME dyn_addr /\
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name cs.cs_next_var 3) /\
    w2n (mload (w2n counter_addr) ss) < w2n len_word /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12) ==>
    fragment_path ctx func ss
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr src_addr abi_sz mem_sz
        counter_addr dyn_addr len_word ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_dynamic_loop_contains_prefix >> strip_tac >>
  drule (List.nth (CONJUNCTS abi_dynamic_loop_no_phi, 1)) >> DISCH_TAC >>
  drule_all abi_dynamic_loop_input_names >> strip_tac >>
  qabbrev_tac `at_body = jump_to (fresh_label_output "enc_dyn_body" (cs.cs_next_label + 1))
    (abi_dynamic_loop_header_state cs.cs_next_var counter_addr len_word ss)` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `len_op`,
    `ss`, `counter_addr`, `len_word`,
    `<|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
       bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|>`,
    `body_bb`] abi_dynamic_loop_header_path) >>
  impl_tac >- simp[abi_dynamic_loop_no_phi] >> asm_simp_tac (srw_ss()) [] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `dst`, `src`, `abi_sz`, `mem_sz`,
    `at_body`, `dst_addr`, `src_addr`, `counter_addr`, `dyn_addr`, `body_bb`] abi_dynamic_loop_body_path) >>
  impl_tac
  >- simp[Abbr`at_body`, eval_operand_jump_to_eq, abi_dynamic_loop_header_operand_frame,
       compiler_var_name_def, jump_to_def] >> DISCH_TAC >>
  simp_tac bool_ss [abi_dynamic_loop_child_state_def] >>
  irule fragment_path_trans >> qexists_tac `at_body` >> fs[Abbr`at_body`]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop child entry: " ^ name)
  end) (DB.thms "abiDynamicLoopStep")
