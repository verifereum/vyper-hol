(* TOP-LEVEL: a completed actual dynamic-child loop exits and returns its
   accumulated encoded size, preserving the entire memory image. *)
Theory abiDynamicLoopFinish
Ancestors
  abiDynamicLoopCode abiDynamicLoopFactor abiDynamicLoopStructure abiDynamicLoopHeader
  abiDynamicLoopStep abiDynamicLoopExit abiDynamicLoopUpdate abiChildCode abiStaticLoopCode abiBytestringCode
  abiStaticLoopBody ssaOperandFrame compileEnv fragExec fragBlockPath instIdxIndep
  venomState venomExecSemantics list words arithmetic

Definition abi_dynamic_loop_finish_state_def:
  abi_dynamic_loop_finish_state next_var var_base labels src_addr counter_addr dyn_addr len_word ss =
    (abi_dynamic_loop_exit_state (next_var + 2) src_addr dyn_addr
      (jump_to (fresh_label_output "enc_dyn_exit" (labels + 2))
        (abi_dynamic_loop_header_state var_base counter_addr len_word ss))) with vs_inst_idx := 3
End

Theorem abi_dynamic_loop_exit_memory:
  !var_base src_addr dyn_addr ss.
    (abi_dynamic_loop_exit_state var_base src_addr dyn_addr ss).vs_memory = ss.vs_memory
Proof
  simp_tac (pure_ss ++ boolSimps.BOOL_ss ++ rewrites
    [venom_state_accfupds, combinTheory.K_THM]) [abi_dynamic_loop_exit_state_def, update_var_def]
QED

Theorem abi_dynamic_loop_finish_values:
  !next_var var_base labels src_addr counter_addr dyn_addr len_word ss.
    let out = abi_dynamic_loop_finish_state next_var var_base labels src_addr counter_addr dyn_addr len_word ss in
    out.vs_current_bb = fresh_label_output "enc_dyn_exit" (labels + 2) /\ out.vs_inst_idx = 3 /\
    out.vs_halted = ss.vs_halted /\ out.vs_memory = ss.vs_memory /\
    eval_operand (Var (compiler_var_name (next_var + 2) 2)) out = SOME (32w + mload (w2n dyn_addr) ss)
Proof
  simp[abi_dynamic_loop_finish_state_def, LET_THM, abi_dynamic_loop_exit_value, eval_op_inst_idx,
    abi_dynamic_loop_exit_frame, abi_dynamic_loop_exit_memory,
    abi_dynamic_loop_header_frame, abi_dynamic_loop_phase_frames, jump_to_def, mload_def]
QED

Theorem abi_dynamic_loop_finish_operand_frame:
  !next_var var_base labels src_addr counter_addr dyn_addr len_word ss arg_op.
    arg_op <> Var (compiler_var_name var_base 3) /\ arg_op <> Var (compiler_var_name var_base 4) /\
    arg_op <> Var (compiler_var_name var_base 5) /\
    EVERY (\name. arg_op <> Var name) (compiler_var_names (next_var + 2) 3) ==>
    eval_operand arg_op
      (abi_dynamic_loop_finish_state next_var var_base labels src_addr counter_addr dyn_addr len_word ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >>
  fs[compiler_var_names_def, GENLIST, compiler_var_name_def] >>
  simp[abi_dynamic_loop_finish_state_def, eval_op_inst_idx, abi_dynamic_loop_exit_operand_frame,
    eval_operand_jump_to_eq, abi_dynamic_loop_header_operand_frame, compiler_var_name_def]
QED

Theorem abi_dynamic_loop_finish_path:
  !ctx func dst src info abi_sz mem_sz len_op cs op cs' child_len mid ss src_addr counter_addr dyn_addr len_word.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) ss = SOME dyn_addr /\
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name cs.cs_next_var 3) /\
    ~(w2n (mload (w2n counter_addr) ss) < w2n len_word) /\
    src <> Var (compiler_var_name cs.cs_next_var 3) /\ src <> Var (compiler_var_name cs.cs_next_var 4) /\
    src <> Var (compiler_var_name cs.cs_next_var 5) ==>
    fragment_path ctx func ss
      (abi_dynamic_loop_finish_state mid.cs_next_var cs.cs_next_var cs.cs_next_label
        src_addr counter_addr dyn_addr len_word ss)
Proof
  rpt gen_tac >> strip_tac >>
  `cs' = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
    (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
    (abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
      (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
        (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid))` by
    fs[compile_abi_dynamic_loop_factor, LET_THM] >>
  gvs[] >> drule_all abi_dynamic_loop_contains_parts >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_dynamic_loop_child_next_var >> DISCH_TAC >>
  drule_all abi_dynamic_loop_contains_prefix >> strip_tac >>
  drule_all abi_dynamic_loop_contains_exit >> strip_tac >>
  drule (List.nth (CONJUNCTS abi_dynamic_loop_no_phi, 2)) >> DISCH_TAC >>
  qabbrev_tac `at_exit = jump_to (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
    (abi_dynamic_loop_header_state cs.cs_next_var counter_addr len_word ss)` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_id`, `cs.cs_next_var`, `cs.cs_next_label`, `len_op`,
    `ss`, `counter_addr`, `len_word`,
    `<|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
       bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|>`,
    `exit_bb`] abi_dynamic_loop_header_path) >>
  impl_tac >- simp[] >> asm_simp_tac (srw_ss()) [] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `mid.cs_next_id + 6`, `mid.cs_next_var + 2`, `src`,
    `Var (compiler_var_name cs.cs_next_var 1)`, `at_exit`, `src_addr`, `dyn_addr`, `exit_bb`]
    abi_dynamic_loop_exit_path) >>
  impl_tac
  >- fs[Abbr`at_exit`, jump_to_def, eval_operand_jump_to_eq, abi_dynamic_loop_header_operand_frame,
       abi_dynamic_loop_latch_cut_def, abi_child_suffix_cut_def, abi_dynamic_loop_saved_name,
       compiler_var_name_def] >> DISCH_TAC >>
  simp_tac bool_ss [abi_dynamic_loop_finish_state_def] >>
  irule fragment_path_trans >> qexists_tac `at_exit` >> fs[Abbr`at_exit`]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic ABI loop completion: " ^ name)
  end) (DB.thms "abiDynamicLoopFinish")
