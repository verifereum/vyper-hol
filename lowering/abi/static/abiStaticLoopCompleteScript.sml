(* TOP-LEVEL: from the initialized header, the actual array loop reaches
   its open exit with the exact memory image and returned size word.
   Helpers combine iteration and exit operand frames and SSA snapshots. *)
Theory abiStaticLoopComplete
Ancestors
  abiStaticLoopCode abiStaticLoopHeader abiStaticLoopBody abiStaticLoopExit
  abiStaticLoopIteration abiStaticLoopRun abiStaticLoopFinish
  fragBlockPath fragExec compileEnv exprLoweringProps instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words arithmetic

Definition abi_static_loop_tail_names_def:
  abi_static_loop_tail_names var_base info =
    abi_static_loop_iteration_names var_base info ++ abi_static_loop_exit_names var_base info
End

Definition abi_static_loop_names_def:
  abi_static_loop_names var_base info =
    compiler_var_name var_base 0 :: abi_static_loop_tail_names var_base info
End

Theorem abi_static_loop_finish_snapshot:
  !var_base labels counter_addr len_word src_addr info abi_sz ss vars saved_state.
    ss with vs_vars := vars = saved_state ==>
    (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss)
      with vs_vars := vars =
    (jump_to (fresh_label_output "enc_dyn_exit" (labels + 2)) saved_state) with vs_inst_idx := 3
Proof
  rpt gen_tac >> DISCH_TAC >> pop_assum (SUBST1_TAC o SYM) >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `len_word`, `src_addr`,
    `info`, `abi_sz`, `ss`] abi_static_loop_finish_frame) >>
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem abi_static_loop_complete_operand_frame:
  !var_base labels counter_addr len_word src_addr info abi_sz ss initial.
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (abi_static_loop_iteration_names var_base info) ==>
      eval_operand arg_op ss = eval_operand arg_op initial) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_tail_names var_base info) ==>
      eval_operand arg_op
        (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss) =
        eval_operand arg_op initial
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> DISCH_TAC >>
  `EVERY (\name. arg_op <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. arg_op <> Var name) (abi_static_loop_finish_names var_base info)` by
    fs[abi_static_loop_tail_names_def, abi_static_loop_finish_names_def,
      abi_static_loop_iteration_names_def] >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `len_word`, `src_addr`,
    `info`, `abi_sz`, `ss`, `arg_op`] abi_static_loop_finish_operand_frame) >> simp[]
QED

Theorem abi_static_loop_complete_path:
  !ctx func id var_base labels dst src info abi_sz mem_sz len_op ss
      dst_addr src_addr counter_addr n header_bb body_bb exit_bb.
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_static_loop_header id var_base labels len_op /\
    lookup_block (fresh_label_output "enc_dyn_body" (labels + 1)) func.fn_blocks = SOME body_bb /\
    body_bb.bb_instructions = abi_static_loop_body id var_base labels dst src info abi_sz mem_sz /\
    lookup_block (fresh_label_output "enc_dyn_exit" (labels + 2)) func.fn_blocks = SOME exit_bb /\
    isPREFIX (abi_static_loop_exit id var_base src info abi_sz) exit_bb.bb_instructions /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\ ss.vs_inst_idx = 0 /\
    ~ss.vs_halted /\ mload (w2n counter_addr) ss = 0w /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME (n2w n) /\ n < dimword(:256) /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_tail_names var_base info) ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = fresh_label_output "enc_dyn_exit" (labels + 2) /\
      out.vs_inst_idx = 3 /\ ~out.vs_halted /\
      eval_operand (Var (compiler_var_name var_base (14 + static_info_var_count info))) out =
        SOME (32w + mload (w2n src_addr)
          (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels)
            n ss) * n2w abi_sz) /\
      out with vs_vars := ss.vs_vars =
        (jump_to (fresh_label_output "enc_dyn_exit" (labels + 2))
          (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels)
            n ss)) with vs_inst_idx := 3 /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_tail_names var_base info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\name. src <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. dst <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. len_op <> Var name) (abi_static_loop_iteration_names var_base info)` by
    fs[abi_static_loop_tail_names_def, EVERY_CONJ] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `dst`, `src`, `info`,
    `abi_sz`, `mem_sz`, `len_op`, `ss`, `dst_addr`, `src_addr`, `counter_addr`,
    `n`, `header_bb`, `body_bb`] abi_static_loop_run) >>
  impl_tac >- fs[abi_static_loop_tail_names_def, EVERY_CONJ] >> strip_tac >>
  rename1 `fragment_path ctx func ss boundary` >> fs[abi_static_loop_run_inv_def] >>
  `eval_operand src boundary = SOME src_addr /\
   eval_operand len_op boundary = SOME (n2w n) /\
   eval_operand (Var (compiler_var_name var_base 0)) boundary = SOME counter_addr` by simp[] >>
  `fragment_path ctx func boundary
    (abi_static_loop_finish_state var_base labels counter_addr (n2w n) src_addr info abi_sz boundary)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `src`, `info`, `abi_sz`,
       `boundary`, `src_addr`, `counter_addr`, `len_op`, `n2w n:bytes32`, `header_bb`, `exit_bb`]
         abi_static_loop_finish_path) >> simp[] >>
     fs[abi_static_loop_tail_names_def, abi_static_loop_iteration_names_def, EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `n2w n:bytes32`, `src_addr`,
    `info`, `abi_sz`, `boundary`, `ss.vs_vars`,
    `FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels) n ss`]
      abi_static_loop_finish_snapshot) >> impl_tac >- simp[] >> DISCH_TAC >>
  `mload (w2n src_addr) boundary = mload (w2n src_addr)
    (FUNPOW (abi_static_loop_effect info dst_addr src_addr abi_sz mem_sz counter_addr labels) n ss)` by
    (qpat_x_assum `boundary with vs_vars := _ = _`
       (mp_tac o AP_TERM ``mload (w2n (src_addr:bytes32))``) >> simp[mload_reset_vars_eq]) >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `n2w n:bytes32`, `src_addr`,
    `info`, `abi_sz`, `boundary`, `ss`] abi_static_loop_complete_operand_frame) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `n2w n:bytes32`, `src_addr`,
    `info`, `abi_sz`, `boundary`] abi_static_loop_finish_value) >> DISCH_TAC >> fs[] >>
  qexists_tac `abi_static_loop_finish_state var_base labels counter_addr (n2w n) src_addr info abi_sz boundary` >>
  simp[] >> irule fragment_path_trans >> qexists_tac `boundary` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop completion theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopComplete")
