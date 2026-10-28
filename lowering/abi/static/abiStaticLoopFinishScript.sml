(* TOP-LEVEL: a completed array loop takes its actual header's exit edge,
   executes the size calculation, and stops at the compiler's open cut.
   Memory is unchanged during this final header/exit path. *)
Theory abiStaticLoopFinish
Ancestors
  abiStaticLoopCode abiStaticLoopCodeProps abiStaticLoopHeader abiStaticLoopBody
  abiStaticLoopExit abiStaticLoopIteration ssaOperandFrame
  fragBlockPath fragExec compileEnv exprLoweringProps instIdxIndep
  venomExecSemantics venomState venomInst list rich_list words

Definition abi_static_loop_enter_exit_def:
  abi_static_loop_enter_exit var_base labels counter_addr len_word ss =
    jump_to (fresh_label_output "enc_dyn_exit" (labels + 2))
      (abi_static_loop_header_state var_base counter_addr len_word ss)
End

Definition abi_static_loop_finish_state_def:
  abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss =
    (abi_static_loop_exit_state var_base src_addr info abi_sz
      (abi_static_loop_enter_exit var_base labels counter_addr len_word ss))
      with vs_inst_idx := 3
End

Definition abi_static_loop_finish_names_def:
  abi_static_loop_finish_names var_base info =
    [compiler_var_name var_base 1; compiler_var_name var_base 2;
     compiler_var_name var_base 3] ++ abi_static_loop_exit_names var_base info
End

val finish_projection_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [venom_state_accfupds, combinTheory.K_THM, LET_THM];

Theorem abi_static_loop_finish_control[simp]:
  !var_base labels counter_addr len_word src_addr info abi_sz ss.
    (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss).
      vs_current_bb = fresh_label_output "enc_dyn_exit" (labels + 2) /\
    (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss).
      vs_inst_idx = 3 /\
    (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss).
      vs_halted = ss.vs_halted
Proof
  simp_tac finish_projection_ss
    [abi_static_loop_finish_state_def, abi_static_loop_exit_state_def,
     abi_static_loop_enter_exit_def, abi_static_loop_header_state_def, update_var_def, jump_to_def]
QED

Theorem abi_static_loop_enter_exit_control[simp]:
  !var_base labels counter_addr len_word ss.
    (abi_static_loop_enter_exit var_base labels counter_addr len_word ss).vs_current_bb =
      fresh_label_output "enc_dyn_exit" (labels + 2) /\
    (abi_static_loop_enter_exit var_base labels counter_addr len_word ss).vs_inst_idx = 0 /\
    (abi_static_loop_enter_exit var_base labels counter_addr len_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_static_loop_enter_exit_def, jump_to_def]
QED

Theorem abi_static_loop_enter_exit_operand:
  !var_base labels counter_addr len_word ss arg_op.
    arg_op <> Var (compiler_var_name var_base 1) /\
    arg_op <> Var (compiler_var_name var_base 2) /\
    arg_op <> Var (compiler_var_name var_base 3) ==>
    eval_operand arg_op (abi_static_loop_enter_exit var_base labels counter_addr len_word ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> strip_tac >>
  simp[abi_static_loop_enter_exit_def, eval_operand_jump_to_eq] >>
  irule abi_static_loop_header_operand_frame >> simp[]
QED

Theorem abi_static_loop_enter_exit_mload:
  !offset var_base labels counter_addr len_word ss.
    mload offset (abi_static_loop_enter_exit var_base labels counter_addr len_word ss) =
      mload offset ss
Proof
  simp[abi_static_loop_enter_exit_def, memory_reads_jump_to,
    abi_static_loop_header_state_def, LET_THM, mload_update_var]
QED

Theorem abi_static_loop_enter_exit_frame:
  !var_base labels counter_addr len_word ss.
    (abi_static_loop_enter_exit var_base labels counter_addr len_word ss)
      with vs_vars := ss.vs_vars =
    jump_to (fresh_label_output "enc_dyn_exit" (labels + 2)) ss
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`var_base`, `counter_addr`, `len_word`, `ss`]
    abi_static_loop_header_state_frame) >>
  disch_then (mp_tac o AP_TERM ``\s:venom_state.
    jump_to (fresh_label_output "enc_dyn_exit" (labels + 2)) s``) >>
  simp[abi_static_loop_enter_exit_def, jump_to_def]
QED

Theorem abi_static_loop_finish_frame:
  !var_base labels counter_addr len_word src_addr info abi_sz ss.
    (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss)
      with vs_vars := ss.vs_vars =
    (jump_to (fresh_label_output "enc_dyn_exit" (labels + 2)) ss) with vs_inst_idx := 3
Proof
  simp_tac finish_projection_ss
    [abi_static_loop_finish_state_def, abi_static_loop_exit_state_def,
     abi_static_loop_enter_exit_def, abi_static_loop_header_state_def,
     update_var_def, jump_to_def, venom_state_component_equality]
QED

Theorem abi_static_loop_finish_value:
  !var_base labels counter_addr len_word src_addr info abi_sz ss.
    eval_operand (Var (compiler_var_name var_base (14 + static_info_var_count info)))
      (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss) =
      SOME (32w + mload (w2n src_addr) ss * n2w abi_sz)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`var_base`, `src_addr`, `info`, `abi_sz`,
    `abi_static_loop_enter_exit var_base labels counter_addr len_word ss`]
      abi_static_loop_exit_value) >>
  simp[abi_static_loop_finish_state_def, eval_op_inst_idx,
    abi_static_loop_enter_exit_mload]
QED

Theorem abi_static_loop_finish_operand_frame:
  !var_base labels counter_addr len_word src_addr info abi_sz ss arg_op.
    EVERY (\name. arg_op <> Var name) (abi_static_loop_finish_names var_base info) ==>
    eval_operand arg_op
      (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> simp[abi_static_loop_finish_names_def] >> strip_tac >>
  simp[abi_static_loop_finish_state_def, eval_op_inst_idx,
    abi_static_loop_exit_operand_frame, abi_static_loop_enter_exit_operand]
QED

Theorem abi_static_loop_finish_path:
  !ctx func id var_base labels src info abi_sz ss src_addr counter_addr
      len_op len_word header_bb exit_bb.
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_static_loop_header id var_base labels len_op /\
    lookup_block (fresh_label_output "enc_dyn_exit" (labels + 2)) func.fn_blocks = SOME exit_bb /\
    isPREFIX (abi_static_loop_exit id var_base src info abi_sz) exit_bb.bb_instructions /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\ ss.vs_inst_idx = 0 /\
    ~ss.vs_halted /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME len_word /\
    ~(w2n (mload (w2n counter_addr) ss) < w2n len_word) /\
    len_op <> Var (compiler_var_name var_base 1) /\
    src <> Var (compiler_var_name var_base 1) /\
    src <> Var (compiler_var_name var_base 2) /\
    src <> Var (compiler_var_name var_base 3) ==>
    fragment_path ctx func ss
      (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_static_loop_exit_no_phi >> DISCH_TAC >>
  `fragment_path ctx func ss
    (abi_static_loop_enter_exit var_base labels counter_addr len_word ss)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `len_op`, `ss`,
       `counter_addr`, `len_word`, `header_bb`, `exit_bb`] abi_static_loop_header_path) >>
     simp[abi_static_loop_enter_exit_def, abi_static_loop_exit_no_phi]) >>
  `eval_operand src (abi_static_loop_enter_exit var_base labels counter_addr len_word ss) =
    SOME src_addr` by simp[abi_static_loop_enter_exit_operand] >>
  `fragment_path ctx func
    (abi_static_loop_enter_exit var_base labels counter_addr len_word ss)
    (abi_static_loop_finish_state var_base labels counter_addr len_word src_addr info abi_sz ss)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `src`, `info`, `abi_sz`,
       `abi_static_loop_enter_exit var_base labels counter_addr len_word ss`, `src_addr`, `exit_bb`]
         abi_static_loop_exit_path) >> simp[abi_static_loop_finish_state_def]) >>
  irule fragment_path_trans >>
  qexists_tac `abi_static_loop_enter_exit var_base labels counter_addr len_word ss` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop finish theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopFinish")
