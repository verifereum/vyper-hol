(* TOP-LEVEL: composition of the actual header and body into one array-loop
   iteration, with exact memory effect, incremented counter and preserved
   input operands. Helpers transport frames through the two jumps. *)
Theory abiStaticLoopIteration
Ancestors
  abiStaticLoopCode abiStaticLoopCodeProps abiStaticLoopHeader abiStaticLoopBody
  fragBlockPath fragExec compileEnv exprLoweringProps ssaOperandFrame
  venomExecSemantics venomState venomInst list rich_list words

Definition abi_static_loop_iteration_names_def:
  abi_static_loop_iteration_names var_base info =
    [compiler_var_name var_base 1; compiler_var_name var_base 2;
     compiler_var_name var_base 3] ++ abi_static_loop_body_names var_base info
End

Definition abi_static_loop_enter_body_def:
  abi_static_loop_enter_body var_base labels counter_addr len_word ss =
    jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
      (abi_static_loop_header_state var_base counter_addr len_word ss)
End

Theorem abi_static_loop_counter_avoids[simp]:
  !var_base info.
    EVERY (\name. Var (compiler_var_name var_base 0) <> Var name)
      (abi_static_loop_iteration_names var_base info)
Proof
  rpt gen_tac >> Cases_on `info` >>
  simp[abi_static_loop_iteration_names_def, abi_static_loop_body_names_def]
QED

Theorem abi_static_loop_enter_body_control[simp]:
  !var_base labels counter_addr len_word ss.
    (abi_static_loop_enter_body var_base labels counter_addr len_word ss).vs_current_bb =
      fresh_label_output "enc_dyn_body" (labels + 1) /\
    (abi_static_loop_enter_body var_base labels counter_addr len_word ss).vs_inst_idx = 0 /\
    (abi_static_loop_enter_body var_base labels counter_addr len_word ss).vs_halted = ss.vs_halted
Proof
  simp[abi_static_loop_enter_body_def, jump_to_def]
QED

Theorem abi_static_loop_enter_operand_frame:
  !var_base labels counter_addr len_word ss info arg_op.
    EVERY (\name. arg_op <> Var name) (abi_static_loop_iteration_names var_base info) ==>
    eval_operand arg_op (abi_static_loop_enter_body var_base labels counter_addr len_word ss) =
      eval_operand arg_op ss
Proof
  rpt gen_tac >> simp[abi_static_loop_iteration_names_def] >> strip_tac >>
  simp[abi_static_loop_enter_body_def, eval_operand_jump_to_eq] >>
  irule abi_static_loop_header_operand_frame >> simp[]
QED

Theorem abi_static_loop_enter_reset_vars:
  !var_base labels counter_addr len_word ss.
    (abi_static_loop_enter_body var_base labels counter_addr len_word ss)
      with vs_vars := ss.vs_vars =
    jump_to (fresh_label_output "enc_dyn_body" (labels + 1)) ss
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`var_base`, `counter_addr`, `len_word`, `ss`]
    abi_static_loop_header_state_frame) >>
  disch_then (mp_tac o AP_TERM ``\s:venom_state.
    jump_to (fresh_label_output "enc_dyn_body" (labels + 1)) s``) >>
  simp[abi_static_loop_enter_body_def, jump_to_def]
QED

Theorem jump_to_reset_vars_eq:
  !label ss vars.
    jump_to label (ss with vs_vars := vars) = (jump_to label ss) with vs_vars := vars
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem abi_static_loop_iteration_memory_frame:
  !info dst_addr src_addr abi_sz mem_sz counter_addr var_base labels len_word ss out.
    out with vs_vars :=
      (abi_static_loop_enter_body var_base labels counter_addr len_word ss).vs_vars =
    jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr
        (abi_static_loop_enter_body var_base labels counter_addr len_word ss)) ==>
    out with vs_vars := ss.vs_vars =
    jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
        (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss))
Proof
  rpt gen_tac >> DISCH_TAC >>
  `((abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr
       (abi_static_loop_enter_body var_base labels counter_addr len_word ss))
       with vs_vars := ss.vs_vars) =
    jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
      (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss)` by
    (mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `len_word`, `ss`]
       abi_static_loop_enter_reset_vars) >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state.
       abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr s``) >>
     simp[abi_static_loop_body_memory_reset_vars, abi_static_loop_body_memory_jump_to]) >>
  qpat_x_assum `out with vs_vars := _ = _`
    (mp_tac o AP_TERM ``\s:venom_state. s with vs_vars := ss.vs_vars``) >>
  simp[GSYM jump_to_reset_vars_eq]
QED

Theorem abi_static_loop_iteration_counter:
  !info dst_addr src_addr abi_sz mem_sz counter_addr labels ss out.
    out with vs_vars := ss.vs_vars =
    jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
        (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss)) ==>
    mload (w2n counter_addr) out = mload (w2n counter_addr) ss + 1w
Proof
  rpt gen_tac >>
  disch_then (mp_tac o AP_TERM ``mload (w2n (counter_addr:bytes32))``) >>
  simp[mload_reset_vars_eq, memory_reads_jump_to, abi_static_loop_body_memory_counter]
QED

Theorem abi_static_loop_iteration_operand_frame:
  !var_base labels counter_addr len_word ss info out.
    (!arg_op. EVERY (\name. arg_op <> Var name) (abi_static_loop_body_names var_base info) ==>
      eval_operand arg_op out =
        eval_operand arg_op (abi_static_loop_enter_body var_base labels counter_addr len_word ss)) ==>
    !arg_op. EVERY (\name. arg_op <> Var name)
      (abi_static_loop_iteration_names var_base info) ==>
      eval_operand arg_op out = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> DISCH_TAC >>
  `EVERY (\name. arg_op <> Var name) (abi_static_loop_body_names var_base info)` by
    fs[abi_static_loop_iteration_names_def] >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `len_word`, `ss`, `info`, `arg_op`]
    abi_static_loop_enter_operand_frame) >> impl_tac >- simp[] >> DISCH_TAC >>
  qpat_x_assum `!arg_op. EVERY _ (abi_static_loop_body_names _ _) ==> _`
    (qspec_then `arg_op` mp_tac) >> simp[]
QED

Theorem abi_static_loop_iteration_path:
  !ctx func id var_base labels dst src info abi_sz mem_sz ss dst_addr src_addr
      counter_addr len_op len_word header_bb body_bb.
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    header_bb.bb_instructions = abi_static_loop_header id var_base labels len_op /\
    lookup_block (fresh_label_output "enc_dyn_body" (labels + 1)) func.fn_blocks = SOME body_bb /\
    body_bb.bb_instructions = abi_static_loop_body id var_base labels dst src info abi_sz mem_sz /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\ ss.vs_inst_idx = 0 /\
    ~ss.vs_halted /\ eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME src_addr /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME len_word /\
    w2n (mload (w2n counter_addr) ss) < w2n len_word /\
    EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
      (abi_static_loop_iteration_names var_base info) ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\ out.vs_inst_idx = 0 /\
      ~out.vs_halted /\ mload (w2n counter_addr) out = mload (w2n counter_addr) ss + 1w /\
      out with vs_vars := ss.vs_vars =
        jump_to (fresh_label_output "enc_dyn_hdr" labels)
          (jump_to (fresh_label_output "enc_dyn_body" (labels + 1))
            (abi_static_loop_body_memory info dst_addr src_addr abi_sz mem_sz counter_addr ss)) /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (abi_static_loop_iteration_names var_base info) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\name. src <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. dst <> Var name) (abi_static_loop_iteration_names var_base info) /\
   EVERY (\name. len_op <> Var name) (abi_static_loop_iteration_names var_base info)` by
    fs[EVERY_CONJ] >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `len_word`, `ss`, `info`]
    abi_static_loop_enter_operand_frame) >> DISCH_TAC >>
  `fragment_path ctx func ss
    (abi_static_loop_enter_body var_base labels counter_addr len_word ss)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `len_op`, `ss`,
       `counter_addr`, `len_word`, `header_bb`, `body_bb`] abi_static_loop_header_path) >>
     fs[abi_static_loop_enter_body_def, abi_static_loop_blocks_no_phi,
       abi_static_loop_iteration_names_def, EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `id`, `var_base`, `labels`, `dst`, `src`, `info`,
    `abi_sz`, `mem_sz`, `abi_static_loop_enter_body var_base labels counter_addr len_word ss`,
    `dst_addr`, `src_addr`, `counter_addr`, `body_bb`, `header_bb`] abi_static_loop_body_path) >>
  impl_tac
  >- (simp[abi_static_loop_blocks_no_phi] >>
      fs[abi_static_loop_iteration_names_def, EVERY_CONJ]) >> strip_tac >>
  rename1 `fragment_path ctx func _ out` >>
  mp_tac (Q.SPECL [`info`, `dst_addr`, `src_addr`, `abi_sz`, `mem_sz`, `counter_addr`,
    `var_base`, `labels`, `len_word`, `ss`, `out`] abi_static_loop_iteration_memory_frame) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  drule_all abi_static_loop_iteration_counter >> DISCH_TAC >>
  mp_tac (Q.SPECL [`var_base`, `labels`, `counter_addr`, `len_word`, `ss`, `info`, `out`]
    abi_static_loop_iteration_operand_frame) >> impl_tac >- simp[] >> DISCH_TAC >>
  qexists_tac `out` >> simp[] >> irule fragment_path_trans >>
  qexists_tac `abi_static_loop_enter_body var_base labels counter_addr len_word ss` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI static-loop iteration theorem: " ^ name)
  end)
  (DB.thms "abiStaticLoopIteration")
