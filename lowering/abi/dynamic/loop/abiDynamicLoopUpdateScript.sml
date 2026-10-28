(* TOP-LEVEL: after a recursive child returns, the actual head/tail suffix
   and index latch reach the outer header, including children with blocks. *)
Theory abiDynamicLoopUpdate
Ancestors
  abiDynamicLoopCode abiDynamicLoopStructure abiDynamicLoopLatch
  abiChildCode abiChildSuffix abiChildFrames abiChildMemoryFrame abiStaticLoopCode
  abiMemoryFrame memoryReadProps memoryValueAbiExec abiEncoderPathProps
  compileEnv fragExec fragBlockPath instIdxIndep venomState list rich_list words arithmetic

Definition abi_dynamic_loop_update_state_def:
  abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss =
    abi_dynamic_loop_latch_state (mid.cs_next_var + 1) counter_addr index
      ((abi_child_suffix_state mid.cs_next_var head_addr dyn_addr tail_offset child_size ss)
        with vs_inst_idx := LENGTH mid.cs_current_insts + 3)
End

Theorem abi_dynamic_loop_saved_name:
  !var_base next_var index new_index.
    var_base + 15 <= next_var /\ index < 15 ==>
    Var (compiler_var_name var_base index) <> Var (compiler_var_name next_var new_index)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [compiler_var_name_def] >> decide_tac
QED

Theorem abi_dynamic_loop_update_frame:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss.
    abi_memory_frame [(w2n head_addr,32);(w2n dyn_addr,32);(w2n counter_addr,32)] ss
      (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss)
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`[(w2n (head_addr:bytes32),32);(w2n (dyn_addr:bytes32),32)]`,
    `[(w2n (counter_addr:bytes32),32)]`, `ss`,
    `(abi_child_suffix_state mid.cs_next_var head_addr dyn_addr tail_offset child_size ss)
      with vs_inst_idx := LENGTH mid.cs_current_insts + 3`,
    `abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss`]
    abi_memory_frame_trans) >>
  impl_tac >- simp[abi_dynamic_loop_update_state_def, abi_memory_frame_inst_idx,
    abi_child_suffix_written_frame, abi_dynamic_loop_latch_memory_frame] >> simp[]
QED

Theorem abi_dynamic_loop_update_counter:
  !mid head_addr dyn_addr counter_addr index tail_offset child_size ss.
    mload (w2n counter_addr)
      (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss) = index + 1w
Proof
  simp[abi_dynamic_loop_update_state_def, abi_dynamic_loop_latch_control]
QED

Theorem abi_dynamic_loop_after_child_path:
  !ctx func var_base labels child_len mid ss src head_addr dyn_addr counter_addr index tail_offset child_size header_bb.
    fn_has_code mid (abi_child_suffix_cut (Var (compiler_var_name var_base 12))
      (Var (compiler_var_name var_base 13)) (Var (compiler_var_name var_base 1)) child_len mid) func /\
    (let stored = abi_child_suffix_cut (Var (compiler_var_name var_base 12))
       (Var (compiler_var_name var_base 13)) (Var (compiler_var_name var_base 1)) child_len mid in
     let latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name var_base 0))
       (Var (compiler_var_name var_base 6)) (fresh_label_output "enc_dyn_hdr" labels) stored in
     fn_has_code latched
       (abi_dynamic_loop_exit_cut src (Var (compiler_var_name var_base 1))
         (fresh_label_output "enc_dyn_exit" (labels + 2)) latched) func) /\
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) func.fn_blocks = SOME header_bb /\
    phi_prefix_length header_bb.bb_instructions = 0 /\
    ss.vs_current_bb = mid.cs_current_bb /\ ss.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name var_base 1)) ss = SOME dyn_addr /\
    eval_operand (Var (compiler_var_name var_base 6)) ss = SOME index /\
    eval_operand (Var (compiler_var_name var_base 12)) ss = SOME head_addr /\
    eval_operand (Var (compiler_var_name var_base 13)) ss = SOME tail_offset /\
    eval_operand child_len ss = SOME child_size /\ var_base + 15 <= mid.cs_next_var ==>
    fragment_path ctx func ss (jump_to (fresh_label_output "enc_dyn_hdr" labels)
      (abi_dynamic_loop_update_state mid head_addr dyn_addr counter_addr index tail_offset child_size ss))
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `stored = abi_child_suffix_cut (Var (compiler_var_name var_base 12))
    (Var (compiler_var_name var_base 13)) (Var (compiler_var_name var_base 1)) child_len mid` >>
  qabbrev_tac `latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name var_base 0))
    (Var (compiler_var_name var_base 6)) (fresh_label_output "enc_dyn_hdr" labels) stored` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `Var (compiler_var_name var_base 12)`, `Var (compiler_var_name var_base 13)`,
    `Var (compiler_var_name var_base 1)`, `child_len`, `mid`, `ss`, `head_addr`, `dyn_addr`, `tail_offset`, `child_size`]
    abi_child_suffix_path) >>
  impl_tac >- simp[Abbr`stored`, abi_dynamic_loop_saved_name] >> DISCH_TAC >>
  qabbrev_tac `after_suffix = (abi_child_suffix_state mid.cs_next_var head_addr dyn_addr tail_offset child_size ss)
    with vs_inst_idx := LENGTH stored.cs_current_insts` >>
  mp_tac (Q.SPECL [`src`, `Var (compiler_var_name var_base 1)`,
    `fresh_label_output "enc_dyn_exit" (labels + 2)`, `latched`, `func`] abi_dynamic_loop_contains_exit) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `stored.cs_next_id`, `stored.cs_next_var`,
    `Var (compiler_var_name var_base 0)`, `Var (compiler_var_name var_base 6)`,
    `fresh_label_output "enc_dyn_hdr" labels`, `after_suffix`, `counter_addr`, `index`,
    `<|bb_label := latched.cs_current_bb; bb_instructions := latched.cs_current_insts|>`, `header_bb`]
    abi_dynamic_loop_latch_path) >>
  impl_tac >- fs[Abbr`after_suffix`, Abbr`latched`, Abbr`stored`, abi_child_suffix_cut_def,
    abi_dynamic_loop_latch_cut_def, abi_child_suffix_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2,
    abi_child_suffix_control, abi_child_suffix_operand_frame, eval_op_inst_idx,
    compiler_var_name_add, abi_dynamic_loop_saved_name] >> DISCH_TAC >>
  `fragment_path ctx func ss (jump_to (fresh_label_output "enc_dyn_hdr" labels)
    (abi_dynamic_loop_latch_state stored.cs_next_var counter_addr index after_suffix))` by
    (irule fragment_path_trans >> qexists_tac `after_suffix` >> fs[Abbr`after_suffix`, Abbr`stored`]) >>
  fs[Abbr`after_suffix`, Abbr`stored`, abi_child_suffix_cut_def, abi_child_suffix_insts_def,
    abi_dynamic_loop_update_state_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic ABI loop recursive-child continuation: " ^ name)
  end) (DB.thms "abiDynamicLoopUpdate")
