(* TOP-LEVEL: one iteration of the actual dynamic-child loop composes its
   header, address prefix, recursive child, head/tail stores and back edge.
   The child-return contract names only the values the wrapper consumes. *)
Theory abiDynamicLoopIteration
Ancestors
  abiDynamicLoopStep abiDynamicLoopCode abiDynamicLoopFactor abiDynamicLoopStructure
  abiDynamicLoopUpdate abiChildCode abiStaticLoopCode
  compileEnv fragExec fragBlockPath venomState list words arithmetic

Definition abi_dynamic_loop_child_return_def:
  abi_dynamic_loop_child_return var_base mid child_len dst_addr abi_sz counter_addr dyn_addr
      index tail_offset child_size ss <=>
    ss.vs_current_bb = mid.cs_current_bb /\ ss.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~ss.vs_halted /\
    eval_operand (Var (compiler_var_name var_base 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name var_base 1)) ss = SOME dyn_addr /\
    eval_operand (Var (compiler_var_name var_base 6)) ss = SOME index /\
    eval_operand (Var (compiler_var_name var_base 12)) ss = SOME (dst_addr + 32w + index * n2w abi_sz) /\
    eval_operand (Var (compiler_var_name var_base 13)) ss = SOME tail_offset /\
    eval_operand child_len ss = SOME child_size
End

Theorem abi_dynamic_loop_iteration_path:
  !ctx func dst src info abi_sz mem_sz len_op cs op cs' child_len mid ss child_out
      dst_addr src_addr counter_addr dyn_addr len_word child_size.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
    fn_has_code cs cs' func /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\
    ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand src ss = SOME src_addr /\ eval_operand dst ss = SOME dst_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 1)) ss = SOME dyn_addr /\
    eval_operand len_op ss = SOME len_word /\ len_op <> Var (compiler_var_name cs.cs_next_var 3) /\
    w2n (mload (w2n counter_addr) ss) < w2n len_word /\
    EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12) /\
    fragment_path ctx func
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr src_addr abi_sz mem_sz
        counter_addr dyn_addr len_word ss) child_out /\
    abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr abi_sz counter_addr dyn_addr
      (mload (w2n counter_addr) ss) (mload (w2n dyn_addr) ss) child_size child_out ==>
    fragment_path ctx func ss
      (jump_to (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
        (abi_dynamic_loop_update_state mid
          (dst_addr + 32w + mload (w2n counter_addr) ss * n2w abi_sz) dyn_addr counter_addr
          (mload (w2n counter_addr) ss) (mload (w2n dyn_addr) ss) child_size child_out))
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
  `fragment_path ctx func ss
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr src_addr abi_sz mem_sz
      counter_addr dyn_addr len_word ss)` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `abi_sz`, `mem_sz`, `len_op`, `cs`, `ss`,
       `dst_addr`, `src_addr`, `counter_addr`, `dyn_addr`, `len_word`] abi_dynamic_loop_header_body_path) >>
     impl_tac >- fs[] >> simp[]) >>
  drule_all abi_dynamic_loop_contains_prefix >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cs.cs_next_var`, `cs.cs_next_label`, `child_len`, `mid`, `child_out`,
    `src`, `dst_addr + 32w + mload (w2n (counter_addr:bytes32)) ss * n2w abi_sz`, `dyn_addr`, `counter_addr`,
    `mload (w2n (counter_addr:bytes32)) ss`, `mload (w2n (dyn_addr:bytes32)) ss`, `child_size`,
    `<|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
       bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|>`]
    abi_dynamic_loop_after_child_path) >>
  impl_tac >- fs[abi_dynamic_loop_child_return_def, abi_dynamic_loop_no_phi, LET_THM] >> DISCH_TAC >>
  irule fragment_path_trans >> qexists_tac `child_out` >> simp[] >>
  irule fragment_path_trans >>
  qexists_tac `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr src_addr abi_sz mem_sz
    counter_addr dyn_addr len_word ss` >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic ABI loop iteration: " ^ name)
  end) (DB.thms "abiDynamicLoopIteration")
