(* TOP-LEVEL: the actual compiled child continuation reaches the next
   generated header through its head/tail stores and index latch. *)
Theory abiNativeDynamicArrayUpdatePath
Ancestors
  abiNativeDynamicArrayUpdateState abiDynamicLoopIteration abiDynamicLoopUpdate abiDynamicLoopFactor
  abiDynamicLoopStructure abiDynamicLoopCode abiChildCode abiStaticLoopCode
  compileEnv fragExec fragBlockPath venomState list words arithmetic

Theorem abi_native_dynamic_array_next_path:
  !ctx func dst src info width stride len_op cs ret after child_len mid ss dst_addr counter_addr dyn_addr index tail_offset child_size.
    compile_abi_encode_dyn_loop dst src info width stride len_op cs = (ret,after) /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\ fn_has_code cs after func /\
    abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr width counter_addr dyn_addr
      (n2w index) tail_offset child_size ss ==>
    fragment_path ctx func ss
      (abi_native_dynamic_array_next_state cs mid dst_addr width counter_addr dyn_addr index tail_offset child_size ss)
Proof
  rpt gen_tac >> strip_tac >>
  `after = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
    (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2))
    (abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label)
      (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
        (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid))` by
    fs[compile_abi_dynamic_loop_factor, LET_THM] >>
  gvs[] >> drule_all abi_dynamic_loop_contains_parts >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_dynamic_loop_child_next_var >> DISCH_TAC >>
  drule_all abi_dynamic_loop_contains_prefix >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs.cs_next_var`, `cs.cs_next_label`, `child_len`, `mid`, `ss`, `src`,
    `dst_addr + 32w + n2w index * n2w width`, `dyn_addr`, `counter_addr`, `n2w index`, `tail_offset`, `child_size`,
    `<|bb_label := fresh_label_output "enc_dyn_hdr" cs.cs_next_label;
       bb_instructions := abi_dynamic_loop_header cs.cs_next_id cs.cs_next_var cs.cs_next_label len_op|>`]
    mp_tac abi_dynamic_loop_after_child_path >>
  impl_tac >- fs[abi_dynamic_loop_child_return_def, abi_dynamic_loop_no_phi, LET_THM] >>
  simp_tac bool_ss [abi_native_dynamic_array_next_state_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual compiled array child continuation path: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayUpdatePath")
