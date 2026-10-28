(* TOP-LEVEL: factor the actual dynamic-child array compiler around its
   arbitrary recursive child and the shared dynamic-child suffix. *)
Theory abiDynamicLoopFactor
Ancestors
  abiDynamicLoopCode abiChildCode abiEncoder abiEncodeVarFlow abiStaticLoopCode context compileEnv
  emitHelper exprLoweringProps fragExec venomInst list arithmetic
Libs pairLib

Theorem compile_abi_dynamic_loop_factor:
  !dst src info abi_sz mem_sz len_op cs.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs =
    let prefix = abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs in
    let (child_len,mid) = compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info prefix in
    let stored = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
      (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid in
    let latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
      (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) stored in
    (Var (compiler_var_name latched.cs_next_var 2),
      abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
        (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2)) latched)
Proof
  rpt gen_tac >>
  simp[Once compile_abi_encode_child_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, emit_inst_def, fresh_id_def, fresh_var_def,
    fresh_label_def, new_block_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
    abi_dynamic_loop_prefix_cut_def, abi_dynamic_loop_entry_def,
    abi_dynamic_loop_header_def, abi_dynamic_loop_body_prefix_def, compiler_var_name_def] >>
  PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >> simp[] >> pairarg_tac >>
  simp[abi_child_suffix_cut_def, abi_child_suffix_insts_def, abi_dynamic_loop_latch_cut_def,
    abi_dynamic_loop_latch_def, abi_dynamic_loop_exit_cut_def, abi_dynamic_loop_exit_def,
    compiler_var_name_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  PURE_ASM_REWRITE_TAC [GSYM APPEND_ASSOC, APPEND] >> simp[compile_state_component_equality]
QED

Theorem compile_abi_dynamic_loop_split:
  !dst src info abi_sz mem_sz len_op cs op cs'.
    compile_abi_encode_dyn_loop dst src info abi_sz mem_sz len_op cs = (op,cs') <=>
    ?child_len mid.
      compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
        (Var (compiler_var_name cs.cs_next_var 9)) info
        (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) /\
      let stored = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 12))
        (Var (compiler_var_name cs.cs_next_var 13)) (Var (compiler_var_name cs.cs_next_var 1)) child_len mid in
      let latched = abi_dynamic_loop_latch_cut (Var (compiler_var_name cs.cs_next_var 0))
        (Var (compiler_var_name cs.cs_next_var 6)) (fresh_label_output "enc_dyn_hdr" cs.cs_next_label) stored in
      op = Var (compiler_var_name latched.cs_next_var 2) /\
      cs' = abi_dynamic_loop_exit_cut src (Var (compiler_var_name cs.cs_next_var 1))
        (fresh_label_output "enc_dyn_exit" (cs.cs_next_label + 2)) latched
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_abi_dynamic_loop_factor, LET_THM] >>
  pairarg_tac >> simp[EQ_SYM_EQ]
QED

Theorem abi_dynamic_loop_child_next_var:
  !dst src info abi_sz mem_sz len_op cs child_len mid.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14))
      (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src abi_sz mem_sz len_op cs) = (child_len,mid) ==>
    cs.cs_next_var + 15 <= mid.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >> drule compile_abi_encode_next_var >>
  simp[abi_dynamic_loop_prefix_cut_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic ABI loop decomposition: " ^ name)
  end) (DB.thms "abiDynamicLoopFactor")
