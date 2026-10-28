(* TOP-LEVEL: the actual generated static loop and actual parent epilogue
   finish the native array result from an initialized header. The enclosing
   traversal retains all prefix execution and allocation obligations. *)
Theory abiNativeStaticArrayFinish
Ancestors
  abiNativeStaticLoopTraversal abiNativeStaticParentEnd abiNativeArrayFinish abiNativeStaticHeaderCode
  abiNativeStaticArrayState abiNativeTraversal abiNativeCursor abiNativeEncodingDefs abiMemoryLeafRun
  abiDynArrayCode abiStaticLoopCode abiFieldOperands compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_static_array_finish:
  !ctx func root_cs source_id target_id counter_inst counter_addr parent_inst parent_addr parent_ptr root_addr source_capacity dst_addr
      info stride fields initial ss dst src len_op cs ret after.
    abi_native_memory_ready func root_cs (abi_dynarray_exit_cut parent_ptr ret after) source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func root_cs (abi_dynarray_exit_cut parent_ptr ret after) dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
      initial (abi_native_static_header_cut cs) ss /\
    abi_native_cursor func root_cs (abi_dynarray_exit_cut parent_ptr ret after) counter_inst counter_addr (abi_native_static_header_cut cs) ss /\
    abi_native_cursor func root_cs (abi_dynarray_exit_cut parent_ptr ret after) parent_inst parent_addr (abi_native_static_header_cut cs) ss /\
    parent_inst.inst_id <> counter_inst.inst_id /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr source_capacity 0 ss /\
    LENGTH fields < dimword (:256) /\ compiler_id_history cs /\
    compile_abi_encode_dyn_static_loop dst src info (abi_static_encoder_size info) stride len_op cs = (ret,after) /\
    fn_has_code cs after func /\ fn_has_code after (abi_dynarray_exit_cut parent_ptr ret after) func /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME (n2w (LENGTH fields)) /\
    eval_operand parent_ptr ss = SOME parent_addr /\ mload (w2n parent_addr) ss = 0w /\
    abi_operand_before (cs.cs_next_var + 1) dst /\ abi_operand_before (cs.cs_next_var + 1) src /\
    abi_operand_before (cs.cs_next_var + 1) len_op /\ abi_operand_before (cs.cs_next_var + 1) parent_ptr ==>
    ?out. abi_native_encoding_result ctx func root_cs (abi_dynarray_exit_cut parent_ptr ret after)
      (Var (compiler_var_name after.cs_next_var 2)) dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial out
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends after (abi_dynarray_exit_cut parent_ptr ret after)` by simp[abi_dynarray_cuts_extend] >>
  drule_all abi_native_static_loop_traversal >> disch_then (qx_choose_then `loop_out` strip_assume_tac) >>
  `abi_operand_before (abi_native_static_header_cut cs).cs_next_var parent_ptr` by
    simp[abi_native_static_header_cut_def] >>
  drule_all abi_native_static_parent_end >> strip_tac >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  qspecl_then [`ctx`, `func`, `root_cs`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields`,
    `initial`, `parent_inst`, `parent_addr`, `parent_ptr`, `ret`, `after`, `loop_out`] mp_tac abi_native_array_finish >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed generated static loop and parent epilogue composition: " ^ name)
  end) (DB.thms "abiNativeStaticArrayFinish")
