(* TOP-LEVEL: the generated static loop advances the enclosing traversal
   from its actual header compiler point to its actual exit. Its precise
   output/index frame remains available to preserve the parent counter. *)
Theory abiNativeStaticLoopTraversal
Ancestors
  abiNativeStaticArrayLoop abiNativeStaticArrayState abiNativeStaticHeaderCode abiNativeArrayResources
  abiNativeCursor abiNativeTraversal abiNativeTraversalStep abiNativeEncodingDefs abiMemoryLeafRun
  abiAllocationTrace abiAllocationWindows abiAllocatorState abiMemoryFrame abiStateFrame abiFieldOperands
  abiStaticLoopCode compileAllocaProvenance compileIdFlow compileEnv fragExec venomState list words arithmetic

Theorem abi_native_static_loop_traversal:
  !ctx func root_cs root_after source_id target_id counter_inst counter_addr root_addr source_capacity dst_addr
      info stride fields initial ss dst src len_op cs ret after.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
      initial (abi_native_static_header_cut cs) ss /\
    abi_native_cursor func root_cs root_after counter_inst counter_addr (abi_native_static_header_cut cs) ss /\
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity 0 ss /\ LENGTH fields < dimword (:256) /\ compiler_id_history cs /\
    compile_abi_encode_dyn_static_loop dst src info (abi_static_encoder_size info) stride len_op cs = (ret,after) /\
    fn_has_code cs after func /\ cs_extends after root_after /\
    ss.vs_current_bb = fresh_label_output "enc_dyn_hdr" cs.cs_next_label /\ ss.vs_inst_idx = 0 /\ ~ss.vs_halted /\
    eval_operand dst ss = SOME dst_addr /\ eval_operand src ss = SOME root_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) ss = SOME counter_addr /\
    eval_operand len_op ss = SOME (n2w (LENGTH fields)) /\
    abi_operand_before (cs.cs_next_var + 1) dst /\ abi_operand_before (cs.cs_next_var + 1) src /\
    abi_operand_before (cs.cs_next_var + 1) len_op ==>
    ?out. abi_native_traversal ctx func root_cs root_after dst_addr
      (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields) initial after out /\
      abi_encoding_result ctx func (abi_native_static_header_cut cs) after ret dst_addr
        (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
        (abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out /\
      abi_allocator_state out = abi_allocator_state ss /\
      abi_memory_frame [(w2n dst_addr,LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields));(w2n counter_addr,32)] ss out /\ ~out.vs_halted
Proof
  rpt gen_tac >> strip_tac >> `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_allocation >> strip_tac >>
  drule_all abi_native_array_resources_initial >> DISCH_TAC >>
  `EVERY (\name. src <> Var name /\ dst <> Var name /\ len_op <> Var name)
    (abi_static_loop_tail_names cs.cs_next_var info)` by
    (simp_tac bool_ss [EVERY_CONJ] >> rpt conj_tac >>
     irule abi_native_static_header_operand_names >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `source_id`, `target_id`, `counter_inst`, `counter_addr`,
    `abi_native_static_header_cut cs`, `root_addr`, `source_capacity`, `dst_addr`, `info`, `stride`, `fields`,
    `initial`, `ss`, `dst`, `src`, `len_op`, `cs`, `ret`, `after`] mp_tac abi_native_static_array_loop >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  `!arg_op. abi_operand_before (abi_native_static_header_cut cs).cs_next_var arg_op ==>
    eval_operand arg_op out = eval_operand arg_op ss` by
    (rpt gen_tac >> simp_tac (srw_ss()) [abi_native_static_header_cut_def] >> DISCH_TAC >>
     first_x_assum irule >> drule_all abi_native_static_header_operand_names >> simp[]) >>
  `abi_encoding_result ctx func (abi_native_static_header_cut cs) after ret dst_addr
    (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)
    (abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out` by
    (PURE_REWRITE_TAC [abi_encoding_result_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_allocation_trace 32 (compiler_alloca_ids (abi_native_static_header_cut cs) after) ss out` by
    (irule abi_allocation_trace_identity >> first_assum MATCH_ACCEPT_TAC) >>
  `cs_extends (abi_native_static_header_cut cs) after` by
    (drule_all abi_native_static_header_continuation >> simp[]) >>
  drule_all abi_native_static_header_after_flow >> strip_tac >>
  qexists_tac `out` >> conj_tac
  >- (drule_all abi_native_traversal_step >> simp[]) >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static loop traversal advancement: " ^ name)
  end) (DB.thms "abiNativeStaticLoopTraversal")
