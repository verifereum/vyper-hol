(* TOP-LEVEL: execute the actual recursive child from its semantic
   induction assertion and retain the layout and both loop cursors
   required by the real post-child stores and latch. *)
Theory abiNativeDynamicArrayChildComplete
Ancestors
  abiNativeDynamicArrayChild abiNativeDynamicArrayChildLayout abiNativeDynamicArrayCallReady abiNativeDynamicArrayCallCursor
  abiNativeDynamicArrayPrefixTraversal abiNativeDynamicArrayState abiNativeFields abiNativeTraversal abiNativeEncodingDefs
  abiNativeCursor abiEncoderStructure abiDynamicLoopRun abiDynamicLoopIteration abiDynamicLoopCode abiDynamicLoopStep
  abiStaticLoopCode abiFieldOperands abiFieldMemory abiFieldLayoutDefs compileEnv fragExec venomMemDefs venomState venomInst list words

Theorem abi_native_dynamic_array_child_complete:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op mid child_len ss index counter_addr dyn_addr dyn_inst index_inst.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial cs ss /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr (LENGTH fields) index ss /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss /\
    abi_native_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) (w2n root_addr + 32) reference fields /\
    mem_bytes_at (w2n root_addr) source_capacity reference = mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 14)) (Var (compiler_var_name cs.cs_next_var 9)) info
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) = (child_len,mid) /\
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) func /\
    fn_has_code (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid func /\ cs_extends mid after /\
    abi_native_cursor func cs after dyn_inst dyn_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) ss /\
    abi_native_cursor func cs after index_inst counter_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) ss /\
    w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\ LENGTH fields < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    ?out. abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) out /\
      abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial mid out /\
      abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr width counter_addr dyn_addr
        (n2w index) (mload (w2n dyn_addr) ss) (n2w (LENGTH (SND (EL index fields)))) out /\ ~out.vs_halted /\
      abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) out /\
      read_memory (w2n dst_addr + 32 + abi_field_head_size fields + abi_field_tail_size (TAKE index fields))
        (LENGTH (SND (EL index fields))) out = SND (EL index fields) /\
      abi_native_cursor func cs after dyn_inst dyn_addr mid out /\ abi_native_cursor func cs after index_inst counter_addr mid out
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv initial /\ ~MEM source_id (compiler_alloca_ids cs after) /\ ~MEM target_id (compiler_alloca_ids cs after)` by
    fs[abi_native_memory_ready_def] >>
  drule_all abi_native_dynamic_array_child >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all abi_native_dynamic_array_prefix_traversal >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_call_ready >> strip_tac >>
  drule_all abi_native_dynamic_array_child_layout >> strip_tac >>
  `cs_extends (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid` by
    (drule_all compile_abi_encode_extends >> simp[]) >>
  `!counter_inst read_addr.
    abi_native_cursor func cs after counter_inst read_addr (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) ss ==>
    abi_native_cursor func cs after counter_inst read_addr mid out` by
    (rpt gen_tac >> DISCH_TAC >>
     `counter_inst.inst_id <> target_id` by
       (qspecl_then [`func`, `cs`, `after`, `counter_inst`, `read_addr`,
          `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`, `ss`, `source_id`, `target_id`]
          mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
     qspecl_then [`ctx`, `func`, `cs`, `after`, `counter_inst`, `read_addr`, `dst`, `src`, `width`, `stride`, `len_op`,
       `dst_addr`, `root_addr`, `counter_addr`, `dyn_addr`, `n2w (LENGTH fields)`, `ss`, `source_id`, `target_id`,
       `root_addr + 32w + n2w index * n2w stride`, `stride`, `SND (EL index fields)`, `mid`, `child_len`, `out`]
       mp_tac abi_native_dynamic_array_call_cursor >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]) >>
  qexists_tac `out` >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    first_x_assum irule >> first_assum MATCH_ACCEPT_TAC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual dynamic array child layout and cursor preservation: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayChildComplete")
