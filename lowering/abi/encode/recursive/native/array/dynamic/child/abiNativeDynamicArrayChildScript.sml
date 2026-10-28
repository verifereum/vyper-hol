(* TOP-LEVEL: from a live real loop header, execute its address prefix and
   recursive child using the semantic native induction assertion. The exact
   child-return contract and enclosing traversal are consequences of that run. *)
Theory abiNativeDynamicArrayChild
Ancestors
  abiNativeDynamicArrayPrefixTraversal abiNativeDynamicArrayCall abiNativeDynamicArrayCallReturn abiNativeDynamicArrayCallTraversal
  abiNativeDynamicArrayState abiNativeFields abiNativeTraversal abiNativeEncodingDefs abiDynamicLoopRun abiDynamicLoopIteration
  abiDynamicLoopCode abiDynamicLoopStep abiStaticLoopCode abiFieldOperands abiFieldLayoutDefs
  compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_child:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial reference
      dst src len_op mid child_len ss index counter_addr dyn_addr.
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
    w2n (dst_addr + 32w) = w2n dst_addr + 32 /\ index < LENGTH fields /\ LENGTH fields < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    ?out. abi_native_encoding_result ctx func (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) mid child_len
      (dst_addr + 32w + mload (w2n dyn_addr) ss) (SND (EL index fields))
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w (LENGTH fields)) ss) out /\
      abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial mid out /\
      abi_dynamic_loop_child_return cs.cs_next_var mid child_len dst_addr width counter_addr dyn_addr
        (n2w index) (mload (w2n dyn_addr) ss) (n2w (LENGTH (SND (EL index fields)))) out /\ ~out.vs_halted
Proof
  rpt gen_tac >> strip_tac >> `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  qpat_assum `abi_dynamic_loop_ready _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_dynamic_loop_ready_def]) >>
  drule_all abi_native_dynamic_array_prefix_traversal >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_call >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all abi_native_dynamic_array_call_traversal >> DISCH_TAC >>
  drule_all abi_native_dynamic_array_call_return >> DISCH_TAC >>
  qexists_tac `out` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual array header and semantic recursive child execution: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayChild")
