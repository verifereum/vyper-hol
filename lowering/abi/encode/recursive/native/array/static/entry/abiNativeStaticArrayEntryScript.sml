(* TOP-LEVEL: the actual parent and index prefixes establish both enclosing
   traversal points and their real allocation cursors. No loop execution
   or initialized-header contract is assumed. *)
Theory abiNativeStaticArrayEntry
Ancestors
  abiNativeStaticArrayHeader abiNativeArrayEntryOperands abiNativeArrayParentReady abiNativeStaticStartReady
  abiNativeTraversal abiNativeCursor abiNativeEncodingDefs abiDynArrayCode abiDynArrayBoundaryFrames
  abiStaticLoopEntry abiStaticLoopCode abiFieldOperands compileEnv fragExec venomState list words arithmetic

Theorem abi_native_static_array_prefix_traversal:
  !ctx func cs root_after source_id target_id root_addr source_capacity dst_addr payload initial dst src info width stride ret after.
    abi_native_memory_ready func cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    32 <= LENGTH payload /\
    compile_abi_encode_dyn_static_loop dst src info width stride (Var (compiler_var_name cs.cs_next_var 1))
      (abi_dynarray_entry_cut dst src cs) = (ret,after) /\
    fn_has_code cs (abi_dynarray_entry_cut dst src cs) func /\
    fn_has_code (abi_dynarray_entry_cut dst src cs) after func /\ cs_extends after root_after /\
    abi_operand_before cs.cs_next_var dst /\ abi_operand_before cs.cs_next_var src /\
    eval_operand dst initial = SOME dst_addr /\ eval_operand src initial = SOME root_addr /\
    initial.vs_current_bb = cs.cs_current_bb /\ initial.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~initial.vs_halted ==>
    abi_native_traversal ctx func cs root_after dst_addr payload initial (abi_dynarray_entry_cut dst src cs)
      (abi_dynarray_entry_boundary cs dst_addr root_addr initial) /\
    abi_native_cursor func cs root_after (abi_native_array_counter_inst cs) (abi_static_loop_counter_addr cs.cs_next_id initial)
      (abi_dynarray_entry_cut dst src cs) (abi_dynarray_entry_boundary cs dst_addr root_addr initial) /\
    abi_native_traversal ctx func cs root_after dst_addr payload initial
      (abi_native_static_header_cut (abi_dynarray_entry_cut dst src cs))
      (abi_native_static_array_start cs dst src dst_addr root_addr initial) /\
    abi_native_cursor func cs root_after (abi_native_array_counter_inst (abi_dynarray_entry_cut dst src cs))
      (abi_static_loop_counter_addr (abi_dynarray_entry_cut dst src cs).cs_next_id
        (abi_dynarray_entry_boundary cs dst_addr root_addr initial))
      (abi_native_static_header_cut (abi_dynarray_entry_cut dst src cs))
      (abi_native_static_array_start cs dst src dst_addr root_addr initial)
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends (abi_dynarray_entry_cut dst src cs) root_after` by
    (irule cs_extends_trans >> qexists_tac `after` >> simp[] >> drule_all compile_abi_dyn_static_loop_extends >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`,
    `dst_addr`, `payload`, `initial`, `dst`, `src`, `abi_native_array_counter_inst cs`]
    mp_tac abi_native_array_parent_traversal >>
  impl_tac >- asm_simp_tac bool_ss [abi_native_array_counter_inst_def] >> strip_tac >>
  qspecl_then [`cs`, `dst`, `src`, `dst_addr`, `root_addr`, `initial`]
    mp_tac abi_native_array_parent_control >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `root_after`, `source_id`, `target_id`, `root_addr`, `source_capacity`,
    `dst_addr`, `payload`, `initial`, `dst`, `src`, `info`, `width`, `stride`, `Var (compiler_var_name cs.cs_next_var 1)`,
    `abi_dynarray_entry_cut dst src cs`, `ret`, `after`, `abi_native_array_counter_inst (abi_dynarray_entry_cut dst src cs)`,
    `abi_dynarray_entry_boundary cs dst_addr root_addr initial`] mp_tac abi_native_static_start_traversal >>
  impl_tac >- asm_simp_tac bool_ss [abi_native_array_counter_inst_def] >> strip_tac >>
  asm_simp_tac bool_ss [abi_native_static_array_start_def, LET_THM]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static array parent/index prefix execution: " ^ name)
  end) (DB.thms "abiNativeStaticArrayEntry")
