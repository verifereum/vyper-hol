(* TOP-LEVEL: the actual loop header and address instructions advance the
   enclosing execution to the compiled recursive-child cut. Repeated loop
   iterations reuse this same genuine compiler prefix and allocation scope. *)
Theory abiNativeDynamicArrayPrefixTraversal
Ancestors
  abiNativeDynamicArrayPrefixCode abiNativeDynamicArrayPrefixState abiNativeTraversal abiNativeTraversalLoop
  abiDynamicLoopRun abiDynamicLoopStep abiDynamicLoopCode abiDynamicLoopStructure abiStaticLoopCode
  abiAllocationTrace abiAllocationWindows abiAllocatorState abiStateFrame abiMemoryFrame abiFieldOperands
  compileAllocaProvenance compileIdFlow compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_prefix_path:
  !ctx func dst src width stride len_op cs ss dst_addr root_addr counter_addr dyn_addr loop_count index.
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) func /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr loop_count index ss /\
    index < loop_count /\ loop_count < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    fragment_path ctx func ss (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w loop_count) ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_dynamic_loop_ready _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_dynamic_loop_ready_def]) >>
  `index < dimword (:256)` by decide_tac >>
  `len_op <> Var (compiler_var_name cs.cs_next_var 3)` by
    (qpat_x_assum `abi_operand_before _ len_op` (mp_tac o PURE_REWRITE_RULE [abi_operand_before_def]) >>
     disch_then (qspec_then `cs.cs_next_var + 3` mp_tac) >> simp[compiler_var_name_def]) >>
  `EVERY (\name. src <> Var name /\ dst <> Var name) (compiler_var_names (cs.cs_next_var + 3) 12)` by
    (simp_tac bool_ss [EVERY_CONJ] >> conj_tac >> irule abi_operand_before_names >>
     qexists_tac `cs.cs_next_var + 3` >> simp[]) >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `width`, `stride`, `len_op`, `cs`, `ss`, `dst_addr`, `root_addr`,
    `counter_addr`, `dyn_addr`, `n2w loop_count`] mp_tac abi_dynamic_loop_header_body_path >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> simp_tac bool_ss []
QED

Theorem abi_native_dynamic_array_prefix_traversal:
  !ctx func cs after root_dst root_payload initial dst src width stride len_op ss dst_addr root_addr counter_addr dyn_addr loop_count index.
    abi_native_traversal ctx func cs after root_dst root_payload initial cs ss /\ alloca_inv initial /\
    fn_has_code cs (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) func /\
    abi_dynamic_loop_ready cs dst src len_op dst_addr root_addr counter_addr dyn_addr loop_count index ss /\
    index < loop_count /\ loop_count < dimword (:256) /\
    abi_operand_before (cs.cs_next_var + 3) dst /\ abi_operand_before (cs.cs_next_var + 3) src /\
    abi_operand_before (cs.cs_next_var + 3) len_op ==>
    abi_native_traversal ctx func cs after root_dst root_payload initial
      (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)
      (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
        counter_addr dyn_addr (n2w loop_count) ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule_all abi_native_dynamic_array_prefix_path >> disch_then (qspec_then `ctx` ASSUME_TAC) >>
  qspecl_then [`cs`, `dst_addr`, `root_addr`, `width`, `stride`, `counter_addr`, `dyn_addr`, `n2w loop_count`, `ss`]
    strip_assume_tac abi_native_dynamic_array_prefix_context >>
  `abi_allocation_trace 32 (compiler_alloca_ids cs after) ss
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w loop_count) ss)` by
    (irule abi_allocation_trace_identity >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_memory_frame ((w2n root_dst,LENGTH root_payload)::abi_allocation_windows (compiler_alloca_ids cs after)
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w loop_count) ss)) ss
    (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w loop_count) ss)` by
    (irule abi_memory_frame_memory >> first_assum MATCH_ACCEPT_TAC) >>
  `!arg_op. abi_operand_before cs.cs_next_var arg_op ==>
    eval_operand arg_op (abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w loop_count) ss) = eval_operand arg_op ss` by
    (rpt gen_tac >> DISCH_TAC >> irule abi_native_dynamic_array_prefix_old_operand >>
     irule abi_operand_before_mono >> qexists_tac `cs.cs_next_var` >> simp[]) >>
  drule_all abi_native_traversal_runtime_step >> DISCH_TAC >>
  `cs_extends cs (abi_dynamic_loop_prefix_cut dst src width stride len_op cs) /\
    cs.cs_next_var <= (abi_dynamic_loop_prefix_cut dst src width stride len_op cs).cs_next_var /\
    compiler_id_history (abi_dynamic_loop_prefix_cut dst src width stride len_op cs)` by
    (conj_tac >- simp[abi_dynamic_loop_cuts_extend] >> conj_tac >- simp[abi_dynamic_loop_prefix_cut_def] >>
     irule abi_native_dynamic_array_prefix_history >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `root_dst`, `root_payload`, `initial`, `cs`,
    `abi_dynamic_loop_child_state cs.cs_next_var cs.cs_next_label dst_addr root_addr width stride
      counter_addr dyn_addr (n2w loop_count) ss`, `abi_dynamic_loop_prefix_cut dst src width stride len_op cs`]
    mp_tac abi_native_traversal_context >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual array header/address traversal into recursive child: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayPrefixTraversal")
