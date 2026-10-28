(* TOP-LEVEL: the actual index setup establishes its owned cursor and
   advances the enclosing traversal to the generated static-loop header.
   Helper: its real path is an empty-payload result for sequential framing. *)
Theory abiNativeStaticStartReady
Ancestors
  abiNativeStaticStartState abiNativeStaticCounterCode abiNativeStaticHeaderCode
  abiNativeArrayBudget abiNativeComplexPrefixReady abiNativeCursor abiNativeTraversal abiNativeTraversalStep
  abiNativeEncodingDefs abiMemoryLeafRun abiStaticLoopEntry abiStaticLoopCode abiAllocationWindows
  abiMemoryFrame abiFieldOperands compileAllocaProvenance compileIdFlow compileEnv fragExec
  venomMemDefs venomState venomInst list words arithmetic

Theorem abi_native_static_start_cursor:
  !func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload
      dst src info width stride len_op cs ret after counter_inst ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload ss /\
    counter_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    cs_extends root_cs cs /\ compiler_id_history cs /\
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\
    fn_has_code cs after func /\ cs_extends after root_after ==>
    abi_native_cursor func root_cs root_after counter_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_static_counter_provenance >> strip_tac >>
  qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
  `MEM cs.cs_next_id (compiler_alloca_ids root_cs root_after)` by gvs[mk_inst_def] >>
  `abi_alloca_request_ok cs.cs_next_id 32 ss` by (first_x_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`cs`, `compiler_alloca_ids root_cs root_after`, `ss`]
    mp_tac abi_native_static_start_window >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  simp_tac bool_ss [abi_native_cursor_def] >> asm_simp_tac (srw_ss()) [mk_inst_def]
QED

Theorem abi_native_static_start_result:
  !ctx func root_cs root_after dst_addr counter_inst dst src info width stride len_op cs ret after ss.
    abi_native_cursor func root_cs root_after counter_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    counter_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    compiler_id_history cs /\
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    abi_encoding_result ctx func cs (abi_native_static_header_cut cs) (Lit 0w) (dst_addr:bytes32) []
      (abi_allocation_windows (compiler_alloca_ids root_cs root_after)
        (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss))
      ss (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    abi_allocation_trace 32 (compiler_alloca_ids cs (abi_native_static_header_cut cs))
      ss (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cs`, `ss`] strip_assume_tac abi_native_static_start_context >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `abi_static_loop_counter_addr cs.cs_next_id ss`,
    `abi_native_static_header_cut cs`, `ss`, `abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss`,
    `dst_addr`, `[]:word8 list`] mp_tac abi_native_cursor_store_frame >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `ss`]
    mp_tac abi_native_static_start_path >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule_all abi_native_static_counter_local_profile >> DISCH_TAC >>
  drule abi_native_static_start_trace >> disch_then (qspec_then `ss` ASSUME_TAC) >>
  conj_tac >- (asm_simp_tac (srw_ss()) [abi_encoding_result_def, eval_operand_def, read_memory_def] >>
    rpt strip_tac >> drule_all abi_native_static_start_old_operand >> simp[]) >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_static_start_traversal:
  !ctx func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial
      dst src info width stride len_op cs ret after counter_inst ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr payload initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial cs ss /\
    counter_inst = mk_inst cs.cs_next_id ALLOCA [Lit 32w] [compiler_var_name cs.cs_next_var 0] /\
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\
    fn_has_code cs after func /\ cs_extends after root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    abi_native_traversal ctx func root_cs root_after dst_addr payload initial (abi_native_static_header_cut cs)
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    abi_native_cursor func root_cs root_after counter_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_traversal_root_ready >> DISCH_TAC >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule_all abi_native_static_start_cursor >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `dst_addr`, `counter_inst`, `dst`, `src`, `info`,
    `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `ss`] mp_tac abi_native_static_start_result >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`cs`, `ss`] strip_assume_tac abi_native_static_start_context >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `abi_static_loop_counter_addr cs.cs_next_id ss`,
    `abi_native_static_header_cut cs`, `ss`, `abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss`,
    `dst_addr`, `payload`] mp_tac abi_native_cursor_store_frame >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `cs_extends cs (abi_native_static_header_cut cs)` by simp[abi_native_static_header_extends] >>
  `cs_extends (abi_native_static_header_cut cs) root_after` by
    (irule cs_extends_trans >> qexists_tac `after` >> simp[] >> drule_all abi_native_static_header_continuation >> simp[]) >>
  `cs.cs_next_var <= (abi_native_static_header_cut cs).cs_next_var /\
    compiler_id_history (abi_native_static_header_cut cs)` by
    (conj_tac >- simp[abi_native_static_header_cut_def] >>
     irule abi_native_static_header_history >> first_assum MATCH_ACCEPT_TAC) >>
  `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  conj_tac >- (drule_all abi_native_traversal_step >> simp[]) >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native static header readiness: " ^ name)
  end) (DB.thms "abiNativeStaticStartReady")
