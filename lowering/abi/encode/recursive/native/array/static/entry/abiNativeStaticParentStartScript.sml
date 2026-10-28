(* TOP-LEVEL: actual static index setup retains the separately allocated
   parent cursor and its current word. This uses the real setup path and
   allocation identities, including when either allocation is cached. *)
Theory abiNativeStaticParentStart
Ancestors
  abiNativeStaticStartMemory abiNativeStaticStartState abiNativeStaticHeaderCode abiNativeCursor
  abiAllocatedWindows allocationPathGrowth abiStaticLoopEntry abiStaticLoopCode
  compileEnv fragExec venomMemDefs venomState list words arithmetic

Theorem abi_native_static_parent_start:
  !ctx func root_cs root_after parent_inst parent_addr counter_inst dst src info width stride len_op cs ret after ss.
    abi_native_cursor func root_cs root_after parent_inst parent_addr cs ss /\
    abi_native_cursor func root_cs root_after counter_inst (abi_static_loop_counter_addr cs.cs_next_id ss)
      (abi_native_static_header_cut cs) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    alloca_inv ss /\ alloca_inv (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    parent_inst.inst_id <> counter_inst.inst_id /\
    compile_abi_encode_dyn_static_loop dst src info width stride len_op cs = (ret,after) /\ fn_has_code cs after func /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    abi_native_cursor func root_cs root_after parent_inst parent_addr (abi_native_static_header_cut cs)
      (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) /\
    mload (w2n parent_addr) (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss) =
      mload (w2n parent_addr) ss
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ctx`, `func`, `dst`, `src`, `info`, `width`, `stride`, `len_op`, `cs`, `ret`, `after`, `ss`]
    mp_tac abi_native_static_start_path >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `allocation_growth ss (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)` by
    (drule_all fragment_path_allocation_growth >> simp[]) >>
  `abi_native_cursor func root_cs root_after parent_inst parent_addr (abi_native_static_header_cut cs)
    (abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss)` by
    (qspecl_then [`func`, `root_cs`, `root_after`, `parent_inst`, `parent_addr`, `cs`, `ss`,
       `abi_native_static_header_cut cs`, `abi_static_loop_start_state cs.cs_next_id cs.cs_next_var cs.cs_next_label ss`]
       mp_tac abi_native_cursor_step >> impl_tac >- simp[abi_native_static_header_extends] >> simp_tac bool_ss []) >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  qpat_assum `abi_native_cursor _ _ _ parent_inst _ (abi_native_static_header_cut cs) _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_cursor_def]) >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `cs`, `ss`, `parent_inst.inst_id`, `parent_addr`]
    mp_tac abi_native_static_start_owned_word >> impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed parent cursor through actual index setup: " ^ name)
  end) (DB.thms "abiNativeStaticParentStart")
