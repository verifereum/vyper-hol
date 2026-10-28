(* TOP-LEVEL: a dynamic child in a mixed aggregate executes recursively,
   writes its actual head/cursor updates, and preserves completed output,
   unread source, cursor ownership and the enclosing execution invariant. *)
Theory abiNativeDynamicStoreStep
Ancestors
  abiNativeDynamicCall abiNativeDynamicStoreWrites abiNativeDynamicAdvance abiNativeDynamicBounds abiNativeDynamicReady
  abiNativeDynamicState abiNativeFields abiNativeFieldFlow abiNativeCursor abiNativeCursorStep abiNativeTraversal
  abiNativeEncodingDefs abiMemoryLeafRun abiMemoryFieldsState abiMemoryFieldsAdvance abiStateFrame
  abiAllocationWindows abiFieldLayoutDefs compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_store_step:
  !ctx func root_cs root_after source_id target_id initial reference full done payload fields dst src dyn_ptr
      dst_addr dyn_addr root_addr source_capacity source_offset info abi_sz mem_sz rest cs ret mid ss counter_inst.
    full = done ++ ((T,payload)::fields) /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,T)::rest) ((T,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss /\
    abi_native_fields ((info,abi_sz,mem_sz,T)::rest) (w2n root_addr + source_offset) reference ((T,payload)::fields) /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info T
      (abi_field_head_size done) dyn_ptr (abi_complex_field_cut src source_offset cs) = (ret,mid) /\
    fn_has_code cs mid func /\ cs_extends mid root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out.
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial mid out /\
      abi_native_cursor func root_cs root_after counter_inst dyn_addr mid out /\
      abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference rest
        (source_offset + mem_sz) (abi_field_head_size done + abi_sz) mid out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  qpat_x_assum `abi_native_fields (_::_) _ _ (_::_)`
    (strip_assume_tac o SIMP_RULE bool_ss [abi_native_fields_cons]) >>
  drule_all abi_native_dynamic_dynamic_call >> disch_then (qx_choose_then `out` strip_assume_tac) >>
  drule_all abi_native_dynamic_field_bounds >> simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_dynamic_call_ready >> simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule_all abi_native_field_compiler_flow >> strip_tac >>
  `alloca_inv initial /\ ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after)` by
    (qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ (abi_field_bytes _ _) _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`func`, `root_cs`, `root_after`, `counter_inst`, `dyn_addr`, `cs`, `ss`, `source_id`, `target_id`]
    mp_tac abi_native_cursor_root_distinct >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_field_head_size done <= LENGTH (abi_field_bytes (abi_field_head_size full) full) /\
    abi_field_head_size full + abi_field_tail_size done <= LENGTH (abi_field_bytes (abi_field_head_size full) full)` by
    (simp_tac bool_ss [abi_field_bytes_length] >> decide_tac) >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `counter_inst`, `cs`, `mid`, `ret`, `source_id`, `target_id`,
    `dst_addr`, `dyn_addr`, `root_addr`, `source_offset`, `source_capacity`, `mem_sz`, `abi_field_head_size done`,
    `abi_field_head_size full`, `abi_field_tail_size done`, `payload`,
    `abi_field_bytes (abi_field_head_size full) full`, `ss`, `out`]
    mp_tac abi_native_dynamic_dynamic_writes >> impl_tac >- asm_simp_tac bool_ss [ADD_ASSOC] >> strip_tac >>
  drule_all abi_native_dynamic_dynamic_advance >> DISCH_TAC >>
  `w2n dst_addr <= w2n (dst_addr + n2w (abi_field_head_size done)) /\
    w2n (dst_addr + n2w (abi_field_head_size done)) + 32 <=
      w2n dst_addr + LENGTH (abi_field_bytes (abi_field_head_size full) full)` by decide_tac >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `dst_addr`,
    `abi_field_bytes (abi_field_head_size full) full`, `initial`, `counter_inst`, `dyn_addr`, `cs`, `mid`, `ret`,
    `dst_addr + mload (w2n dyn_addr) ss`, `payload`, `w2n (dst_addr + n2w (abi_field_head_size done))`, `ss`, `out`]
    mp_tac abi_native_cursor_traversal_step >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `~out.vs_halted` by
    (qspecl_then [`ss`, `out`] mp_tac abi_state_frame_observables >> asm_simp_tac bool_ss []) >>
  qexists_tac `out` >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic field of actual mixed traversal: " ^ name)
  end) (DB.thms "abiNativeDynamicStoreStep")
