(* TOP-LEVEL: actual field calls in a mixed parent derive all child
   resources and parent-store separation from the enclosing state. Static
   calls also preserve the real parent cursor through recursive execution. *)
Theory abiNativeDynamicCall
Ancestors
  abiNativeDynamicBounds abiNativeDynamicReady abiNativeDynamicSeparation abiNativeDynamicState
  abiNativeStaticField abiNativeDynamicField abiNativeCursor abiNativeCursorFrame
  abiNativeTraversal abiNativeFieldFlow abiNativeEncodingDefs abiMemoryFieldsState abiFieldLayoutDefs
  compileAllocaProvenance compileIdFlow compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_static_call:
  !ctx func root_cs root_after source_id target_id initial reference full done payload fields dst src dyn_ptr
      dst_addr dyn_addr root_addr source_capacity source_offset info abi_sz mem_sz rest cs ret mid ss counter_inst.
    full = done ++ ((F,payload)::fields) /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss /\
    abi_native_encoder info (w2n root_addr + source_offset) mem_sz reference payload /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info F
      (abi_field_head_size done) dyn_ptr (abi_complex_field_cut src source_offset cs) = (ret,mid) /\
    fn_has_code cs mid func /\ cs_extends mid root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out. abi_native_encoding_result ctx func cs mid ret (dst_addr + n2w (abi_field_head_size done)) payload ss out /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule_all abi_native_dynamic_field_bounds >> simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_dynamic_call_ready >> simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_memory_fields_operands _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_memory_fields_operands_def]) >>
  drule_all abi_native_static_field >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >>
  `fn_inst_ids_distinct func /\ ~MEM source_id (compiler_alloca_ids root_cs root_after) /\
    ~MEM target_id (compiler_alloca_ids root_cs root_after)` by
    (qpat_assum `abi_native_memory_ready _ _ _ _ _ _ _ _ (abi_field_bytes _ _) _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  drule_all abi_native_cursor_root_distinct >> strip_tac >>
  `compiler_id_history cs` by
    (qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  drule_all abi_native_field_compiler_flow >> strip_tac >>
  `alloca_inv ss /\ abi_allocated_window ss target_id
    (w2n (dst_addr + n2w (abi_field_head_size done))) (LENGTH payload)` by
    (qpat_assum `abi_native_memory_ready _ _ _ _ _ (_ + n2w source_offset) _ _ _ ss`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_memory_ready_def]) >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`ctx`, `func`, `root_cs`, `root_after`, `counter_inst`, `dyn_addr`, `cs`, `ss`, `mid`, `ret`,
    `dst_addr + n2w (abi_field_head_size done)`, `payload`, `out`, `target_id`]
    mp_tac abi_native_cursor_static_read >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

Theorem abi_native_dynamic_dynamic_call:
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
    abi_native_encoder info (w2n root_addr + source_offset) mem_sz reference payload /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info T
      (abi_field_head_size done) dyn_ptr (abi_complex_field_cut src source_offset cs) = (ret,mid) /\
    fn_has_code cs mid func /\ cs_extends mid root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out.
      abi_encoding_result ctx func cs mid ret (dst_addr + mload (w2n dyn_addr) ss) payload
        (abi_allocation_windows (compiler_alloca_ids cs mid) out ++
          [(w2n (dst_addr + n2w (abi_field_head_size done)),32);(w2n dyn_addr,32)]) ss out /\
      abi_allocation_trace 32 (compiler_alloca_ids cs mid) ss out /\
      mload (w2n (dst_addr + n2w (abi_field_head_size done))) out = mload (w2n dyn_addr) ss /\
      mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH payload)
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule_all abi_native_dynamic_field_bounds >> simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_dynamic_call_ready >> simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_native_dynamic_call_store_regions >> strip_tac >>
  qpat_assum `abi_memory_fields_operands _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_memory_fields_operands_def]) >>
  drule_all abi_native_dynamic_field >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual mixed-parent recursive calls: " ^ name)
  end) (DB.thms "abiNativeDynamicCall")
