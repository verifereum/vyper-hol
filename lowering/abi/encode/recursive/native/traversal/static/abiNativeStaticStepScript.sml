(* TOP-LEVEL: a complete static traversal step derives the actual recursive
   execution from the child induction assertion and advances both runtime
   layout and enclosing execution resources. No child run is assumed. *)
Theory abiNativeStaticStep
Ancestors
  abiNativeStaticState abiNativeStaticBounds abiNativeStaticReady abiNativeStaticAdvance abiNativeStaticSeparation
  abiNativeStaticField abiNativeFields abiNativeFieldFlow abiNativeTraversal abiNativeTraversalStep
  abiNativeEncodingDefs abiMemoryLeafRun abiMemoryFieldsState abiMemoryFieldsAdvance
  abiAllocationWindows abiFieldLayoutDefs compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_static_step:
  !ctx func root_cs root_after source_id target_id initial reference full dst src dst_addr root_addr source_capacity
      info abi_sz mem_sz is_dyn rest source_offset head_offset cs ret mid ss.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference
      ((info,abi_sz,mem_sz,is_dyn)::rest) source_offset head_offset cs ss /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset (Lit 0w)
      (abi_complex_field_cut src source_offset cs) = (ret,mid) /\
    fn_has_code cs mid func /\ cs_extends mid root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out.
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial mid out /\
      abi_native_static_state full dst src dst_addr root_addr source_capacity reference rest
        (source_offset + mem_sz) (head_offset + abi_sz) mid out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  drule abi_native_static_current >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choose_then `done` (qx_choose_then `payload` (qx_choose_then `fields` strip_assume_tac)))) >>
  qpat_x_assum `head_offset = _` SUBST_ALL_TAC >>
  `EVERY (\(is_dyn,bytes). ~is_dyn) full /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss` by
    (qpat_assum `abi_native_static_state _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_native_static_state_def]) >>
     conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `abi_memory_fields_operands _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_memory_fields_operands_def]) >>
  qpat_assum `abi_native_traversal _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_traversal_def]) >>
  drule_all abi_native_static_field_bounds >> strip_tac >>
  drule_all abi_native_static_call_ready >> strip_tac >>
  qpat_x_assum `abi_native_fields ((info,abi_sz,mem_sz,F)::rest) _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_fields_cons]) >>
  drule_all abi_native_static_field >>
  disch_then (qspec_then `ctx` (qx_choose_then `out` strip_assume_tac)) >>
  qpat_assum `abi_native_encoding_result _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_encoding_result_def]) >>
  drule_all abi_native_field_compiler_flow >> strip_tac >>
  `abi_field_head_size done <= LENGTH (abi_field_bytes (abi_field_head_size full) full)` by decide_tac >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr`, `root_addr`, `source_offset`, `source_capacity`,
    `mem_sz`, `abi_field_head_size done`, `payload`, `abi_field_bytes (abi_field_head_size full) full`,
    `ss`, `out`, `source_id`, `target_id`] mp_tac abi_native_static_separation >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`ctx`, `func`, `full`, `done`, `fields`, `dst`, `src`, `dst_addr`, `root_addr`,
    `source_capacity`, `reference`, `info`, `abi_sz`, `mem_sz`, `rest`, `source_offset`,
    `cs`, `mid`, `ret`, `payload`, `abi_allocation_windows (compiler_alloca_ids cs mid) out`, `ss`, `out`]
    mp_tac abi_native_static_advance >> impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `alloca_inv initial` by fs[abi_native_memory_ready_def] >>
  drule_all abi_native_traversal_native_step >> DISCH_TAC >>
  drule_all abi_native_encoding_not_halted >> DISCH_TAC >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  qexists_tac `out` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native static traversal step: " ^ name)
  end) (DB.thms "abiNativeStaticStep")
