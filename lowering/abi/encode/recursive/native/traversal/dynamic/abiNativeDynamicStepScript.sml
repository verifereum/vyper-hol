(* TOP-LEVEL: either field kind advances the actual mixed traversal from
   its semantic child assertions, without assuming a recursive execution. *)
Theory abiNativeDynamicStep
Ancestors
  abiNativeDynamicStaticStep abiNativeDynamicStoreStep abiNativeDynamicState
  abiNativeCursor abiNativeTraversal abiNativeEncodingDefs abiMemoryFieldsState
  abiFieldLayoutDefs compileEnv venomState list words arithmetic

Theorem abi_native_dynamic_step:
  !ctx func root_cs root_after source_id target_id initial reference full dst src dyn_ptr dst_addr dyn_addr
      root_addr source_capacity info abi_sz mem_sz is_dyn rest source_offset head_offset cs ret mid ss counter_inst.
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_native_traversal ctx func root_cs root_after dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial cs ss /\
    abi_native_cursor func root_cs root_after counter_inst dyn_addr cs ss /\
    mem_bytes_at (w2n root_addr) source_capacity reference =
      mem_bytes_at (w2n root_addr) source_capacity initial.vs_memory /\
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      ((info,abi_sz,mem_sz,is_dyn)::rest) source_offset head_offset cs ss /\
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
      (abi_complex_field_cut src source_offset cs) = (ret,mid) /\
    fn_has_code cs mid func /\ cs_extends mid root_after /\
    ss.vs_current_bb = cs.cs_current_bb /\ ss.vs_inst_idx = LENGTH cs.cs_current_insts /\ ~ss.vs_halted ==>
    ?out.
      abi_native_traversal ctx func root_cs root_after dst_addr
        (abi_field_bytes (abi_field_head_size full) full) initial mid out /\
      abi_native_cursor func root_cs root_after counter_inst dyn_addr mid out /\
      abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference rest
        (source_offset + mem_sz) (head_offset + abi_sz) mid out /\
      out.vs_current_bb = mid.cs_current_bb /\ out.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~out.vs_halted
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_dynamic_current >>
  disch_then (qx_choose_then `done` (qx_choose_then `payload` (qx_choose_then `fields` strip_assume_tac))) >>
  qpat_x_assum `head_offset = _` SUBST_ALL_TAC >>
  qpat_assum `abi_native_dynamic_state _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (ASSUME_TAC o CONJUNCT1 o PURE_REWRITE_RULE [abi_native_dynamic_state_def]) >>
  Cases_on `is_dyn`
  >- (drule_all abi_native_dynamic_store_step >> simp_tac bool_ss []) >>
  drule_all abi_native_dynamic_static_step >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual native mixed traversal step: " ^ name)
  end) (DB.thms "abiNativeDynamicStep")
