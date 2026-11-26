(* Observe the dynamic input at the fixed restored exit. The scratch
   separation concerns only the following codec interval. *)
Theory bodyAbiTupleDynamicRestoreInputMods
Ancestors
  bodyAbiEncodeRestoredInputMods abiEncoderWindow exprLowering
  loweringPosts loweringStateRelDefs bodyPtrDefs compileEnv
  vyperABI vyperContext vyperTyping vyperValue contractABI
  fragExec venomState venomInst venomMemDefs finite_map list words

Theorem abi_tuple_dynamic_restore_input_mods:
  stmt_state_rel H ctx func ce cx ee s /\
  expr_val_at ce cx ty first last ee v src s /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_val_rel cx ty v src s /\ ptr_val_ok cx ty v src G tn s /\
  expr_store_bound cx ty v src s /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ bytes = enc at av /\
  get_tenv cx SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  MEM owner (fn_insts func) /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  (owner.inst_id < first.cs_next_id \/ last.cs_next_id <= owner.inst_id) /\
  FLOOKUP s.vs_allocas owner.inst_id = SOME (pbase,capacity) /\
  pbase <= pbase+dst_offset+off /\ pbase+dst_offset+off + LENGTH bytes <= pbase+capacity /\
  owner.inst_id < ready.cs_next_id /\ last.cs_next_id <= ready.cs_next_id /\
  local_ptrs_reserved ce ready /\
  unwrap_value ce saved prep = (src,ready) /\
  compile_abi_encode_to_buf (Var tp) src (type_to_abi_enc_info ce.ce_struct_fields ce ty)
    ready = (len,mid) /\
  fn_has_code ready mid func /\ fn_inst_ids_distinct func /\
  (!x. src = Var x ==> not_fresh_at ready x) ==>
  ?sb.
    eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\
    (!x. src = Var x ==> not_fresh_at ready x) /\
    (?ct rv. enc ct rv = enc at av /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
          ct rv sb (val_footprint tv v) mem) /\
    (0 < val_footprint tv v ==> sb + val_footprint tv v <= s.vs_alloca_next /\
      venomMemDefs$regions_disjoint (sb,val_footprint tv v) (pbase+dst_offset+off,LENGTH (enc at av)) /\
      ?p. src = Var p /\ ptr_covers G tn p s (val_footprint tv v)) /\
    (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
      sz = 32 /\ (0 < val_footprint tv v ==> venomMemDefs$regions_disjoint (sb,val_footprint tv v) (p,sz)) /\
      venomMemDefs$regions_disjoint (pbase+dst_offset+off,LENGTH (enc at av)) (p,sz))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `at = _` SUBST_ALL_TAC >>
  `compile_abi_encode_payload ce T [saved] [ty] (Var tp) prep = (len,mid)` by
    simp[compile_abi_encode_payload_def, comp_bind_def] >>
  drule_all (Q.INST [`d` |-> `pbase+dst_offset+off`] abi_encode_restored_window_input_mods) >>
  disch_then (qx_choosel_then [`w`,`ct`,`rv`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `w2n w` >>
  qpat_x_assum `bytes = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[n2w_w2n] >>
  qexistsl [`ct`,`rv`] >> asm_rewrite_tac[]
QED
