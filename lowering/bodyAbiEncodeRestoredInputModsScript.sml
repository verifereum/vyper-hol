Theory bodyAbiEncodeRestoredInputMods
Ancestors
  abiEncodeValuesSource bodyFullAbiEncodeNonwordWindow
  abiEncoderWindow exprLowering loweringPosts loweringStateRelDefs
  compileEnv context vyperContext vyperABI vyperValue vyperTyping contractABI
  fragExec bodyPtrDefs ptrDiscipline venomMemDefs venomState words finite_map list

(* The source interval is the saved operand's original interval on an
   identity unwrap, and the actual unwrap interval on a materializing unwrap. *)
Theorem abi_encode_restored_window_input_mods:
  stmt_state_rel H ctx func ce cx ee z /\
  expr_val_at ce cx ty first last ee v src z /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src G tn z /\
  expr_store_bound cx ty v src z /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  bytes = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
  get_tenv cx SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  MEM owner (fn_insts func) /\ owner.inst_outputs = [x] /\
  not_local_ptr ce ee.scopes x /\
  (owner.inst_id < first.cs_next_id \/ last.cs_next_id <= owner.inst_id) /\
  FLOOKUP z.vs_allocas owner.inst_id = SOME (b,sz) /\
  b <= d /\ d + LENGTH bytes <= b + sz /\ owner.inst_id < st.cs_next_id /\
  last.cs_next_id <= st.cs_next_id /\ local_ptrs_reserved ce st /\
  compile_abi_encode_payload ce T [saved] [ty] dst ready = (out,en) /\
  unwrap_value ce saved ready = (src,st) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func ==>
  ?w at rv.
    eval_operand src z = SOME w /\ op_taint tn src = {} /\ enc at rv = bytes /\
    (!mem. mem_agree_outside tn.t_mem z.vs_memory mem ==>
      abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
        at rv (w2n w) (val_footprint tv v) mem) /\
    (0 < val_footprint tv v ==>
      w2n w + val_footprint tv v <= z.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (d,LENGTH bytes) /\
      ?p. src = Var p /\ ptr_covers G tn p z (val_footprint tv v)) /\
    (!inst r len. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st en /\ FLOOKUP z.vs_allocas inst.inst_id = SOME (r,len) ==>
      len = 32 /\
      (0 < val_footprint tv v ==>
        venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (r,len)) /\
      venomMemDefs$regions_disjoint (d,LENGTH bytes) (r,len))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `compile_abi_encode_to_buf dst src
      (type_to_abi_enc_info ce.ce_struct_fields ce ty) st = (out,en)` by
    (qpat_x_assum `compile_abi_encode_payload _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_abi_encode_payload_def, comp_bind_def]) >>
  drule_all abi_encode_values_memory_source >> strip_tac >>
  drule_all abi_encode_uniform_translated_footprint_window >> strip_tac >>
  `eval_operand src z = SOME (n2w (w2n w))` by simp[] >>
  `(0 < val_footprint tv v ==> w2n w + val_footprint tv v <= z.vs_alloca_next)` by
    (strip_tac >> first_x_assum drule >> simp[]) >>
  qexistsl [`w`,`ct`,`rv`] >> asm_rewrite_tac[n2w_w2n] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_scratch_separation >> simp[]
QED
