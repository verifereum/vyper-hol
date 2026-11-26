(* The nonword tuple-row unwrap is observed after the address phase. *)
Theory bodyAbiTupleRowRestoreMods
Ancestors
  abiEncodeValuesPrefixFrame abiEncodeValuesRun bodyAbiTupleBufferStateMods
  bodyAbiEncodeSavedMemoryMods bodyAbiEncodeSavedCodeMods bodyAbiEncodeSavedSlotMods
  bodyAbiEncodeRestoredInputMods bodyExtSavedRowInputMods
  localPtrsProps stateRelProj loweringStateRelDefs
  exprLowering exprLoweringProps loweringPosts compileEnv
  venomState venomInst finite_map list arithmetic

(* The payload and the cursor are registered separately at this cut. An
   unwrap keeps both allocations, even though its own result may be fresh. *)
Theorem tuple_unwrap_prefix_mods[local]:
  abi_encode_values_prefix_at ats avs hl dest cursor loc slot i a u Gu tu /\
  wb_frame ce ee ee a u z /\ ghost_kept_at lo ce ee a Gu tu u Gz tz /\
  ci_mono a c /\ stmt_state_rel H ctx func ce cx ee u /\
  stmt_state_rel H ctx func ce cx ee z /\ fn_inst_ids_distinct func /\
  MEM owner (fn_insts func) /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  FLOOKUP u.vs_allocas owner.inst_id = SOME (pbase,capacity) /\ owner.inst_id < a.cs_next_id /\
  MEM cur (fn_insts func) /\ cur.inst_id = loc /\ cur.inst_outputs = [cursor_var] /\
  not_local_ptr ce ee.scopes cursor_var /\
  pbase <= dest /\
  dest + LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) <= pbase+capacity /\
  dest + hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) <= pbase+capacity ==>
  abi_encode_values_prefix_at ats avs hl dest cursor loc slot i c z Gz tz
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee u`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee z`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `FLOOKUP u.vs_allocas cur.inst_id = SOME (slot,32)` by
    (qhdtm_assum `abi_encode_values_prefix_at` (strip_assume_tac o REWRITE_RULE[abi_encode_values_prefix_at_def]) >> simp[]) >>
  irule abi_encode_values_prefix_after_unwrap >>
  qhdtm_assum `abi_encode_values_prefix_at` (irule_at Any) >>
  qpat_assum `wb_frame ce ee ee a u z` (irule_at Any) >>
  qpat_assum `FLOOKUP u.vs_allocas owner.inst_id = SOME (pbase,capacity)` (irule_at Any) >>
  qexists `lo` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_tac >>
  pure_rewrite_tac[GSYM regions_disjoint_def] >>
  conj_tac
  >- (irule local_ptrs_rel_alloca_disjoint >>
      qpat_assum `FLOOKUP u.vs_allocas owner.inst_id = SOME (pbase,capacity)` (irule_at Any) >>
      qpat_assum `local_region ce ee.scopes u name p k` (irule_at Any) >>
      qpat_assum `owner.inst_outputs = [root]` (irule_at Any) >>
      qexists `func` >> asm_rewrite_tac[]) >>
  irule local_ptrs_rel_alloca_disjoint >>
  qpat_assum `FLOOKUP u.vs_allocas cur.inst_id = SOME (slot,32)` (irule_at Any) >>
  qpat_assum `local_region ce ee.scopes u name p k` (irule_at Any) >>
  qpat_assum `cur.inst_outputs = [cursor_var]` (irule_at Any) >>
  qexists `func` >> asm_rewrite_tac[]
QED

(* Only the codec interval is relevant to the window-input rule. Package
   that interval and the actual unwrap using the singleton compile equation;
   this does not execute a standalone encoder or its allocation/header. *)
Theorem tuple_unwrap_window_input_mods[local]:
  stmt_state_rel H ctx func ce cx ee z /\
  expr_val_at ce cx ty first last ee v src z /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
  expr_store_bound cx ty v src z /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  get_tenv cx SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==> type_memory_bytes ce t = type_memory_size v) /\
  MEM owner (fn_insts func) /\ owner.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  (owner.inst_id < first.cs_next_id \/ last.cs_next_id <= owner.inst_id) /\
  FLOOKUP z.vs_allocas owner.inst_id = SOME (pbase,capacity) /\
  pbase <= dest /\ dest + LENGTH (enc at av) <= pbase + capacity /\
  owner.inst_id < c.cs_next_id /\ last.cs_next_id <= c.cs_next_id /\
  local_ptrs_reserved ce c /\ unwrap_value ce saved a = (src,c) /\
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info ce.ce_struct_fields ce ty) c = (out,en) /\
  fn_has_code c en func /\ fn_inst_ids_distinct func ==>
  ?w ct rv.
    eval_operand src z = SOME w /\ op_taint tz src = {} /\ enc ct rv = enc at av /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
        ct rv (w2n w) (val_footprint tv v) mem) /\
    (0 < val_footprint tv v ==>
      w2n w + val_footprint tv v <= z.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (dest,LENGTH (enc at av)) /\
      ?p. src = Var p /\ ptr_covers Gz tz p z (val_footprint tv v)) /\
    (!inst r len. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids c en /\ FLOOKUP z.vs_allocas inst.inst_id = SOME (r,len) ==>
      len = 32 /\
      (0 < val_footprint tv v ==>
        venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (r,len)) /\
      venomMemDefs$regions_disjoint (dest,LENGTH (enc at av)) (r,len))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `compile_abi_encode_payload ce T [saved] [ty] dst a = (out,en)` by
    simp[compile_abi_encode_payload_def, comp_bind_def] >>
  qpat_x_assum `at = _` SUBST_ALL_TAC >>
  irule abi_encode_restored_window_input_mods >>
  qpat_assum `expr_val_at ce cx ty first last ee v src z` (irule_at Any) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee z` (irule_at Any) >>
  qpat_assum `compile_abi_encode_payload ce T [saved] [ty] dst a = (out,en)` (irule_at Any) >>
  qpat_assum `FLOOKUP z.vs_allocas owner.inst_id = SOME (pbase,capacity)` (irule_at Any) >>
  qpat_assum `owner.inst_outputs = [root]` (irule_at Any) >>
  qpat_assum `get_tenv cx SUBMAP E0` (irule_at Any) >>
  simp[]
QED
