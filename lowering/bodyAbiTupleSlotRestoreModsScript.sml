(* Select the storage/transient saved-slot restore at the reached tuple cut. *)
Theory bodyAbiTupleSlotRestoreMods
Ancestors
  bodyAbiTupleCaptureMods bodyAbiEncodeSavedSlotMods bodyAbiTupleBufferStateMods
  bodyAbiEncodePackedPostMods bodyAbiTupleSlotUnwrapShapeMods bodyFullPostsMods
  bodyFullShadowBodyInv exprPtrUnwrapStorageLayout exprPtrUnwrapEnsureShape
  exprPtrUnwrapAllocation exprSimOperands exprLowering exprLoweringProps
  bodyMemoryDefs loweringPosts compileEnv loweringStateRelDefs
  vyperStorageFootprint venomState venomInst finite_map list arithmetic pred_set
Libs horizonTypeLib


Theorem abi_tuple_slot_restore_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin se e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s) /\
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!l. vv_operand saved <> Label l) /\
  unwrap_value ce saved a = (src,c) /\ fn_has_code a c func /\
  saved = LocatedValue (lowered_value_type ce e) p /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\
  storage_trace_domain cx st0 ee.storage_trace /\ fn_inst_ids_distinct func ==>
  ?z Gz tz inst szw out mid b n.
    expr_val_at ce cx (lowered_value_type ce e) a c ee v src z /\
    expr_val_rel cx (lowered_value_type ce e) v src z /\
    ptr_val_ok cx (lowered_value_type ce e) v src Gz tz z /\
    expr_store_bound cx (lowered_value_type ce e) v src z /\
    src = Var out /\ not_fresh_at c out /\
    eval_operand src z = SOME (n2w b) /\ op_taint tz src = {} /\
    ptr_covers Gz tz out z n /\ b+n <= z.vs_alloca_next /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = a.cs_next_id /\ a.cs_next_id < c.cs_next_id /\
    inst.inst_operands = [Lit szw] /\ inst.inst_outputs = [out] /\
    not_local_ptr ce ee.scopes out /\
    exec_alloca inst u szw = OK mid /\ copy_static z = copy_static mid /\
    FLOOKUP z.vs_allocas a.cs_next_id = SOME (b,n) /\ lo <= b /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!aid pair. FLOOKUP u.vs_allocas aid = SOME pair ==>
      FLOOKUP z.vs_allocas aid = SOME pair) /\
    (!off len. off+len <= b \/ b+n <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    (!i. i < b \/ b+n <= i ==> i IN tz.t_mem ==> i IN tu.t_mem) /\
    (!x. not_fresh_at a x ==>
      lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)) /\
    tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = c.cs_current_bb /\
    z.vs_inst_idx = LENGTH c.cs_current_insts /\ return_buf_frame d ce c z /\
    wb_frame ce ee ee a u z /\ ghost_kept_at lo ce ee a Gu tu u Gz tz /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    abi_tuple_saved_capture_transport_mods >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_row_mods_def]) >>
  `~is_word_type (lowered_value_type ce e)` by
    (qpat_x_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
     qpat_assum `saved = LocatedValue _ _` (fn th => simp[th]) >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx origin a e saved v si sm ss vv copy H ee Gu tu u /\
    stmt_state_rel H ctx func ce cx ee u /\ immutable_frame_mods func ce cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> asm_rewrite_tac[]) >>
  `si.cs_next_var <= sm.cs_next_var` by
    (drule (cj 1 compile_expr_grows) >> strip_tac >> decide_tac) >>
  `si.cs_next_var <= a.cs_next_var` by
    (irule LESS_EQ_TRANS >> qexists `sm.cs_next_var` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  drule_all abi_encode_saved_slot_restore_packet_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`z`,`Gz`,`tz`,`w`,`out`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `src = Var out` SUBST_ALL_TAC >>
  `out = STRING #"%" (toString a.cs_next_var) /\
    not_local_ptr ce ee.scopes out` by
    (qpat_x_assum `saved = LocatedValue _ _` SUBST_ALL_TAC >>
     irule abi_tuple_slot_unwrap_output_mods >>
     conj_tac
     >- (qexistsl [`c`,`p`,`lowered_value_type ce e`] >> simp[])
     >- (qexists `si` >> simp[])) >>
  qpat_x_assum `?mid. exec_alloca _ _ _ = OK mid /\ _`
    (qx_choose_then `mid` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`z`,`Gz`,`tz`,
    `mk_inst a.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [out]`,
    `n2w (type_memory_size rt)`,`out`,`mid`,`w2n w`,`type_memory_size rt`] >>
  asm_rewrite_tac[mk_inst_def] >> simp[]
QED
