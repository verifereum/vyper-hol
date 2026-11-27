Theory bodyExtPackingEndpointMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv vyperStorageFootprint abiEncoderWindowContract
  loweringPosts loweringStateRelDefs exprLoweringProps bodyPtrDefs
  venomState finite_map pred_set pair

(* The fixed input is (front,s,G,tn), just before the shared allocation.
   ret describes the enclosing function's return buffer, not the ABI
   destination pbase+32. Cursor registration and encoded bytes belong to
   abi_encode_values_prefix_at, not to this predicate. *)
Definition ext_packing_endpoint_mods_def:
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner pbase capacity root dst selector a u Gu tu <=>
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee u /\
       storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo ret ce cx ee Gu tu u /\
       immutable_frame_mods func ce cx ee u) /\
    alloca_history func u /\ window_alloca_growth s u /\
    ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts /\
    front.cs_next_var <= a.cs_next_var /\ front.cs_next_id <= owner /\
    owner < a.cs_next_id /\ FLOOKUP u.vs_allocas owner = SOME (pbase,capacity) /\
    not_fresh_at a root /\ not_fresh_at a dst /\
    lookup_var root u = SOME (n2w pbase) /\ FLOOKUP Gu root = SOME (pbase,capacity) /\
    ptr_covers Gu tu root u capacity /\
    lookup_var dst u = SOME (n2w (pbase+32)) /\ ptr_covers Gu tu dst u (capacity-32) /\
    read_memory (pbase+28) 4 u = selector /\
    (!i. pbase+28 <= i /\ i < pbase+32 ==> i NOTIN tu.t_mem) /\
    pure_frame ce func ee front s u /\ wb_frame ce ee ee front s u /\
    ghost_kept_at lo ce ee front G tn s Gu tu /\
    u.vs_labels = s.vs_labels /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_immutables = s.vs_immutables /\ u.vs_data_section = s.vs_data_section /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!b n. (b+n <= lo \/
            (?name p k. local_region ce ee.scopes s name p k /\ p <= b /\ b+n <= p+k) \/
            (?id p k. id < front.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (p,k) /\
                      p <= b /\ b+n <= p+k)) ==>
       mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory /\
       (!i. b <= i /\ i < b+n /\ i IN tu.t_mem ==> i IN tn.t_mem))
End

(* The horizon witness gives the allocation and conditional FMP resources
   via stmt_state_rel and ghost_inv_at_mods. The writeback and kept-ghost
   clauses preserve successful old variable observations and registrations;
   together with the subrange clause they also protect the old default cell.
   The return-buffer frame transports from front using the same writeback
   clause and window_alloca_growth. *)
