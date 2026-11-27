(* Linked ABI tuple buffer, anchored at the saved-operand observation. *)
Theory bodyAbiTupleBufferStateMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs loweringPosts
  abiEncoderWindowContract abiEncoderRegisteredEffect exprSimAbiEncodeExecFrame
  exprLoweringProps compileEnv memoryReadProps ptrDiscipline valueEncodingDefs
  loweringStateRelDefs venomState venomInst words finite_map pred_set list pair

(* se,s,G,tn describe the saved observation; a,u,Gu,tu describe the live cut.
   The owner and the payload pointer may be the same operand. The cursor
   allocation belongs to the loop, not to this entry state. *)
Definition abi_tuple_buffer_state_mods_def[nocompute]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu <=>
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\
      immutable_frame_mods func ce cx ee u) /\
    return_buf_frame d ce a u /\
    wb_frame ce ee ee se s u /\ ghost_kept_at lo ce ee se G tn s Gu tu /\
    alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
    u.vs_inst_idx = LENGTH a.cs_current_insts /\
    se.cs_next_var <= a.cs_next_var /\ se.cs_next_id <= shared /\ shared < a.cs_next_id /\
    not_fresh_at a root /\ not_fresh_at a dst /\
    eval_operand (Var root) u = SOME (n2w pbase) /\ ptr_covers Gu tu root u capacity /\
    eval_operand (Var dst) u = SOME (n2w (pbase+dst_offset)) /\
    ptr_covers Gu tu dst u (capacity-dst_offset) /\
    FLOOKUP u.vs_allocas shared = SOME (pbase,capacity) /\
    LENGTH prefix <= dst_offset /\ dst_offset <= capacity /\
    read_memory (pbase+dst_offset-LENGTH prefix) (LENGTH prefix) u = prefix /\
    (!i. pbase+dst_offset-LENGTH prefix <= i /\ i < pbase+dst_offset ==> i NOTIN tu.t_mem) /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
    u.vs_data_section = s.vs_data_section /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!b n. ((b = 0 /\ n = lo) \/
            (?name. local_region ce ee.scopes s name b n) \/
            (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
      mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory /\
      (!i. b <= i /\ i < b+n /\ i IN tu.t_mem ==> i IN tn.t_mem))
End

(* outs records only the written payload slices, not the entire owner.
   The cursor may be initialized here, or may have been registered at an
   earlier cut. Other sites are ALLOCAs emitted in this compiler interval.
   Only the registered extent (if any) of each site permits effects. *)
Definition abi_tuple_row_effects_mods_def[nocompute]:
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c z Gz tz <=>
    ci_mono a c /\ window_alloca_growth u z /\ abi_encode_exec_frame func u z /\
    (!x. not_fresh_at a x ==>
      (!w. lookup_var x u = SOME w ==> lookup_var x z = SOME w) /\
      FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
    tz.t_stor = tu.t_stor /\ tz.t_trans = tu.t_trans /\ tz.t_imm = tu.t_imm /\
    ?ids outs.
      shared NOTIN ids /\
      EVERY (\(b,n). pbase+dst_offset <= b /\ b+n <= pbase+capacity) outs /\
      (cursor_site IN ids ==>
        cursor_site < c.cs_next_id /\ ?slot. FLOOKUP z.vs_allocas cursor_site = SOME (slot,32)) /\
      (!aid. aid IN ids ==>
        (aid <> cursor_site ==> a.cs_next_id <= aid /\ aid < c.cs_next_id) /\
        ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
      abi_encoder_registered_effect ids outs u z /\
      (!i. EVERY (\(b,n). i < b \/ b+n <= i) outs /\
        (!aid b n. aid IN ids /\ FLOOKUP z.vs_allocas aid = SOME (b,n) ==>
          i < b \/ b+n <= i) /\ i IN tz.t_mem ==> i IN tu.t_mem)
End
