(* Fixed-endpoint linked buffer entry for the ABI payload continuations. *)
Theory bodyAbiEncodeSetupBufferMods
Ancestors
  bodyAbiTupleBufferStateMods bodyMemoryDefs bodyFullPostsMods bodyPtrDefs
  typedMemoryCopy loweringStateRelDefs exprLoweringProps compileEnv
  venomState venomMemDefs finite_map pred_set list pair words

Theorem abi_encode_setup_buffer_mods:
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee pre /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre /\
     immutable_frame_mods func ce cx ee pre) /\
  return_buf_frame d ce ready pre /\
  wb_frame ce ee ee st s pre /\
  ghost_kept_at lo ce ee st G tn s Gpre tnpre /\
  alloca_history func pre /\
  lo <= s.vs_alloca_next /\
  s.vs_alloca_next <= pre.vs_alloca_next /\
  ~pre.vs_halted /\
  pre.vs_current_bb = ready.cs_current_bb /\
  pre.vs_inst_idx = LENGTH ready.cs_current_insts /\
  st.cs_next_var <= ready.cs_next_var /\
  st.cs_next_id < ready.cs_next_id /\
  not_fresh_at ready root /\
  not_fresh_at ready dp /\
  eval_operand (Var root) pre = SOME (n2w p) /\
  ptr_covers Gpre tnpre root pre N /\
  eval_operand (Var dp) pre = SOME (n2w (p+dst_offset)) /\
  ptr_covers Gpre tnpre dp pre (N-dst_offset) /\
  FLOOKUP pre.vs_allocas st.cs_next_id = SOME (p,N) /\
  LENGTH prefix <= dst_offset /\
  dst_offset <= N /\
  read_memory (p+dst_offset-LENGTH prefix) (LENGTH prefix) pre = prefix /\
  (!i. p+dst_offset-LENGTH prefix <= i /\
       i < p+dst_offset ==> i NOTIN tnpre.t_mem) /\
  pre.vs_accounts = s.vs_accounts /\
  pre.vs_transient = s.vs_transient /\
  pre.vs_call_ctx = s.vs_call_ctx /\
  pre.vs_immutables = s.vs_immutables /\
  pre.vs_data_section = s.vs_data_section /\
  tnpre.t_stor = tn.t_stor /\
  tnpre.t_trans = tn.t_trans /\
  tnpre.t_imm = tn.t_imm /\
  (!b n. ((b = 0 /\ n = lo) \/
          (?name. local_region ce ee.scopes s name b n) \/
          (?aid. aid < st.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
    (b+n <= p+32 \/ p+32+write_len <= b)) /\
  (!a n. a+n <= p+32 \/ p+32+write_len <= a ==>
     mem_bytes_at a n pre.vs_memory = mem_bytes_at a n s.vs_memory) /\
  (!i. i < s.vs_alloca_next /\
       i IN tnpre.t_mem ==> i IN tn.t_mem) /\
  (!b n. ((b = 0 /\ n = lo) \/
          (?name. local_region ce ee.scopes s name b n) \/
          (?aid. aid < st.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
    (mem_bytes_at b n pre.vs_memory = mem_bytes_at b n s.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tnpre.t_mem ==> i IN tn.t_mem))) ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d st s G tn
    st.cs_next_id p N root dp dst_offset prefix ready pre Gpre tnpre
Proof
  strip_tac >> simp[abi_tuple_buffer_state_mods_def] >> conj_tac
  >- metis_tac[]
  >- metis_tac[]
QED
