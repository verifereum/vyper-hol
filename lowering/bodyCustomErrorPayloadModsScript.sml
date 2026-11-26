(* Before the terminal ADD, the allocation contains the selector followed
   by the tuple bytes. The row supplier works at the actual loop cursor. *)
Theory bodyCustomErrorPayloadMods
Ancestors
  bodyFullExtCallDirectStart bodyFullExtCallDirectState
  bodyAbiEncodeTuplePayloadMods fragGasOriginPtrLoop exprLoweringProps
  selectorCompilerProps reasonCopySourcePtr allocaSiteResource stateRelProj
  memoryReadProps vyperABI venomState words arithmetic finite_map list pair

Theorem custom_payload_data[local]:
  LENGTH arg_types = LENGTH vs ==>
  build_custom_error_data tenv name arg_types vs =
    build_ext_calldata tenv name arg_types vs
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `TAKE (LENGTH vs) arg_types = arg_types` by simp[TAKE_LENGTH_ID_rwt] >>
  simp[build_custom_error_data_def, build_ext_calldata_def]
QED

(* Convert the allocation/selector/ADD landing into the shared loop entry. *)
Theorem custom_payload_saved_start[local]:
  compile_alloc_buffer n se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (calldata_method_id selector)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand;Lit 32w] sm = (dst,st) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\ fn_has_code sm st func /\
  fn_inst_ids_distinct func /\ LENGTH selector = 4 /\ 32 <= n /\ n < dimword (:256) /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?r p (w:256 word) u Gu tu inst.
    ba.buf_operand = Var r /\ dst = Var p /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [r] /\
    not_local_ptr ce ee.scopes r /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id (w2n w) n r p 32 selector st u Gu tu /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all extcall_direct_request_start >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`r`,`p`,`w`,`u`,`Gu`,`tu`,`inst`] strip_assume_tac)) >>
  `ci_mono se sb` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono sb sm` by metis_tac[ci_mono_emit_void, SND] >>
  `ci_mono sm st` by metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono se st` by metis_tac[ci_mono_trans] >>
  qexistsl [`r`,`p`,`w`,`u`,`Gu`,`tu`,`inst`] >>
  drule_then (fn th => pure_rewrite_tac[th]) abi_encode_saved_state_extcall >>
  fs[extcall_direct_state_def, ci_mono_def, eval_operand_def] >>
  qpat_assum `dst = Var p` (fn th =>
    qpat_assum `eval_operand dst u = SOME _`
      (mp_tac o PURE_REWRITE_RULE [th,eval_operand_def])) >> simp[]
QED

Theorem custom_payload_observe[local]:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id (w2n w) n r p 32 selector en q Gq tq /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  LENGTH selector = 4 /\ 32 + LENGTH bytes <= n /\
  mem_bytes_at (w2n w + 32) (LENGTH bytes) q.vs_memory = bytes ==>
  lookup_var r q = SOME w /\ ptr_covers Gq tq r q (32 + LENGTH bytes) /\
  w2n w + 32 + LENGTH bytes <= q.vs_alloca_next /\
  q.vs_alloca_next < dimword (:256) /\
  read_memory (w2n w + 28) (4 + LENGTH bytes) q = selector ++ bytes /\
  allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
  ~q.vs_halted /\ q.vs_current_bb = en.cs_current_bb /\
  q.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_x_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `w2n w + n <= q.vs_alloca_next` by
    (irule alloca_site_registered_below >>
     qpat_assum `FLOOKUP q.vs_allocas _ = SOME (_,n)` (irule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `w2n w + 32 + LENGTH bytes <= q.vs_alloca_next` by decide_tac >>
  `w2n w + 32 - 4 = w2n w + 28 /\ w2n w + 28 + 4 = w2n w + 32` by decide_tac >>
  `read_memory (w2n w + 28) 4 q = selector` by
    (qpat_assum `w2n w + 32 - 4 = w2n w + 28` (fn addr =>
       qpat_assum `LENGTH selector = 4` (fn len =>
         qpat_assum `read_memory _ (LENGTH selector) q = selector`
           (ACCEPT_TAC o PURE_REWRITE_RULE [len,addr])))) >>
  `read_memory (w2n w + 32) (LENGTH bytes) q = bytes` by
    simp[read_memory_eq_mem_bytes_at] >>
  `read_memory (w2n w + 28) (4 + LENGTH bytes) q = selector ++ bytes` by
    (once_rewrite_tac[read_memory_split] >> asm_rewrite_tac[]) >>
  fs[eval_operand_def] >>
  conj_tac >- (irule ptr_covers_mono >>
               qpat_assum `ptr_covers Gq tq r q n` (irule_at Any) >> simp[]) >>
  irule alloca_room_next_lt >> qpat_assum `alloca_room ctx func q` (irule_at Any)
QED

Theorem custom_error_payload_buffer_mods:
  ~NULL saved /\
  LENGTH (MAP SND params) = LENGTH vs /\
  selector = function_selector (SND id) (vyper_to_abi_types (get_tenv cx) (MAP SND params)) /\
  build_ext_calldata (get_tenv cx) (SND id) (MAP SND params) vs = SOME (selector ++ bytes) /\
  32 + LENGTH bytes <= n /\ n < dimword (:256) /\
  compile_alloc_buffer n se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (calldata_method_id selector)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand;Lit 32w] sm = (dst,st) /\
  compile_abi_encode_values_to_buf ce dst (ZIP (saved,tys)) st = (payload_len,en) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\
  fn_has_code sm st func /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) (ZIP (saved,tys)) ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ hl = head_lengths ats 0 /\
  (!r p (w:256 word). ba.buf_operand = Var r /\ dst = Var p ==>
    !ci k. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
      ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [k] /\
      not_local_ptr ce ee.scopes k ==>
      !i a c v Gv tv cursor slot.
        i < LENGTH (ZIP (saved,tys)) /\
        abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
          se.cs_next_id (w2n w) n r p 32 selector a v Gv tv /\
        abi_encode_values_prefix_at ats avs hl (w2n w + 32)
          cursor st.cs_next_id slot i a v Gv tv /\
        compile_abi_encode_value_rows ce (Var p) cursor
          (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND)
            (TAKE i (ZIP (saved,tys))))) [EL i (ZIP (saved,tys))] a = ((),c) /\
        fn_has_code a c func ==>
        ?z Gz tz.
          abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
            se.cs_next_id (w2n w) n r p 32 selector c z Gz tz /\
          abi_encode_values_prefix_at ats avs hl (w2n w + 32)
            cursor st.cs_next_id slot (SUC i) c z Gz tz /\
          !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
            (v,Gv,tv) [] (OK z,Gz,tz)) ==>
  ?r w q Gq tq.
    ba.buf_operand = Var r /\
    build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs = SOME (selector ++ bytes) /\
    eval_operand payload_len q = SOME (n2w (LENGTH bytes)) /\
    op_taint tq payload_len = {} /\
    (!x. payload_len = Var x ==> not_fresh_at en x) /\
    lookup_var r q = SOME w /\ ptr_covers Gq tq r q (32 + LENGTH bytes) /\
    w2n w + 32 + LENGTH bytes <= q.vs_alloca_next /\
    q.vs_alloca_next < dimword (:256) /\
    read_memory (w2n w + 28) (4 + LENGTH bytes) q = selector ++ bytes /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    ~q.vs_halted /\ q.vs_current_bb = en.cs_current_bb /\
    q.vs_inst_idx = LENGTH en.cs_current_insts /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gq,tq)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH selector = 4` by simp[function_selector_length] >>
  `32 <= n` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  drule_all custom_payload_saved_start >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`r`,`p`,`w`,`u`,`Gu`,`tu`,`inst`] strip_assume_tac)) >>
  qpat_x_assum `!r p w. ba.buf_operand = Var r /\ _ ==> _`
    (qspecl_then [`r`,`p`,`w`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qpat_assum `dst = Var p` (fn th =>
    qpat_x_assum `compile_abi_encode_values_to_buf ce dst _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [th])) >>
  drule_all abi_encode_tuple_payload_mods >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`] strip_assume_tac) >>
  drule_all custom_payload_observe >> strip_tac >>
  drule_then (fn th => PURE_ONCE_REWRITE_TAC [th]) custom_payload_data >>
  qexistsl [`r`,`w`,`q`,`Gq`,`tq`] >> asm_rewrite_tac[] >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl [`Gu`,`u`,`tu`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
