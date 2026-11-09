(* Caller allocation, size-prefix and successful return decoding. *)
Theory extcallReturnCallerSuccess
Ancestors
  extcallReturnUnifiedCounted extcallReturnEntryBridge extcallReturnFrameBridge
  extcallReturnDecoderLabels loweringHalt
  abiReturnSize abiBoundaryChecks abiDecoderCoherence abiReturnPrefixTransport
  abiMalformedRecursiveInterface abiMalformedSiteFrame abiValidAllocatedContract
  exprLoweringProps exprSimWordArgs placeMemoryPrimitiveForward fragExec fragGasSeq fragGasMode
  compileEnv venomState venomInst venomExecSemantics exprLowering emitHelper emitHelperProps
  builtinSimple context arithmetic list rich_list finite_map words

Theorem return_size_counted:
  compile_return_value_decode lo cap a = (hi,b) /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  run_inst_seq (emitted_insts a b) s = OK t ==>
  gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH b.cs_current_insts))
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> GAS) (emitted_insts a b)` by
    (qpat_x_assum `compile_return_value_decode _ _ _ = _` mp_tac >>
     simp[compile_return_value_decode_def, compile_select_def,
          comp_bind_def, comp_ignore_bind_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pure_rewrite_tac[emitted_insts_def] >>
     simp_tac (srw_ss()) [] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule abi_return_size_code >> strip_tac >>
  irule straight_line_zero_gas_path >>
  fs[same_blocks_def, EVERY_MEM] >> metis_tac[]
QED

Theorem return_allocated_counted_entry:
  compile_alloc_buffer n a = (buf,m) /\
  compile_return_value_decode lo cap m = (hi,st) /\
  cs_extends st en /\ fn_has_code a en func /\
  stmt_state_rel ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce a /\ n < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  safe_operand a base_op /\ eval_operand base_op s = SOME (n2w B) /\
  B + cap < dimword (:256) /\
  FLOOKUP s.vs_allocas live = SOME (B,bufsz) /\ cap <= bufsz /\
  live < a.cs_next_id /\
  mem_bytes_at B (LENGTH (TAKE cap bs)) s.vs_memory = TAKE cap bs /\
  lo < dimword (:256) /\ cap < dimword (:256) /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\ lo <= LENGTH bs /\
  (!aid. aid IN sites ==> st.cs_next_id <= aid) ==>
  ?r u d. gas_marked_path F ctx func s 0 (OK r) /\
    abi_return_decode_ready ctx func ce cx ee m sites a.cs_next_id live
      base_op buf.buf_operand B cap bs d n r /\
    gas_marked_path F ctx func r 0 (OK u) /\
    abi_malformed_entry ctx func ce cx ee st sites a.cs_next_id live
      base_op hi (Lit 0w) buf.buf_operand B (LENGTH (TAKE cap bs))
      (TAKE cap bs) 0 d n u /\
    (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    u = r with <|vs_vars := u.vs_vars;
                 vs_inst_idx := LENGTH st.cs_current_insts|> /\
    (!x. not_fresh_at m x ==> lookup_var x u = lookup_var x r) /\
    ~u.vs_halted /\ u.vs_current_bb = st.cs_current_bb /\
    u.vs_inst_idx = LENGTH st.cs_current_insts
Proof
  strip_tac >>
  `cs_extends a m` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >> gvs[] >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `cs_extends m st` by
    (drule abi_return_size_code >> simp[same_blocks_def, cs_extends_def] >>
     metis_tac[IS_PREFIX_APPEND]) >>
  `m.cs_next_id <= st.cs_next_id` by
    (mp_tac (Q.SPECL [`lo`, `cap`, `m`] ci_mono_compile_return_value_decode) >>
     simp[ci_mono_def]) >>
  `fn_has_code a m func /\ fn_has_code m st func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!aid. aid IN sites ==> m.cs_next_id <= aid` by metis_tac[LESS_EQ_TRANS] >>
  drule_all return_allocated_decode_ready >>
  disch_then (qx_choose_then `r` (qx_choose_then `d` strip_assume_tac)) >>
  `r.vs_returndata = bs` by
    (qpat_x_assum `(r with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|>) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule_all return_decode_ready_entry >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `gas_marked_path F ctx func r 0
     (OK (u with vs_inst_idx := LENGTH st.cs_current_insts))` by
    (irule return_size_counted >> metis_tac[]) >>
  `m.cs_current_bb = st.cs_current_bb` by
    metis_tac[abi_return_size_code, same_blocks_def] >>
  qexistsl_tac [`r`, `u with vs_inst_idx := LENGTH st.cs_current_insts`, `d`] >>
  simp[] >>
  qpat_assum `u = r with vs_vars := _` SUBST1_TAC >> simp[] >>
  fs[lookup_var_def] >> metis_tac[]
QED

Theorem return_allocated_counted_decode:
  compile_alloc_buffer n a = (buf,m) /\
  compile_return_value_decode lo cap m = (hi,st) /\
  compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  n = type_memory_bytes ce rt /\ cs_extends st en /\
  fn_has_code a en func /\ fn_inst_ids_distinct func /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce a /\
  n < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  safe_operand a base_op /\ eval_operand base_op s = SOME (n2w B) /\
  B + cap < dimword (:256) /\
  FLOOKUP s.vs_allocas live = SOME (B,bufsz) /\ cap <= bufsz /\
  live < a.cs_next_id /\
  mem_bytes_at B (LENGTH (TAKE cap bs)) s.vs_memory = TAKE cap bs /\
  lo < dimword (:256) /\ cap < dimword (:256) /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\ lo <= LENGTH bs /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  rv = (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ty bs = INL v /\
  abi_decoder_coherent ce env sf rt tv ==>
  ?r u d ceiling z.
    gas_marked_path F ctx func s 0 (OK z) /\
    abi_return_decode_ready ctx func ce cx ee m
      (abi_malformed_scratch_sites st en func) a.cs_next_id live
      base_op buf.buf_operand B cap bs d n r /\
    abi_malformed_entry ctx func ce cx ee st
      (abi_malformed_scratch_sites st en func) a.cs_next_id live
      base_op hi (Lit 0w) buf.buf_operand B (LENGTH (TAKE cap bs))
      (TAKE cap bs) 0 d n u /\
    (!x. not_fresh_at a x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    u = r with <|vs_vars := u.vs_vars;
                 vs_inst_idx := LENGTH st.cs_current_insts|> /\
    (!x. not_fresh_at m x ==> lookup_var x u = lookup_var x r) /\
    z.vs_fmp = u.vs_fmp /\
    abi_malformed_resource_post ctx func ce cx ee st.cs_next_var
      (abi_malformed_scratch_sites st en func) a.cs_next_id u z /\
    val_in_memory tv rv d z.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d n u z /\
    fresh_vars_wrt ceiling z /\
    (!aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP u.vs_allocas aid = SOME (b,sz) \/ u.vs_alloca_next <= b) /\
    ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `n = _` SUBST_ALL_TAC >>
  `!aid. aid IN abi_malformed_scratch_sites st en func ==> st.cs_next_id <= aid` by
    simp[abi_malformed_scratch_sites_def] >>
  drule_all return_allocated_counted_entry >>
  disch_then (qx_choose_then `r` (qx_choose_then `u`
    (qx_choose_then `d` strip_assume_tac))) >>
  `cs_extends a m` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends m st` by
    (drule abi_return_size_code >> simp[same_blocks_def, cs_extends_def] >>
     metis_tac[IS_PREFIX_APPEND]) >>
  `fn_has_code st en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!l. buf.buf_operand <> Label l` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     drule emitted_insts_emit_op >>
     strip_tac >> gvs[comp_return_def]) >>
  `!l. buf.buf_operand <> Label l /\ base_op <> Label l /\ hi <> Label l` by
    metis_tac[return_safe_operand_not_label, return_decode_bound_not_label] >>
  `?ceiling z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_fmp = u.vs_fmp /\
    abi_malformed_resource_post ctx func ce cx ee st.cs_next_var
      (abi_malformed_scratch_sites st en func) a.cs_next_id u z /\
    val_in_memory tv rv d z.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d
      (type_memory_bytes ce rt) u z /\
    fresh_vars_wrt ceiling z /\
    (!aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP u.vs_allocas aid = SOME (b,sz) \/ u.vs_alloca_next <= b) /\
    ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts` by
    (irule return_capped_counted_success >> simp[] >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`B`, `live`, `sf`] >> gvs[]) >>
  qexistsl_tac [`r`, `u`, `d`, `ceiling`, `z`] >> simp[] >>
  `gas_marked_path F ctx func r (0 + 0) (OK z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  `gas_marked_path F ctx func s (0 + 0) (OK z)` by
    (irule gas_marked_path_then >> qexists_tac `r` >> gvs[]) >>
  fs[]
QED
