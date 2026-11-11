(* Return-size prefix with an already allocated destination. *)
Theory extcallReturnDefaultDecode
Ancestors
  extcallReturnCallerSuccess extcallReturnCallerReject extcallReturnEntryBridge
  extcallReturnUnifiedCounted extcallReturnCountedReject extcallReturnFrameBridge
  extcallReturnDecoderOwnership extcallReturnDecoderLabels
  abiReturnSize abiReturnPrefixTransport abiMalformedRecursiveInterface
  abiValidAllocatedContract abiMalformedSiteFrame exprSimWordArgs
  exprLoweringProps loweringPosts compileEnv venomState fragGasMode
  list rich_list arithmetic fragExec localPtrsProps exprSimProps abiBoundaryChecks

Theorem return_prepared_counted_entry:
  compile_return_value_decode lo cap a = (hi,b) /\
  fn_has_code a b func /\
  lo < dimword (:256) /\ cap < dimword (:256) /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\ lo <= LENGTH bs /\
  abi_return_decode_ready ctx func ce cx ee a sites dstid live base_op dst
    B cap bs d n s /\ wb_frame ce es sa s0 s /\
  sa.cs_next_var <= a.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    abi_malformed_entry ctx func ce cx ee b sites dstid live base_op hi
      (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d n u /\
    wb_frame ce es sa s0 u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >> drule_all return_decode_ready_entry >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH b.cs_current_insts))` by
    (irule return_size_counted >> metis_tac[]) >>
  `wb_frame ce es sa s0 (u with vs_inst_idx := LENGTH b.cs_current_insts)` by
    (irule wb_frame_readonly_tail >>
     qexistsl_tac [`a`, `s`] >> simp[lookup_var_def] >>
     qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
     gvs[lookup_var_def]) >>
  drule abi_return_size_code >> strip_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH b.cs_current_insts` >> simp[] >>
  qpat_assum `u = s with vs_vars := _` SUBST1_TAC >>
  fs[same_blocks_def]
QED

Theorem return_prepared_counted_reject:
  compile_return_value_decode lo cap a = (hi,st) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  cs_extends st en /\ fn_has_code a en func /\ fn_inst_ids_distinct func /\
  (!l. dst <> Label l /\ base_op <> Label l) /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  lo < dimword (:256) /\ cap < dimword (:256) /\ lo <= cap /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\
  lo = abi_static_length (vyper_to_abi_type env rt) /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  evaluate_abi_decode_return env ty bs = INR err /\
  abi_decoder_coherent ce env sf rt tv /\ abi_decode_bytes_widths env rt /\
  assignable_type env rt /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf rt < dimword (:256) /\
  (case type_to_abi_dec_info sf ce rt of DecPrimWord clamp => 32 <= lo | _ => T) /\
  abi_return_decode_ready ctx func ce cx ee a
    (abi_malformed_scratch_sites st en func) dstid live base_op dst
    B cap bs d (type_memory_bytes ce rt) s /\
  wb_frame ce es sa s0 s /\ sa.cs_next_var <= a.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (Abort Revert_abort z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a st` by
    (drule abi_return_size_code >> simp[same_blocks_def, cs_extends_def] >>
     metis_tac[IS_PREFIX_APPEND]) >>
  `fn_has_code a st func /\ fn_has_code st en func` by
    metis_tac[fn_has_code_split] >>
  Cases_on `LENGTH bs < lo`
  >- (irule return_size_short_counted >> metis_tac[]) >>
  `lo <= LENGTH bs` by decide_tac >>
  drule_all return_prepared_counted_entry >> strip_tac >>
  `!l. dst <> Label l /\ base_op <> Label l /\ hi <> Label l` by
    metis_tac[return_decode_bound_not_label] >>
  `lo <= LENGTH (TAKE cap bs)` by gvs[LENGTH_TAKE_EQ] >>
  `?z. gas_marked_path F ctx func u 0 (Abort Revert_abort z)` by
    (irule return_capped_counted_reject >>
     first_assum (irule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`ty`, `err`] >> simp[] >>
     qpat_x_assum `case type_to_abi_dec_info _ _ _ of _ => _ | _ => _ | _ => _ | _ => _` mp_tac >>
     Cases_on `type_to_abi_dec_info sf ce rt` >> gvs[] >> decide_tac) >>
  `gas_marked_path F ctx func s (0 + 0) (Abort Revert_abort z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  metis_tac[ADD_0]
QED

Theorem return_prepared_counted_success:
  compile_return_value_decode lo cap a = (hi,st) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  cs_extends st en /\ fn_has_code a en func /\ fn_inst_ids_distinct func /\
  (!l. dst <> Label l /\ base_op <> Label l) /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  lo < dimword (:256) /\ cap < dimword (:256) /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\ lo <= LENGTH bs /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  tv = (if needs_external_call_wrap ty then TupleTV [actual_tv] else actual_tv) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ty bs = INL v /\
  abi_decoder_coherent ce env sf rt tv /\
  abi_return_decode_ready ctx func ce cx ee a
    (abi_malformed_scratch_sites st en func) dstid live base_op dst
    B cap bs d (type_memory_bytes ce rt) s /\
  wb_frame ce es sa s0 s /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= a.cs_next_var /\ sa.cs_next_id <= dstid /\
  sa.cs_next_id <= st.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?z. gas_marked_path F ctx func s 0 (OK z) /\
    stmt_state_rel ctx func ce cx ee z /\ wb_frame ce es sa s0 z /\
    eval_operand dst z = SOME (n2w d) /\
    val_in_memory actual_tv v d z.vs_memory /\
    abi_malformed_destination func ce ee.scopes dstid d
      (type_memory_bytes ce rt) z /\
    ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends a st` by
    (drule abi_return_size_code >> simp[same_blocks_def, cs_extends_def] >>
     metis_tac[IS_PREFIX_APPEND]) >>
  `fn_has_code a st func /\ fn_has_code st en func` by
    metis_tac[fn_has_code_split] >>
  drule_all return_prepared_counted_entry >> strip_tac >>
  `!l. dst <> Label l /\ base_op <> Label l /\ hi <> Label l` by
    metis_tac[return_decode_bound_not_label] >>
  `?ceiling z. gas_marked_path F ctx func u 0 (OK z) /\
    z.vs_fmp = u.vs_fmp /\
    abi_malformed_resource_post ctx func ce cx ee st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid u z /\
    val_in_memory tv (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v)
      d z.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d
      (type_memory_bytes ce rt) u z /\
    fresh_vars_wrt ceiling z /\
    (!aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP u.vs_allocas aid = SOME (b,sz) \/ u.vs_alloca_next <= b) /\
    ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts` by
    (irule return_capped_counted_success >> simp[] >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`B`, `live`, `sf`] >> gvs[]) >>
  `local_ptrs_reserved ce st` by fs[abi_malformed_entry_def] >>
  `!aid. aid IN abi_malformed_scratch_sites st en func ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = aid /\
      inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
      not_local_ptr ce ee.scopes q` by
    (rpt strip_tac >> irule return_decoder_scratch_owned >> metis_tac[]) >>
  `wb_frame ce es sa s0 z` by
    (irule return_allocated_wb_frame >> (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `abi_valid_allocated_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `abi_malformed_resource_post _ _ _ _ _ _ _ _ _ _`)) >>
     `a.cs_next_var <= st.cs_next_var` by
       (mp_tac (Q.SPECL [`lo`, `cap`, `a`] ci_mono_compile_return_value_decode) >>
        simp[ci_mono_def]) >>
     fs[abi_malformed_entry_def, stmt_state_rel_def, state_rel_def,
       abi_malformed_scratch_sites_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `gas_marked_path F ctx func s (0 + 0) (OK z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  `eval_operand dst z = SOME (n2w d)` by
    (fs[abi_malformed_resource_post_def, abi_malformed_entry_def] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee z` by fs[abi_malformed_resource_post_def] >>
  `val_in_memory actual_tv v d z.vs_memory` by
    (Cases_on `needs_external_call_wrap ty` >> gvs[val_in_memory_singleton_tuple]) >>
  `abi_malformed_destination func ce ee.scopes dstid d
      (type_memory_bytes ce rt) z` by
    (irule abi_malformed_resource_destination >> goal_assum (drule_at Any) >>
     fs[abi_malformed_entry_def]) >>
  qexists_tac `z` >> metis_tac[ADD_0]
QED
