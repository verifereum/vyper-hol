Theory externalReturnNormalizeMem
Ancestors
  typedCopyAgreement context compileEnv loweringStateRelDefs emitHelper fragExecMem instMemFrontier
  venomExecSemantics venomState venomInst exprLoweringProps words exprSimDefs exprSimProps loweringPosts
  vfmConstants externalReturnBounds valueEncoding valueEncodingDefs vyperTypeSystem vyperValue
  exprSimBufferStore exprSimLiteralBuffer exprSimVVFrame allocaFootprint
  exprSimOperands abiCallerAllocation exprSimBuffer emitHelperProps
  valueEncodingProps

Theorem typed_copy_word_mem_ok:
  is_word_type dst_ty /\
  compile_store_memory_typed cenv dst dst_ty src src_ty sa = ((), sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n p + 32 <= s.vs_alloca_next /\
  w2n d + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1,
      run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
      below_frontier_MLOAD, below_frontier_MSTORE, mk_inst_def,
      step_inst_base_def, exec_read1_def, eval_operands_def,
      eval_operand_def, lookup_var_def, update_var_def] >>
  simp[GSYM mk_inst_def, below_frontier_MLOAD, below_frontier_MSTORE] >>
  Cases_on `dst` >> gvs[eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def]
QED

(* Diagnostic only: live expression bytes do not include copy padding.
   This is not a counterexample to the external-frame theorem. *)
Theorem bytestring_live_window_not_padded[local]:
  !s:venom_state.
    let t = BaseTV (BytesT (Dynamic 1));
        v = BytesV [0w];
        s' = s with vs_alloca_next := 33
    in w2n (0w:bytes32) + val_footprint t v <= s'.vs_alloca_next /\
       ~(w2n (0w:bytes32) + val_store_size t v <= s'.vs_alloca_next)
Proof
  simp[val_footprint_def, val_store_size_def, word_size_def]
QED

Theorem typed_copy_child_window[local]:
  val_wf child_tv child_v /\
  (off:num) + type_memory_size child_tv <= type_memory_size parent_tv /\
  baddr + type_memory_size parent_tv <= frontier ==>
  baddr + off + val_store_size child_tv child_v <= frontier
Proof
  strip_tac >> drule val_store_size_le >> decide_tac
QED

Theorem normalized_bytes_tuple_dispatch[local]:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory_typed cenv dst
    (TupleT [BaseT (BytesT (Dynamic 2))]) src
    (TupleT [BaseT (BytesT (Dynamic 1))]) =
  compile_typed_copy_fields cenv dst src
    [BaseT (BytesT (Dynamic 2))] [BaseT (BytesT (Dynamic 1))] 0 0
Proof
  simp[compile_store_memory_typed_valid, is_word_type_def,
       is_bytestring_type_def]
QED

Theorem normalized_bytes_tuple_window[local]:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx (TupleT [BaseT (BytesT (Dynamic 1))])
    sa sb es (ArrayV (TupleV [BytesV [0w]])) op s ==>
  ?p. eval_operand op s = SOME p /\
    w2n p + val_store_size (BaseTV (BytesT (Dynamic 1))) (BytesV [0w])
      <= s.vs_alloca_next
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (TupleT [BaseT (BytesT (Dynamic 1))]) =
    SOME (TupleTV [BaseTV (BytesT (Dynamic 1))])` by
    (simp[evaluate_type_def, type_slot_size_def, dimword_def] >> EVAL_TAC) >>
  `~is_word_type (TupleT [BaseT (BytesT (Dynamic 1))])` by
    simp[is_word_type_def] >>
  drule_all expr_val_at_frontier >>
  simp[evaluate_type_def, is_word_type_def, val_footprint_def,
       type_memory_size_def, word_size_def, val_store_size_def]
QED

Theorem normalized_bytes_tuple_typing[local]:
  type_widens_to tenv (TupleT [BaseT (BytesT (Dynamic 1))])
    (TupleT [BaseT (BytesT (Dynamic 2))])
Proof
  EVAL_TAC >> simp[dimword_def, type_slot_size_def, word_size_def]
QED

Theorem normalized_bytes_tuple_layout[local]:
  type_memory_bytes cenv (TupleT [BaseT (BytesT (Dynamic 1))]) = 64 /\
  type_memory_bytes cenv (TupleT [BaseT (BytesT (Dynamic 2))]) = 64 /\
  type_memory_size (TupleTV [BaseTV (BytesT (Dynamic 1))]) = 64 /\
  val_store_size (BaseTV (BytesT (Dynamic 2))) (BytesV [0w]) = 64 /\
  (~is_word_type (TupleT [BaseT (BytesT (Dynamic 2))]) /\
   ~(is_bytestring_type (TupleT [BaseT (BytesT (Dynamic 2))]) /\
     is_bytestring_type (TupleT [BaseT (BytesT (Dynamic 1))])) /\
   TupleT [BaseT (BytesT (Dynamic 1))] <>
     TupleT [BaseT (BytesT (Dynamic 2))])
Proof
  simp[type_memory_bytes_def, type_memory_size_def, val_store_size_def,
       word_size_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem normalized_bytes_tuple_field[local]:
  compile_typed_copy_fields cenv dst src
    [BaseT (BytesT (Dynamic 2))] [BaseT (BytesT (Dynamic 1))] 0 0 =
  compile_store_bytestring src dst
Proof
  simp[Once compile_store_memory_typed_def, compile_with_byte_offset_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  simp[compile_store_memory_typed_bytes, is_bytestring_type_def] >>
  simp[Once compile_store_memory_typed_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >> simp[]
QED

Theorem bytestring_copy_len_mem_ok[local]:
  compile_bytestring_copy_len src sa = (op,sb) /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
  simp[compile_bytestring_copy_len_def, emit_op_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  Cases_on `step_inst_base
    (mk_inst sa.cs_next_id MLOAD [src]
      [STRING #"%" (toString sa.cs_next_var)]) s` >>
  simp[] >> irule run_inst_seq_mem_ok_every >>
  simp[] >> rpt strip_tac >> irule below_frontier_no_ranges >>
  simp[mk_inst_def]
QED

Theorem store_bytestring_mem_ok:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_store_bytestring_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >> strip_tac >>
  rename1 `compile_bytestring_copy_len src sa = (out,mid)` >>
  drule_all buffer_copy_len_run >> strip_tac >>
  drule buffer_copy_len_shape >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa mid) s` by
    (irule bytestring_copy_len_mem_ok >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with vs_vars := _ = s`
      (mp_tac o AP_TERM ``\z. z.vs_alloca_next``) >> simp[]) >>
  `eval_operand src q = SOME p` by
    (`eval_operand src q = eval_operand src s` by
      (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  `eval_operand dst q = SOME d` by
    (`eval_operand dst q = eval_operand dst s` by
      (irule literal_operand_frame >> simp[] >> qexists_tac `sa` >> simp[]) >> simp[]) >>
  drule emit_mcopy_mem_ok >> disch_then irule >> simp[]
QED

(* A normalization site comes after the source expression's sites.  Its
   recorded row may be reused; no global freshness assumption is needed. *)
Theorem normalize_alloca_source_separate:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty sa sb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  0 < val_footprint tv v /\ eval_operand src s = SOME p /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\ sb.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  w2n p + val_footprint tv v <= b \/ b + sz <= w2n p
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >>
  gvs[]
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      `aid <> inst.inst_id` by decide_tac >>
      drule_all abi_caller_allocation_separate >> decide_tac) >>
  drule_all alloca_clear_of_locals >> decide_tac
QED

(* The widened bytes child has a 96-byte destination stride, while the
   next source word starts at offset 64. *)
Theorem normalized_bytes_first_preserves_word[local]:
  compile_store_bytestring src dst sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n p) s = n2w len /\ len <= 1 /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n p + 96 <= s.vs_alloca_next /\
  w2n d + 128 <= s.vs_alloca_next /\
  (w2n p + 96 <= w2n d \/ w2n d + 128 <= w2n p) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      mem_bytes_at (w2n p + 64) 32 q.vs_memory =
        mem_bytes_at (w2n p + 64) 32 s.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 + 32 * word_size len <= 64` by
    (`len = 0 \/ len = 1` by decide_tac >> gvs[word_size_def]) >>
  conj_tac
  >- (drule store_bytestring_mem_ok >> disch_then irule >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `len` >>
      simp[] >> decide_tac) >>
  drule_all buffer_store_bytestring_run >> strip_tac >>
  qexists_tac `q` >> simp[] >>
  irule buffer_mcopy_exterior >> decide_tac
QED

Theorem normalized_bytes_word_fields[local]:
  compile_typed_copy_fields cenv dst src
    [BaseT (BytesT (Dynamic 33)); BaseT (UintT 256)]
    [BaseT (BytesT (Dynamic 1)); BaseT (UintT 256)] 0 0 =
  do compile_store_bytestring src dst;
     d <- compile_with_byte_offset dst 96;
     p <- compile_with_byte_offset src 64;
     compile_store_memory_typed cenv d (BaseT (UintT 256)) p
       (BaseT (UintT 256))
  od
Proof
  simp[Once compile_store_memory_typed_def, compile_with_byte_offset_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  simp[compile_store_memory_typed_bytes, is_bytestring_type_def,
       type_memory_bytes_def, word_size_def] >>
  simp[Once compile_store_memory_typed_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, FUN_EQ_THM] >>
  gen_tac >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[Once compile_store_memory_typed_def, comp_return_def] >>
  gvs[compile_with_byte_offset_def]
QED


Theorem normalize_byte_offset_run:
  compile_with_byte_offset op off sa = (out,sb) /\
  eval_operand op s = SOME a /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  (!x. out = Var x ==> not_fresh_at sb x) /\
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      eval_operand out q = SOME (a + n2w off) /\
      (q with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  Cases_on `off = 0`
  >- (simp[compile_with_byte_offset_def, comp_return_def,
           emitted_insts_def, run_inst_seq_def] >> strip_tac >>
      gvs[WORD_ADD_0]) >>
  simp[compile_with_byte_offset_def] >> strip_tac >>
  drule_all buffer_emit_add_run >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem normalize_byte_offset_mem_ok:
  compile_with_byte_offset op off sa = (out,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `off = 0`
  >- simp[compile_with_byte_offset_def, comp_return_def,
          emitted_insts_def, run_inst_seq_mem_ok_def] >>
  simp[compile_with_byte_offset_def] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem normalize_word_copy_run:
  is_word_type dst_ty /\
  compile_store_memory_typed cenv dst dst_ty src src_ty sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  (!x. dst = Var x ==> not_fresh_at sa x) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
      q.vs_memory = (mstore (w2n d) (mload (w2n p) s) s).vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_store_memory_typed_word, emit_op_def, emit_void_def,
       emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  qabbrev_tac `q = update_var (STRING #"%" (toString sa.cs_next_var))
    (mload (w2n p) s) s` >>
  `step_inst_base (mk_inst sa.cs_next_id MLOAD [src]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK q` by
    (simp[Abbr `q`] >> irule step_MLOAD >> simp[]) >>
  `eval_operand dst q = SOME d` by
    (Cases_on `dst` >> gvs[Abbr `q`, eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def]) >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) q =
      SOME (mload (w2n p) s)` by
    simp[Abbr `q`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (sa.cs_next_id + 1) MSTORE
    [dst; Var (STRING #"%" (toString sa.cs_next_var))] []) q =
      OK (mstore (w2n d) (mload (w2n p) s) q)` by
    (irule step_MSTORE >> simp[]) >>
  simp[run_inst_seq_def] >>
  simp[Abbr `q`, mstore_def, write_memory_with_expansion_def,
       update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem normalize_offset_word_run[local]:
  compile_with_byte_offset dst 96 sa = (d,sb) /\
  compile_with_byte_offset src 64 sb = (p,sc) /\
  compile_store_memory_typed cenv d (BaseT (UintT 256)) p
    (BaseT (UintT 256)) sc = ((),sd) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME v /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  w2n w + 96 <= s.vs_alloca_next /\
  w2n v + 128 <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd /\
  run_inst_seq_mem_ok (emitted_insts sa sd) s /\
  ?q. run_inst_seq (emitted_insts sa sd) s = OK q /\
      q.vs_memory = (mstore (w2n v + 96)
        (mload (w2n w + 64) s) s).vs_memory /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  strip_tac >> qpat_assum `compile_with_byte_offset dst _ _ = _`
    (mp_then Any mp_tac normalize_byte_offset_run) >>
  disch_then drule >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sb x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand src q = SOME w` by
    (Cases_on `src` >> gvs[eval_operand_def] >>
     qpat_x_assum `q with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `compile_with_byte_offset src _ _ = _` assume_tac >>
  drule_all normalize_byte_offset_run >> strip_tac >>
  `eval_operand d q' = SOME (v + 96w)` by
    (Cases_on `d` >> gvs[eval_operand_def] >>
     qpat_x_assum `q' with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `(!x. d = Var x \/ p = Var x ==> not_fresh_at sc x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `q'.vs_memory = s.vs_memory /\ q'.vs_alloca_next = s.vs_alloca_next /\
   (q' with vs_vars := s.vs_vars) = s` by
    (fs[venom_state_component_equality]) >>
  `w2n (v + 96w) = w2n v + 96 /\
   w2n (w + 64w) = w2n w + 64` by
    (conj_tac >- (irule buffer_offset_no_wrap >> qexists_tac `128` >> decide_tac) >>
     irule buffer_offset_no_wrap >> qexists_tac `96` >> decide_tac) >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  `!x. d = Var x ==> not_fresh_at sc x` by metis_tac[] >>
  drule_all normalize_word_copy_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sc sd) q'` by
    (qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
       (mp_then Any mp_tac typed_copy_word_mem_ok) >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  `emitted_insts sa sd = emitted_insts sa sb ++
     (emitted_insts sb sc ++ emitted_insts sc sd)` by
    (`emitted_insts sb sd = emitted_insts sb sc ++ emitted_insts sc sd` by
       (irule emitted_insts_append >> simp[]) >>
     `sd.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sd` by
       simp[listTheory.APPEND_ASSOC] >>
     `emitted_insts sa sd = emitted_insts sa sb ++ emitted_insts sb sd` by
       (irule emitted_insts_append >> simp[]) >> simp[]) >>
  imp_res_tac run_inst_seq_append >>
  conj_tac >- simp[listTheory.APPEND_ASSOC] >> simp[] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[run_inst_seq_append] >>
      irule run_inst_seq_mem_ok_append >> simp[] >>
      metis_tac[normalize_byte_offset_mem_ok]) >>
  once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[] >>
  conj_tac
  >- gvs[mstore_def, mload_def, write_memory_with_expansion_def] >>
  fs[venom_state_component_equality]
QED

Theorem normalized_bytes_word_run[local]:
  compile_typed_copy_fields cenv dst src
    [BaseT (BytesT (Dynamic 33)); BaseT (UintT 256)]
    [BaseT (BytesT (Dynamic 1)); BaseT (UintT 256)] 0 0 sa = ((),sd) /\
  eval_operand src s = SOME w /\ eval_operand dst s = SOME v /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  mload (w2n w) s = n2w len /\ len <= 1 /\
  32 + 32 * word_size len < dimword (:256) /\
  w2n w + 96 <= s.vs_alloca_next /\
  w2n v + 128 <= s.vs_alloca_next /\
  (w2n w + 96 <= w2n v \/ w2n v + 128 <= w2n w) /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts sa sd) s /\
  ?q. run_inst_seq (emitted_insts sa sd) s = OK q /\
      mem_word_at (w2n v + 96) q.vs_memory = mload (w2n w + 64) s /\
      (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[normalized_bytes_word_fields, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_bytestring src dst sa = (u,sb)` >>
  Cases_on `u` >>
  drule_all normalized_bytes_first_preserves_word >> strip_tac >>
  drule_all buffer_store_bytestring_shape >> strip_tac >>
  `eval_operand src q = SOME w /\ eval_operand dst q = SOME v` by
    (conj_tac >- (Cases_on `src` >> gvs[eval_operand_def] >>
                  fs[venom_state_component_equality]) >>
     Cases_on `dst` >> gvs[eval_operand_def] >>
     fs[venom_state_component_equality]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `q.vs_alloca_next = s.vs_alloca_next` by
    fs[venom_state_component_equality] >>
  `w2n w + 96 <= q.vs_alloca_next /\
   w2n v + 128 <= q.vs_alloca_next /\
   q.vs_alloca_next < dimword (:256)` by simp[] >>
  drule_all normalize_offset_word_run >> strip_tac >>
  `emitted_insts sa sd = emitted_insts sa sb ++ emitted_insts sb sd` by
    (irule emitted_insts_append >> simp[]) >>
  imp_res_tac run_inst_seq_append >> simp[] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_append >> simp[]) >>
  conj_tac
  >- (simp[mstore_mem_word_at_same] >>
      fs[GSYM mem_word_at_eq_mload, mem_word_at_def, mem_bytes_at_def]) >>
  fs[venom_state_component_equality]
QED
