(* Shared raise/assert storage normalization, retaining encoder buffers. *)
Theory reasonStorageNormalizationPtr
Ancestors
  storageNormalizationPtr reasonStoragePrefixPtr reasonNormalizedSuffixPtr
  loweringHalt emitHelperProps exprLoweringProps context compileEnv loweringStateRelDefs
  venomState ptrDiscipline bodyPtrDefs words arithmetic finite_map
  fragGasPathPtr

Theorem reason_storage_prefix_normalized_path_ptr:
  stmt_state_rel ctx func cenv cx es s /\
  compile_alloc_buffer (64+m) cc = (buf,c1) /\
  emit_void MSTORE [buf.buf_operand; Lit 0x08c379a0w] c1 = ((),c2) /\
  emit_op ADD [buf.buf_operand; Lit 32w] c2 = (payload,c3) /\
  compile_alloc_buffer m c3 = (tuple,c4) /\
  unwrap_value cenv (LocatedValue ann p) c4 = (op,cb) /\
  fn_has_code cc c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\ fn_has_code c4 cb func /\
  ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  local_ptrs_reserved cenv cc /\ 64+m < dimword(:256) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  vv_holds cenv cx ty tv (LocatedValue ann p) es0 s0 /\ ~is_word_type ty /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  32*n < dimword(:256) /\ n < dimword(:256) /\ 32*n <= m /\
  eval_operand p.ptr_operand s = SOME a /\ storage_holds cx tr ty tv a es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) /\
  n = type_slot_size (BaseTV (StringT max)) ==>
  ?root outer pay tup Gf tnf z b bo bt.
    op = Var root /\ buf.buf_operand = Var outer /\ payload = Var pay /\
    tuple.buf_operand = Var tup /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK z) /\
    z.vs_current_bb = cb.cs_current_bb /\
    z.vs_inst_idx = LENGTH cb.cs_current_insts /\ ~z.vs_halted /\
    stmt_state_rel ctx func cenv cx es z /\ local_ptrs_reserved cenv cb /\
    (!x. MEM x [root;outer;pay;tup] ==> not_fresh_at cb x) /\
    c3.cs_next_id < cb.cs_next_id /\ b+32*n < dimword(:256) /\
    lookup_var root z = SOME (n2w b) /\
    lookup_var outer z = SOME (n2w bo) /\
    lookup_var pay z = SOME (n2w bo+32w) /\
    lookup_var tup z = SOME (n2w bt) /\
    bo+(64+m) < dimword(:256) /\ bt+m < dimword(:256) /\
    ptr_mem_ok cx ty (StringV str) (Var root) Gf tnf z /\
    val_wf (BaseTV (StringT max)) (StringV str) /\
    ptr_covers Gf tnf root z (32+32*word_size (LENGTH str)) /\
    ptr_covers Gf tnf outer z (64+m) /\
    ptr_covers Gf tnf pay z (32+m) /\ ptr_covers Gf tnf tup z m /\
    FLOOKUP z.vs_allocas c3.cs_next_id = SOME (bt,m) /\
    MEM (mk_inst c3.cs_next_id ALLOCA [Lit (n2w m)] [tup]) (fn_insts func) /\
    not_local_ptr cenv es.scopes tup /\
    32+32*word_size (LENGTH str) <= m /\
    32+32*word_size (LENGTH str) < dimword(:256) /\
    val_store_size (BaseTV (StringT max)) (StringV str) =
      32+32*word_size (LENGTH str) /\
    w2n (n2w bo+32w : bytes32)+(32+m) < dimword(:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
    assume_tac >- (Cases_on `tr` >> gvs[]) >>
  `32 <= 64+m /\ m < dimword(:256)` by decide_tac >>
  drule_all reason_storage_encoder_prefix_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at c4 x` by suspend "fresh" >>
  `eval_operand p.ptr_operand t = SOME a /\ storage_holds cx tr ty tv a es t` by
    metis_tac[] >>
  drule_all storage_unwrap_resources_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`root`, `out`, `x`, `out2`, `Gf'`, `tnf'`, `z`, `b'`, `b`, `b2`] >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- suspend "path" >- suspend "names" >- suspend "ids"
  >- suspend "outer" >- suspend "pay" >- suspend "tuple"
  >- suspend "cover_outer" >- suspend "cover_pay" >- suspend "cover_tuple"
  >- suspend "registry" >- suspend "size" >- suspend "bound"
  >- simp[exprSimPropsTheory.val_store_size_def] >> suspend "payload_bound"
QED

Resume reason_storage_prefix_normalized_path_ptr[fresh]:
  qpat_assum `compile_alloc_buffer (64+m) cc = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  qpat_assum `compile_alloc_buffer m c3 = _`
    (strip_assume_tac o MATCH_MP compile_alloc_buffer_parts) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cc.cs_next_var <= c4.cs_next_var` by decide_tac >>
  rpt strip_tac >>
  `not_fresh_at cc x'` by metis_tac[] >>
  qpat_x_assum `not_fresh_at cc x'` mp_tac >>
  qpat_x_assum `cc.cs_next_var <= c4.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED

Resume reason_storage_prefix_normalized_path_ptr[path]:
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume reason_storage_prefix_normalized_path_ptr[names]:
  simp[] >> metis_tac[listTheory.MEM]
QED

Resume reason_storage_prefix_normalized_path_ptr[ids]:
  qpat_assum `compile_alloc_buffer m c3 = _` (mp_tac o MATCH_MP compile_alloc_buffer_parts) >>
  rpt strip_tac >> decide_tac
QED

Resume reason_storage_prefix_normalized_path_ptr[outer]:
  metis_tac[listTheory.MEM]
QED
Resume reason_storage_prefix_normalized_path_ptr[pay]:
  metis_tac[listTheory.MEM]
QED
Resume reason_storage_prefix_normalized_path_ptr[tuple]:
  metis_tac[listTheory.MEM]
QED
Resume reason_storage_prefix_normalized_path_ptr[cover_outer]:
  metis_tac[listTheory.MEM]
QED
Resume reason_storage_prefix_normalized_path_ptr[cover_pay]:
  `64+m-32 = 32+m` by decide_tac >> metis_tac[listTheory.MEM]
QED
Resume reason_storage_prefix_normalized_path_ptr[cover_tuple]:
  metis_tac[listTheory.MEM]
QED
Resume reason_storage_prefix_normalized_path_ptr[registry]:
  metis_tac[]
QED

Resume reason_storage_prefix_normalized_path_ptr[size]:
  drule_all storageUnwrapSizingPtrTheory.storage_string_runtime_copy_capacity >>
  strip_tac >> decide_tac
QED

Resume reason_storage_prefix_normalized_path_ptr[bound]:
  drule_all storageUnwrapSizingPtrTheory.storage_string_runtime_copy_capacity >>
  strip_tac >> decide_tac
QED

Resume reason_storage_prefix_normalized_path_ptr[payload_bound]:
  `b+32 < dimword(:256)` by decide_tac >>
  simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w, LESS_MOD] >> decide_tac
QED

Finalise reason_storage_prefix_normalized_path_ptr
