(* Runtime code reasons share the source-independent prefix and memory suffix. *)
Theory reasonCodeEncoderPtr
Ancestors
  reasonCodeNormalizationPtr reasonEncoderPrefixResourcesPtr reasonEncoderLayoutPtr
  reasonNormalizedSuffixPtr reasonMemorySuccessPtr reasonRaiseContinuationPtr
  bodyPtrDefs loweringPosts exprSimProps stmtLowering exprLowering context
  compileEnv venomState venomInst ptrDiscipline fragGasPathPtr arithmetic words
  finite_map exprLoweringProps reasonResourcesPtr valueEncodingProps emitHelper
  reasonCodeResourcesPtr exprOperandVar freshWrites emitHelperProps reasonFinishBoundsPtr

Theorem compile_revert_code_reason_path_ptr:
  compile_revert_with_reason cenv (LocatedValue ann p) ty m cc = ((),se) /\
  fn_has_code cc se func /\ stmt_state_rel ctx func cenv cx es s /\
  ~ctx_has_dalloca ctx /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = cc.cs_current_bb /\
  s.vs_inst_idx = LENGTH cc.cs_current_insts /\ ~s.vs_halted /\
  local_ptrs_reserved cenv cc /\ 64+m < dimword(:256) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at cc x) /\
  p.ptr_location = LocCode /\ ~cenv.ce_is_ctor /\ ~is_word_type ann /\
  type_memory_bytes cenv ann = 32*n /\
  (type_memory_bytes cenv ann+31) DIV 32 = n /\
  32*n < dimword(:256) /\ 32*n <= m /\
  eval_operand p.ptr_operand s = SOME a /\ op_taint tn p.ptr_operand = {} /\
  immutable_holds cenv cx ty tv a es s /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT max)) /\
  read_result cx tv es = (INL (StringV str),es) /\
  n = type_slot_size (BaseTV (StringT max)) ==>
  ?Gf tnf sf. gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (Abort Revert_abort sf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all reason_encoder_layout_ptr >> strip_tac >>
  `32 <= 64+m /\ m < dimword(:256)` by decide_tac >>
  drule_all reason_encoder_prefix_resources_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `(!x. p.ptr_operand = Var x ==> not_fresh_at c4 x) /\
   (!old. MEM old [out; x; out2] ==> not_fresh_at c4 old)` by suspend "fresh" >>
  `eval_operand p.ptr_operand t = SOME a /\ op_taint tnf p.ptr_operand = {} /\
   immutable_holds cenv cx ty tv a es t` by metis_tac[] >>
  `type_memory_size (BaseTV (StringT max)) = 32*n` by
    simp[type_memory_size_slots] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) code_reason_unwrap_path_ptr >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `type_memory_bytes _ _ = _`)) >>
  disch_then (qspec_then `tnf` mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  `?G2 tn2 sf. gas_path_ptr D 0 ctx func PG Gf' tnf' t' 0 G2 tn2
      (Abort Revert_abort sf)` by suspend "suffix" >>
  qexistsl_tac [`G2`, `tn2`, `sf`] >> suspend "path"
QED

Resume compile_revert_code_reason_path_ptr[fresh]:
  qpat_x_assum `compile_alloc_buffer (64+m) cc = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ c1 = _` mp_tac >>
  qpat_x_assum `emit_op ADD _ c2 = _` mp_tac >>
  qpat_x_assum `compile_alloc_buffer m c3 = _` mp_tac >>
  qpat_x_assum `buf.buf_operand = Var out` mp_tac >>
  qpat_x_assum `payload = Var x` mp_tac >>
  qpat_x_assum `tuple.buf_operand = Var out2` mp_tac >>
  qpat_x_assum `!x. p.ptr_operand = Var x ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[compile_alloc_buffer_def, emit_void_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED
Resume compile_revert_code_reason_path_ptr[suffix]:
  `ci_mono c4 cb` by
    (qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_unwrap_value, pairTheory.SND]) >>
  `local_ptrs_reserved cenv cb /\
   (!old. MEM old [root;out2;x;out] ==> not_fresh_at cb old)` by
    suspend "suffix_fresh" >>
  `lookup_var out t' = SOME (n2w b) /\
   lookup_var x t' = SOME (n2w b+32w) /\
   lookup_var out2 t' = SOME (n2w b2) /\
   ptr_covers Gf' tnf' out t' (64+m) /\
   ptr_covers Gf' tnf' x t' (32+m) /\
   ptr_covers Gf' tnf' out2 t' m /\
   FLOOKUP t'.vs_allocas c3.cs_next_id = SOME (b2,m)` by
    (qpat_assum `!old. MEM old [out;x;out2] ==> _` mp_tac >> simp[NoAsms] >> strip_tac >>
     qpat_assum `!x. not_fresh_at c4 x ==> lookup_var x t' = _ /\ _`
       (qspecl_then [`out`] assume_tac) >>
     qpat_assum `!x. not_fresh_at c4 x ==> lookup_var x t' = _ /\ _`
       (qspecl_then [`x`] assume_tac) >>
     qpat_assum `!x. not_fresh_at c4 x ==> lookup_var x t' = _ /\ _`
       (qspecl_then [`out2`] assume_tac) >>
     gvs[]) >>
  `val_wf (BaseTV (StringT max)) (StringV str)` by
    (drule_all immutable_source_resources >> simp[]) >>
  `c3.cs_next_id < sm.cs_next_id` by suspend "suffix_id" >>
  `ptr_covers Gf' tnf' root t' (32+32*word_size (LENGTH str))` by
    (gvs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `w2n (n2w b : bytes32) + (64+m) < dimword(:256) /\
   w2n (n2w b + 32w : bytes32) + (32+m) < dimword(:256) /\
   b2 < dimword(:256)` by suspend "suffix_bounds" >>
  gvs[] >>
  drule_at (Pat `reason_encode_finish _ _ _ _ _ = _`)
    reason_normalized_suffix_path_ptr >>
  disch_then (drule_at (Pat `ptr_mem_ok _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_op MLOAD _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[mk_inst_def] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (qspecl_then [`m`, `b2`, `PG`, `D`] mp_tac) >>
  simp[val_store_size_def, w2n_n2w, LESS_MOD] >>
  impl_tac >- (rpt conj_tac >> metis_tac[]) >> simp[]
QED
Resume compile_revert_code_reason_path_ptr[path]:
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ Gf tnf _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ Gf tnf t _ Gf' tnf' _` mp_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ Gf' tnf' t' _ G2 tn2 _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED
Resume compile_revert_code_reason_path_ptr[suffix_fresh]:
  conj_tac
  >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >>
      gvs[ci_mono_def]) >>
  drule compiler_unwrap_value_var >> simp[] >>
  strip_tac >> rpt strip_tac >> gvs[] >> irule not_fresh_at_mono >>
  qexists_tac `c4` >> gvs[ci_mono_def] >> metis_tac[]
QED
Resume compile_revert_code_reason_path_ptr[suffix_id]:
  `c4.cs_next_id = c3.cs_next_id+1` by
    (qpat_x_assum `compile_alloc_buffer m c3 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  gvs[ci_mono_def] >> decide_tac
QED
Resume compile_revert_code_reason_path_ptr[suffix_bounds]:
  `b < dimword(:256) /\ b+32 < dimword(:256)` by decide_tac >>
  simp[word_add_n2w, w2n_n2w, w2n_add_2, LESS_MOD] >> decide_tac
QED
Finalise compile_revert_code_reason_path_ptr
