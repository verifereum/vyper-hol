(* Counted bulk array copying, retaining all frames on one endpoint. *)
Theory typedCopyReturnArrayBulkPtr
Ancestors typedCopyReturnDynArrayEntryPtr typedCopyReturnDynArrayBulkDataPtr
  assignBasePtrCopyFrame assignBasePtrCopyPath assignTuplePtrLocalFixedCopy reasonCopySourcePtr
  venomExecSemantics ptrDiscipline
  annAssignPtrCopy exprSimBufferStore typedMemoryCopy valueCopy
  fragGasPathPtr bodyPtrDefs context words venomState venomInst
  emitHelper compileEnv valueEncoding valueEncodingProps finite_map
  exprSimProps vyperTypeSystem vyperTypeABI vyperTypeArgFits

Theorem typed_copy_bulk_fixed_counted[local]:
  n < dimword(:256) /\
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  (n <> 0 ==> ptr_covers G tn src s n /\ ptr_covers G tn dst s n) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) n s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory tv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b+n <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      qexistsl_tac [`G`,`tn`,`s`] >> simp[gas_path_ptr_rules] >>
      rpt strip_tac >> irule valueCopyTheory.val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`w2n a`,`0`,`m`] >> simp[mem_bytes_at_def]) >>
  `0 < n` by decide_tac >> fs[] >>
  drule_all (SRULE [] assign_base_copy_memory_robust_endpoint_ptr) >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (Cases_on `n` >> gvs[compile_copy_memory_def, emit_void_def, comp_bind_def,
        comp_ignore_bind_def, fresh_id_def, emit_def, comp_return_def]) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[typed_copy_mcopy_state_frame, annassign_static_mcopy_ghost_ptr] >>
  conj_tac >- simp[mcopy_def, write_memory_with_expansion_def] >>
  conj_tac >-
    (gen_tac >> disch_tac >> conj_tac
     >- (`mem_bytes_at i 1 (mcopy (w2n b) (w2n a) n s).vs_memory =
           mem_bytes_at i 1 s.vs_memory` by
           (irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
         pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
         simp[buffer_window_byte]) >>
     eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >-
    simp[step_taint_def, mk_inst_def, imm_taint_def, adopt_reset_def,
         set_var_taint_def] >>
  simp[op_taint_def, annassign_static_mcopy_ghost_ptr] >>
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem typed_copy_sarray_bulk_counted:
  type_memory_bytes ce de = type_memory_bytes ce se /\
  ~is_abi_dynamic ce.ce_struct_fields de /\
  compile_store_memory_typed ce (Var dst) (ArrayT de (Fixed N))
    (Var src) (ArrayT se (Fixed M)) sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv (ArrayT se (Fixed M)) (ArrayT de (Fixed N)) /\
  evaluate_type tenv (ArrayT se (Fixed M)) = SOME stv /\
  evaluate_type tenv (ArrayT de (Fixed N)) = SOME dtv /\ val_wf stv v /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  w2n a + type_memory_size stv < dimword(:256) /\
  w2n b + type_memory_size dtv < dimword(:256) /\
  (type_memory_size stv <> 0 ==> ptr_covers G tn src s (type_memory_size stv)) /\
  (type_memory_size dtv <> 0 ==> ptr_covers G tn dst s (type_memory_size dtv)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b + type_memory_size dtv <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `~is_abi_dynamic ce.ce_struct_fields (ArrayT de (Fixed N))` by
    simp[is_abi_dynamic_def] >>
  `stv = dtv` by metis_tac[typed_copy_static_widening] >>
  qpat_x_assum `stv = dtv` SUBST_ALL_TAC >>
  `type_memory_bytes ce (ArrayT de (Fixed N)) = type_memory_size dtv` by
    (irule typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `compile_copy_memory (Var dst) (Var src) (type_memory_size dtv) sa = ((),sb)` by
    (gvs[Once compile_store_memory_typed_def, is_word_type_def,
         is_bytestring_type_def, type_memory_bytes_def] >>
     gvs[Once compile_store_memory_typed_def]) >>
  irule typed_copy_bulk_fixed_counted >> simp[] >>
  conj_tac >- metis_tac[exprSimPropsTheory.val_footprint_le] >>
  qexistsl_tac [`a`,`dst`,`src`] >> simp[]
QED

Theorem typed_copy_dynarray_bulk_layout[local]:
  acyclic_struct_metadata ce.ce_struct_fields /\
  compile_store_memory_typed ce (Var dst) (ArrayT de (Dynamic N))
    (Var src) (ArrayT de (Dynamic M)) sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?a1 a2 a3 a4 a5 a6 a7 a8 len sp dp flag ok count_op.
    emit_op MLOAD [Var src] sa = (Var len,a1) /\
    emit_op GT [Var len; Lit (n2w N)] a1 = (flag,a2) /\
    emit_op ISZERO [flag] a2 = (ok,a3) /\
    emit_inst ASSERT [ok] [] a3 = ((),a4) /\
    emit_void MSTORE [Var dst; Var len] a4 = ((),a5) /\
    emit_op ADD [Var src; Lit 32w] a5 = (Var sp,a6) /\
    emit_op ADD [Var dst; Lit 32w] a6 = (Var dp,a7) /\
    emit_op MUL [Var len; Lit (n2w (type_memory_bytes ce de))] a7 = (count_op,a8) /\
    compile_copy_memory_dynamic (Var dp) (Var sp) count_op a8 = ((),sb) /\
    fn_has_code sa a1 fn /\ fn_has_code a1 a4 fn /\
    fn_has_code a4 a5 fn /\ fn_has_code a5 a6 fn /\
    fn_has_code a6 a7 fn /\ fn_has_code a7 a8 fn /\ fn_has_code a8 sb fn /\
    ci_mono sa a7 /\ not_fresh_at a7 len /\
    not_fresh_at a7 sp /\ not_fresh_at a7 dp
Proof
  strip_tac >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def,is_word_type_def,is_bytestring_type_def] >>
  simp[Once compile_store_memory_typed_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gnvs[]) >> disch_tac >>
  `?len. length = Var len` by metis_tac[emitHelperPropsTheory.emitted_insts_emit_op] >>
  `?sp. src_data = Var sp` by metis_tac[emitHelperPropsTheory.emitted_insts_emit_op] >>
  `?dp. dst_data = Var dp` by metis_tac[emitHelperPropsTheory.emitted_insts_emit_op] >>
  gnvs[] >> drule_all typed_copy_dyn_prefix_mono >> strip_tac >>
  rename1 `emit_void ASSERT [ok] a3 = ((),a4)` >>
  `emit_inst ASSERT [ok] [] a3 = ((),a4)` by
    (qpat_x_assum `emit_void ASSERT _ _ = _` mp_tac >>
     simp[emit_void_def,emit_inst_def]) >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  gvs[compile_copy_memory_dynamic_def,emit_op_def,emit_void_def,emit_inst_def,
    comp_bind_def,comp_ignore_bind_def,comp_return_def,fresh_var_def,fresh_id_def,emit_def] >>
  fs[fragExecTheory.fn_has_code_def,fragExecTheory.emitted_blocks_def,
    rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem typed_copy_dynarray_bulk_suffix[local]:
  !tv vs M N a b sa sb sc len sp dp count_op fn ctx t tm H PG D.
  emit_op MUL [Var len; Lit (n2w (type_memory_size tv))] sa = (count_op,sb) /\
  compile_copy_memory_dynamic (Var dp) (Var sp) count_op sb = ((),sc) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ ~ctx_has_dalloca ctx /\
  ~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa sp /\ not_fresh_at sa dp /\
  lookup_var sp t = SOME (a+32w) /\ lookup_var dp t = SOME (b+32w) /\
  lookup_var len t = SOME (n2w (LENGTH vs)) /\ op_taint tm (Var len) = {} /\
  op_taint tm (Var sp) = {} /\ op_taint tm (Var dp) = {} /\
  LENGTH vs <= M /\ LENGTH vs <= N /\ EVERY (val_wf tv) vs /\
  w2n b + (N * type_memory_size tv + 32) < dimword(:256) /\
  w2n (a+32w) = w2n a+32 /\ w2n (b+32w) = w2n b+32 /\
  (0 < type_memory_size tv ==> ptr_covers H tm sp t (M * type_memory_size tv)) /\
  (0 < type_memory_size tv ==> ptr_covers H tm dp t (N * type_memory_size tv)) /\
  (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
    mem_word_at (w2n b) m = n2w (LENGTH vs)) /\
  (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic M)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?K tf u.
    gas_path_ptr D 0 ctx fn PG H tm t 0 K tf (OK u) /\
    u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
    typed_copy_state_frame sa (w2n b+32) (LENGTH vs * type_memory_size tv) t u /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic N)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
    (!i. i < w2n b+32 \/ w2n b+32+LENGTH vs * type_memory_size tv <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 t.vs_memory /\
      (i IN tf.t_mem <=> i IN tm.t_mem)) /\
    tf.t_stor = tm.t_stor /\ tf.t_trans = tm.t_trans /\ tf.t_imm = tm.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p t /\
      FLOOKUP K p = FLOOKUP H p /\ op_taint tf (Var p) = op_taint tm (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vs * type_memory_size tv <= N * type_memory_size tv /\
   LENGTH vs * type_memory_size tv <= M * type_memory_size tv` by simp[] >>
  `LENGTH vs * type_memory_size tv < dimword(:256)` by
    (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `N * type_memory_size tv` >> simp[]) >>
  `LENGTH vs * type_memory_size tv <> 0 ==>
   ptr_covers H tm sp t (LENGTH vs * type_memory_size tv) /\
   ptr_covers H tm dp t (LENGTH vs * type_memory_size tv)` by
    (strip_tac >>
     `0 < type_memory_size tv` by (fs[] >> decide_tac) >>
     conj_tac
     >- (irule ptr_covers_mono >> qexists_tac `M * type_memory_size tv` >> simp[]) >>
     irule ptr_covers_mono >> qexists_tac `N * type_memory_size tv` >> simp[]) >>
  `!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
    elems_in_memory vs (w2n (a+32w)) tv m` by
    (rpt strip_tac >> irule exprSimAggregateEncodingTheory.elems_in_memory_intro >>
     gvs[typed_copy_dynarray_representation]) >>
  `eval_operand (Var len) t = SOME (n2w (LENGTH vs))` by simp[eval_operand_def] >>
  drule_all (GEN_ALL typed_copy_dynarray_bulk_data_counted) >>
  disch_then (qspecl_then [`N`,`PG`,`D`] mp_tac) >> simp[]
QED

Theorem typed_copy_dynarray_bulk_compose[local]:
  !K. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
  gas_path_ptr D 0 ctx fn PG H tm t 0 K tf (OK u) /\
  t = (mstore off w s) with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!i. i < off \/ off+32 <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) /\
  typed_copy_state_frame mid (off+32) live t u /\ ci_mono sa mid /\ live <= capacity /\
  (!i. i < off+32 \/ off+32+live <= i ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 t.vs_memory /\
    (i IN tf.t_mem <=> i IN tm.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  tf.t_stor = tm.t_stor /\ tf.t_trans = tm.t_trans /\ tf.t_imm = tm.t_imm /\
  (!p. not_fresh_at mid p ==> lookup_var p u = lookup_var p t /\
    FLOOKUP K p = FLOOKUP H p /\ op_taint tf (Var p) = op_taint tm (Var p)) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK u) /\
  typed_copy_state_frame sa off (32+capacity) s u /\
  (!i. i < off \/ off+(32+capacity) <= i ==>
    mem_byte_at u.vs_memory i = mem_byte_at s.vs_memory i /\
    (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!p. not_fresh_at sa p ==> lookup_var p u = lookup_var p s /\
    FLOOKUP K p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))
Proof
  gen_tac >> strip_tac >>
  `!p. not_fresh_at sa p ==> not_fresh_at mid p` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def,freshWritesTheory.not_fresh_at_mono] >>
  `typed_copy_state_frame sa off (32+capacity) s t` by
    (rw[typed_copy_state_frame_def,typed_copy_frame_def]
     >- (qpat_x_assum `t = _`
           (fn th => once_rewrite_tac[th]) >>
         simp[mstore_def,write_memory_with_expansion_def])
     >> qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
     simp[valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     simp[mstore_def,write_memory_with_expansion_def,listTheory.LENGTH_TAKE] >>
     IF_CASES_TAC >> simp[listTheory.LENGTH_TAKE] >> decide_tac) >>
  `typed_copy_state_frame sa off (32+capacity) t u` by
    (irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`off+32`,`live`] >> simp[] >>
     metis_tac[typed_copy_state_frame_mono]) >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- metis_tac[typed_copy_state_frame_trans] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `i < off+32 \/ off+32+live <= i` by decide_tac >>
      `i < off \/ off+32 <= i` by decide_tac >>
      `mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by simp[] >>
      rpt conj_tac >> gvs[] >>
      `mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by simp[] >>
      qpat_x_assum `mem_bytes_at i 1 _ = _`
        (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
      simp[buffer_window_byte]) >>
  metis_tac[]
QED

Theorem typed_copy_dynarray_bulk_entry[local]:
  !tv vs M N a b sa a1 a2 a3 a4 a5 a6 a7 len sp dp flag ok fn ctx s tn G src dst PG D.
  emit_op MLOAD [Var src] sa = (Var len,a1) /\
  emit_op GT [Var len; Lit (n2w N)] a1 = (flag,a2) /\
  emit_op ISZERO [flag] a2 = (ok,a3) /\
  emit_inst ASSERT [ok] [] a3 = ((),a4) /\
  emit_void MSTORE [Var dst; Var len] a4 = ((),a5) /\
  emit_op ADD [Var src; Lit 32w] a5 = (Var sp,a6) /\
  emit_op ADD [Var dst; Lit 32w] a6 = (Var dp,a7) /\
  fn_has_code sa a1 fn /\ fn_has_code a1 a4 fn /\ fn_has_code a4 a5 fn /\
  fn_has_code a5 a6 fn /\ fn_has_code a6 a7 fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  0 < type_slot_size tv /\ type_slot_size (ArrayTV tv (Dynamic N)) < dimword(:256) /\
  LENGTH vs <= N /\ val_wf (ArrayTV tv (Dynamic M)) (ArrayV (DynArrayV vs)) /\
  w2n a + type_memory_size (ArrayTV tv (Dynamic M)) < dimword(:256) /\
  w2n b + type_memory_size (ArrayTV tv (Dynamic N)) < dimword(:256) /\
  (w2n a + type_memory_size (ArrayTV tv (Dynamic M)) <= w2n b \/
   w2n b + type_memory_size (ArrayTV tv (Dynamic N)) <= w2n a) /\
  (type_memory_size (ArrayTV tv (Dynamic M)) <> 0 ==>
    ptr_covers G tn src s (type_memory_size (ArrayTV tv (Dynamic M)))) /\
  (type_memory_size (ArrayTV tv (Dynamic N)) <> 0 ==>
    ptr_covers G tn dst s (type_memory_size (ArrayTV tv (Dynamic N)))) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic M)) (ArrayV (DynArrayV vs)) (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = a7.cs_current_bb /\ t.vs_inst_idx = LENGTH a7.cs_current_insts /\
    ~t.vs_halted /\ lookup_var len t = SOME (n2w (LENGTH vs)) /\
    op_taint tm (Var len) = {} /\
    lookup_var sp t = SOME (a+32w) /\ op_taint tm (Var sp) = {} /\
    lookup_var dp t = SOME (b+32w) /\ op_taint tm (Var dp) = {} /\
    (0 < M * type_memory_size tv ==> ptr_covers H tm sp t (M * type_memory_size tv)) /\
    (0 < N * type_memory_size tv ==> ptr_covers H tm dp t (N * type_memory_size tv)) /\
    t = (mstore (w2n b) (n2w (LENGTH vs)) s) with
      <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    tm.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      mem_word_at (w2n b) m = n2w (LENGTH vs)) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic M)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
    (!i. ~(w2n b <= i /\ i < w2n b+32) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `N < dimword(:256)` by
    (fs[vyperValueTheory.type_slot_size_def] >>
     `N <= N * type_slot_size tv` by simp[] >> decide_tac) >>
  `ptr_covers G tn src s (32 + M * type_memory_size tv) /\
   ptr_covers G tn dst s (32 + N * type_memory_size tv) /\
   w2n a + 32 < dimword(:256) /\ w2n b + 32 < dimword(:256) /\
   (w2n a + type_memory_size (ArrayTV tv (Dynamic M)) <= w2n b \/
    w2n b + 32 <= w2n a)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  drule_at (Pat `emit_op MLOAD _ _ = _`) typed_copy_dynarray_entry_counted >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers G tn src s _`)) >>
  disch_then (drule_at (Pat `ptr_covers G tn dst s _`)) >>
  disch_then (drule_at (Pat `emit_op GT _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst ASSERT _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD [Var src; Lit 32w] _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD [Var dst; Lit 32w] _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code sa a1 fn`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca ctx`)) >>
  disch_then (drule_at (Pat `lookup_var src s = _`)) >>
  disch_then (drule_at (Pat `lookup_var dst s = _`)) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >> simp[]
QED

Theorem typed_copy_dynarray_bulk_counted:
  de = se /\
  compile_store_memory_typed ce (Var dst) (ArrayT de (Dynamic N))
    (Var src) (ArrayT se (Dynamic M)) sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv (ArrayT se (Dynamic M)) (ArrayT de (Dynamic N)) /\
  evaluate_type tenv (ArrayT se (Dynamic M)) = SOME stv /\
  evaluate_type tenv (ArrayT de (Dynamic N)) = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  w2n a + type_memory_size stv < dimword(:256) /\
  w2n b + type_memory_size dtv < dimword(:256) /\
  (w2n a + type_memory_size stv <= w2n b \/
    w2n b + type_memory_size dtv <= w2n a) /\
  (type_memory_size stv <> 0 ==> ptr_covers G tn src s (type_memory_size stv)) /\
  (type_memory_size dtv <> 0 ==> ptr_covers G tn dst s (type_memory_size dtv)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b + type_memory_size dtv <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  gnvs[vyperValueTheory.evaluate_type_def,AllCaseEqs()] >>
  qpat_x_assum `?tv. _ /\ _ /\ ArrayTV tv (Dynamic M) = stv` strip_assume_tac >>
  qpat_x_assum `?tv. _ /\ _ /\ ArrayTV tv (Dynamic N) = dtv` strip_assume_tac >>
  gnvs[] >>
  qpat_assum `value_has_type (ArrayTV tv (Dynamic M)) v`
    (mp_then Any strip_assume_tac typed_copy_dynarray_typed_value) >>
  gnvs[] >>
  drule_all typed_copy_dynarray_bulk_layout >> strip_tac >>
  `LENGTH vs <= N /\ EVERY (val_wf tv) vs` by
    gvs[typed_copy_dynarray_wf,listTheory.EVERY_EL] >>
  qpat_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _`
    (mp_then Any mp_tac (SRULE [arithmeticTheory.ADD_COMM] typed_copy_dynarray_bulk_entry)) >>
  ntac 8 (disch_then drule) >>
  disch_then (drule_at (Pat `lookup_var dst s = _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca ctx`)) >>
  disch_then (drule_at (Pat `ptr_covers G tn src s _`)) >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `type_memory_bytes ce de = type_memory_size tv` by
    metis_tac[typed_copy_memory_size] >>
  `w2n (a + 32w) = w2n a + 32 /\ w2n (b + 32w) = w2n b + 32` by
    (dep_rewrite.DEP_REWRITE_TAC[abiDecodeStaticPropsTheory.w2n_add_n2w_lt] >>
     fs[type_memory_size_def]) >>
  fs[type_memory_size_def] >>
  `(0 < type_memory_size tv ==> ptr_covers H tm sp t (M * type_memory_size tv)) /\
   (0 < type_memory_size tv ==> ptr_covers H tm dp t (N * type_memory_size tv))` by simp[] >>
  drule_all (SRULE [] typed_copy_dynarray_bulk_suffix) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  rev_drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)
    (GEN_ALL typed_copy_dynarray_bulk_compose) >>
  disch_then (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `t = _`)) >>
  disch_then (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ci_mono _ _`)) >>
  disch_then (qspec_then `N * type_memory_size tv` mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `!i. ~(_ <= i) \/ _ ==> _`
       (assume_tac o REWRITE_RULE [arithmeticTheory.NOT_LESS_EQUAL,arithmeticTheory.NOT_LESS]) >>
     qpat_x_assum `tm.t_mem = _` kall_tac >>
     qpat_x_assum `!i. i < w2n b+32 \/ _ ==> _` (assume_tac o SRULE []) >>
     simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     gen_tac >> disch_tac >>
     qpat_x_assum `!i. i < w2n b+32 \/ _ ==> _` (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> simp[])) >> strip_tac >>
  qexistsl_tac [`K'`,`tf`,`u`] >> simp[type_memory_size_def,arithmeticTheory.ADD_COMM] >>
  conj_tac >- (qpat_x_assum `typed_copy_state_frame sa _ _ s u` mp_tac >>
               simp[arithmeticTheory.ADD_COMM]) >>
  gvs[]
QED
