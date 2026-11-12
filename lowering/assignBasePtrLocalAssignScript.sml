(* The overlap-safe assignment prefix is executed once, then the local
   store consumes its actual pointer and semantic endpoint. *)
Theory assignBasePtrLocalAssign
Ancestors assignBasePtrLocalCompilerStore assignBasePtrStaging bodyDeclMemoryCore
  stmtLowering context valueCopyBytes exprLoweringProps stmtFragPtr
  abiBuiltinAllocation abiBuiltinEncodeAllocate bodyPtrDefs
  emitHelper emitHelperProps compileEnv loweringStateRelDefs localPtrsProps
  venomState venomExecSemantics valueEncoding valueEncodingProps
  exprSimProps exprSimBufferStore valueTypingMemoryProps fragExec finite_map words fragGasPathPtr gasSummaryComposePtr

Theorem assign_base_scratch_var_reserved[local]:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) ==>
  not_fresh_at sn (STRING #"%" (toString sa.cs_next_var))
Proof
  strip_tac >> drule buffer_copy_memory_shape >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[not_fresh_at_def]
QED

Theorem assign_base_local_staged_code:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn /\
  (dty = sty \/ is_bytestring_type dty) ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty dty sn = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
    fn_has_code sa sm fn /\ fn_has_code sm sn fn /\ fn_has_code sn sb fn
Proof
  strip_tac >>
  `?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[pairTheory.PAIR]) >>
  `compile_store_memory ce buf.buf_operand dst dty dty sn = ((),sb)` by
    metis_tac[compile_store_memory_bytestring_src] >>
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[] >>
  `cs_extends sa sm` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sm sn` by
    (drule buffer_copy_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sn sb` by
    (drule buffer_store_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn fn /\ fn_has_code sn sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

Theorem assign_base_local_compatible_store_ptr:
  compile_store_memory cenv (Var src) (Var p) dty dty sa = ((),sb) /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  ~is_word_type dty /\ evaluate_type (get_tenv cx) dty = SOME entry.type /\
  evaluate_type (get_tenv cx) sty = SOME tv /\
  value_has_type entry.type v /\ value_has_type tv v /\
  type_memory_bytes cenv dty = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\ ptr_covers G tn src s (type_memory_size tv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw) m) /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      Gf tf u /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `(!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type v (w2n sw) m) /\
   (if is_bytestring_type dty then val_store_size entry.type v
    else type_memory_size entry.type) <= type_memory_size tv` by
    (Cases_on `dty = sty` >-
       (gvs[] >> rw[] >> metis_tac[val_store_size_le, value_has_type_memory_wf]) >>
     `is_bytestring_type dty /\ is_bytestring_type sty` by fs[] >>
     `val_store_size entry.type v = val_store_size tv v` by
       metis_tac[bytestring_val_store_size_eq] >>
     conj_tac >- metis_tac[bytestring_val_in_memory_transfer] >>
     simp[] >> metis_tac[val_store_size_le, value_has_type_memory_wf]) >>
  `ptr_covers G tn src s (if is_bytestring_type dty then val_store_size entry.type v
    else type_memory_size entry.type)` by
    (Cases_on `is_bytestring_type dty` >> gvs[ptr_covers_def] >> decide_tac) >>
  irule assign_base_local_store_memory_ptr >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem assign_base_local_memory_assign_ptr:
  compile_assign_value cenv (Var p) LocMemory (Var src) F loc
    dty sty info bytes sa = ((),sb) /\
  (dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  evaluate_type (get_tenv cx) dty = SOME entry.type /\
  evaluate_type (get_tenv cx) sty = SOME tv /\
  value_has_type entry.type v /\ value_has_type tv v /\
  type_memory_bytes cenv dty = type_memory_size entry.type /\
  type_memory_bytes cenv sty = type_memory_size tv /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  type_memory_size tv < dimword (:256) /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  expr_val_at cenv cx sty va vb es v (Var src) s /\
  lookup_var src s = SOME sw /\ ptr_covers G tn src s (type_memory_size tv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n sw) m) /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tf u.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) u /\
    ghost_inv d cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      Gf tf u /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory cenv (Var src) (Var p) dty dty sa = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_assign_value_def] >> metis_tac[compile_store_memory_bytestring_src]) >>
  irule assign_base_local_compatible_store_ptr >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >> simp[] >>
  qexistsl_tac [`sty`, `tv`] >> simp[]
QED

Resume assign_base_local_memory_assign_ptr[staged]:
  qpat_x_assum `loc = SOME LocMemory` SUBST_ALL_TAC >>
  drule assign_base_local_staged_code >>
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule body_scratch_alloc_operand >> strip_tac >>
  qmatch_asmsub_abbrev_tac `buf.buf_operand = Var fresh` >>
  `not_local_ptr cenv es.scopes fresh` by
    (simp[Abbr `fresh`] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> fresh` by
    (simp[Abbr `fresh`, not_fresh_at_def] >> metis_tac[]) >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> x <> fresh) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> x <> fresh)` by
    metis_tac[] >>
  `val_wf tv v /\ val_footprint tv v <= type_memory_bytes cenv sty` by
    simp[value_has_type_memory_wf, val_footprint_le] >>
  `src <> fresh` by metis_tac[] >>
  `eval_operand (Var src) s = SOME sw` by simp[eval_operand_def] >>
  `compile_copy_memory (Var fresh) (Var src) (type_memory_bytes cenv sty) sm = ((),sn)` by
    metis_tac[] >>
  `type_memory_bytes cenv sty < dimword (:256) /\
   ptr_covers G tn src s (type_memory_bytes cenv sty) /\ sa.cs_next_id <= sa.cs_next_id` by simp[] >>
  unabbrev_all_tac >>
  drule_all (Q.INST [`frame_sa` |-> `sa`] (SPEC_ALL assign_base_alloc_scratch_staging_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "landing"
QED

Resume assign_base_local_memory_assign_ptr[landing]:
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sn x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sn x)` by
    metis_tac[] >>
  `not_fresh_at sn (STRING #"%" (toString sa.cs_next_var))` by
    (drule_all assign_base_scratch_var_reserved >> simp[]) >>
  `compile_store_memory cenv (Var (STRING #"%" (toString sa.cs_next_var)))
     (Var p) dty dty sn = ((),sb)` by metis_tac[] >>
  `lookup_var (STRING #"%" (toString sa.cs_next_var)) t = SOME a /\
   ptr_covers Gf tf (STRING #"%" (toString sa.cs_next_var)) t (type_memory_size tv)` by
    (conj_tac
     >- (qpat_x_assum `eval_operand (Var (STRING _ _)) t = SOME a` mp_tac >>
         simp[eval_operand_def]) >>
     qpat_x_assum `ptr_covers Gf tf _ t _` mp_tac >> simp[]) >>
  drule_all assign_base_local_compatible_store_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf' tf' (OK u')` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`Gf'`, `tf'`, `u'`] >> simp[] >>
  rpt strip_tac >> fs[ghost_kept_def] >>
  metis_tac[eval_operand_def, operand_11]
QED

Finalise assign_base_local_memory_assign_ptr
