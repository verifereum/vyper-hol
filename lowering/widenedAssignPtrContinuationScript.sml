(* Compiler and execution composition for retained widened local assignments. *)
Theory widenedAssignPtrContinuation
Ancestors widenedAssignPtrTypedLocal widenedAssignPtrRhsInput
  assignBasePtrAllocSeparate valueEncodingProps bodyDeclMemoryCore
  tupleLocalStoreRun localPtrsProps venomInst fragGasPathPtr stmtFragPtr exprSimAlloc
  assignBasePtrLocalAssign externalEntryShape stmtLowering context
  abiBuiltinAllocation abiBuiltinEncodeAllocate emitHelper emitHelperProps
  compileEnv exprLoweringProps valueCopyBytes fragExec exprSimBufferStore
  externalNormalizePremises bodyPtrDefs stmtSimAssignStore valueEncodingDefs
  valueEncoding loweringStateRelDefs venomState venomExecSemantics ptrDiscipline
  vyperLookup finite_map words

Theorem widened_assign_local_staged_code:
  compile_assign_value ce dst LocMemory src F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\ fn_has_code sa sb fn ==>
  ?buf sm sn.
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src (type_memory_bytes ce sty) sm = ((),sn) /\
    compile_store_memory ce buf.buf_operand dst dty sty sn = ((),sb) /\
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
  qexistsl_tac [`buf`, `sm`, `sn`] >> simp[] >>
  `cs_extends sa sm` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     metis_tac[cs_appends_emit_helpers, cs_appends_def]) >>
  `cs_extends sm sn` by
    (drule buffer_copy_memory_shape >> simp[cs_extends_def, same_blocks_def] >>
     strip_tac >> simp[]) >>
  `cs_extends sn sb` by
    (mp_tac compile_store_memory_labels >>
     disch_then (qspecl_then [`ce`,`buf.buf_operand`,`dst`,`dty`,`sty`,`sn`] mp_tac) >>
     simp[]) >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn fn /\ fn_has_code sn sb fn` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

(* All store branches land the source write at their own counted endpoint. *)
Theorem widened_assign_local_store_dispatch_ptr:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME entry.type /\
  value_has_type stv v /\ value_has_type entry.type v /\
  val_wf stv v /\ val_wf entry.type v /\ ~is_word_type dty /\
  type_memory_bytes cenv dty = type_memory_size entry.type /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  compile_store_memory cenv (Var src) (Var p) dty sty a = ((),b) /\
  not_fresh_at a src /\ lookup_var src s = SOME sw /\
  op_taint tn (Var src) = {} /\ ptr_covers G tn src s (type_memory_size stv) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  (w2n dw + type_memory_size entry.type <= w2n sw \/
   w2n sw + type_memory_size stv <= w2n dw) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m) /\
  fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  write_place cx (MemoryPlace id []) v es = (INL (),es') /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME dw /\ local_ptrs_reserved cenv a /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx fn cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
    (!x. not_fresh_at a x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `dty = sty \/ is_bytestring_type dty /\ is_bytestring_type sty`
  >- (`compile_store_memory cenv (Var src) (Var p) dty dty a = ((),b)` by
        metis_tac[compile_store_memory_bytestring_src] >>
      `es' = es with scopes := pre ++
        (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` by
        (drule stmtSimAssignStoreTheory.write_place_local >> simp[] >> metis_tac[]) >>
      drule_all assign_base_local_compatible_store_ptr >> metis_tac[]) >>
  `~is_bytestring_type dty /\ dty <> sty` by
    metis_tac[normalize_return_source_kinds] >>
  `compile_store_memory_typed cenv (Var p) dty (Var src) sty a = ((),b)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_def]) >>
  `0 < type_memory_size stv ==> ptr_covers G tn src s (type_memory_size stv)` by simp[] >>
  drule_all widened_assign_typed_local_store_ptr >> metis_tac[]
QED

(* A zero-sized physical source need not be a pointer operand.  Only the
   allocation runs; its fresh result is the source of the subsequent store. *)
Theorem widened_assign_zero_scratch_staging_ptr:
  compile_alloc_buffer 0 sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op 0 sm = ((),sb) /\
  fn_has_code sa sm fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var)) /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==>
    x <> STRING #"%" (toString sa.cs_next_var)) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==>
    x <> STRING #"%" (toString sa.cs_next_var)) /\
  (!x. not_fresh_at frame_sa x ==>
    x <> STRING #"%" (toString sa.cs_next_var)) /\
  frame_sa.cs_next_id <= sa.cs_next_id /\
  expr_val_at cenv cx ty va vb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ op <> buf.buf_operand /\
  val_wf tv v /\ type_memory_size tv = 0 /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n w) m) ==>
  ?u a Gf tf dst.
    buf.buf_operand = Var dst /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
    stmt_state_rel ctx fn cenv cx es u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n a,0) /\
    w2n a < dimword (:256) /\
    lookup_var dst u = SOME a /\ ptr_covers Gf tf dst u 0 /\
    (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
      val_in_memory tv v (w2n a) m) /\
    ghost_inv d cenv cx es Gf tf u /\
    ghost_kept cenv es frame_sa G tn s Gf tf /\
    (!q. q <> buf.buf_operand ==> eval_operand q u = eval_operand q s) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n a) 0 b len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb = sm` by fs[compile_copy_memory_def, comp_return_def] >>
  qpat_x_assum `sb = sm` SUBST_ALL_TAC >>
  `0 < dimword (:256)` by simp[] >>
  drule_all assign_base_ptr_alloc_buffer_counted_separated >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `lookup_var p u = SOME a` by
    metis_tac[eval_operand_def] >>
  `!m. mem_agree_outside tn'.t_mem u.vs_memory m ==>
    val_in_memory tv v (w2n a) m` by
    (rpt strip_tac >>
     irule valueEncodingPropsTheory.val_in_memory_relocate >>
     simp[] >> qexistsl_tac [`m`,`0`,`w2n w`] >>
     simp[mem_bytes_at_def]) >>
  qexistsl_tac [`u`,`a`,`G'`,`tn'`,`p`] >> simp[] >> metis_tac[]
QED

Theorem widened_assign_staged_local_ptr:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME entry.type /\
  value_has_type stv v /\ value_has_type entry.type v /\
  val_wf stv v /\ val_wf entry.type v /\ ~is_word_type dty /\ ~is_word_type sty /\
  type_memory_bytes cenv dty = type_memory_size entry.type /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_size entry.type + 64 < dimword (:256) /\
  type_memory_size stv < dimword (:256) /\
  compile_assign_value cenv (Var p) LocMemory op F (SOME LocMemory)
    dty sty info bytes sa = ((),sb) /\
  (!src. op = Var src ==> not_fresh_at sa src) /\
  expr_val_at cenv cx sty va vb es v op s /\ eval_operand op s = SOME sw /\
  (0 < type_memory_size stv ==> ?src. op = Var src /\
    ptr_covers G tn src s (type_memory_size stv)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  write_place cx (MemoryPlace id []) v es = (INL (),es') /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME dw /\ local_ptrs_reserved cenv sa /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    stmt_state_rel ctx fn cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all widened_assign_local_staged_code >> strip_tac >>
  drule bodyDeclMemoryCoreTheory.body_scratch_alloc_operand >> strip_tac >>
  qmatch_asmsub_abbrev_tac `buf.buf_operand = Var fresh` >>
  `not_local_ptr cenv es.scopes fresh` by
    (simp[Abbr `fresh`] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> fresh` by
    (simp[Abbr `fresh`, not_fresh_at_def] >> metis_tac[]) >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> x <> fresh) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> x <> fresh)` by metis_tac[] >>
  `op <> buf.buf_operand` by (Cases_on `op` >> gvs[] >> metis_tac[]) >>
  `val_footprint stv v <= type_memory_bytes cenv sty` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `?t a Gf tf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
    stmt_state_rel ctx fn cenv cx es t /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~t.vs_halted /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,type_memory_size stv) /\
    w2n a + type_memory_size stv < dimword (:256) /\
    lookup_var fresh t = SOME a /\ ptr_covers Gf tf fresh t (type_memory_size stv) /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    ghost_inv d cenv cx es Gf tf t /\ ghost_kept cenv es sa G tn s Gf tf /\
    (!q. q <> Var fresh ==> eval_operand q t = eval_operand q s)` by
    suspend "stage" >>
  suspend "store"
QED

Resume widened_assign_staged_local_ptr[stage]:
  Cases_on `type_memory_size stv = 0`
  >- suspend "zero" >>
  `0 < type_memory_size stv` by decide_tac >>
  `?src. op = Var src /\ ptr_covers G tn src s (type_memory_size stv)` by metis_tac[] >>
  pop_assum strip_assume_tac >>
  `src <> fresh` by metis_tac[operand_11] >>
  `expr_val_at cenv cx sty va vb es v (Var src) s /\
   eval_operand (Var src) s = SOME sw` by metis_tac[] >>
  `compile_copy_memory (Var fresh) (Var src) (type_memory_bytes cenv sty) sm = ((),sn)` by metis_tac[] >>
  `ptr_covers G tn src s (type_memory_bytes cenv sty) /\
   type_memory_bytes cenv sty < dimword (:256) /\ sa.cs_next_id <= sa.cs_next_id` by simp[] >>
  unabbrev_all_tac >>
  drule_all (Q.INST [`frame_sa` |-> `sa`] (SPEC_ALL assignBasePtrStagingTheory.assign_base_alloc_scratch_staging_ptr)) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`a`,`Gf`,`tf`] >> simp[] >> metis_tac[eval_operand_def]
QED

Resume widened_assign_staged_local_ptr[zero]:
  `compile_alloc_buffer 0 sa = (buf,sm) /\
   compile_copy_memory buf.buf_operand op 0 sm = ((),sn) /\ sa.cs_next_id <= sa.cs_next_id` by (simp[] >> metis_tac[]) >>
  unabbrev_all_tac >>
  drule_all (Q.INST [`frame_sa` |-> `sa`] (SPEC_ALL widened_assign_zero_scratch_staging_ptr)) >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`u`,`a`,`Gf`,`tf`] >> simp[] >> metis_tac[operand_11]
QED

Resume widened_assign_staged_local_ptr[store]:
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sn x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sn x)` by metis_tac[] >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `p <> fresh` by metis_tac[] >>
  `lookup_var p t = SOME dw` by metis_tac[eval_operand_def, operand_11] >>
  `lookup_scopes id es.scopes = SOME entry` by metis_tac[find_containing_scope_lookup] >>
  `local_region cenv es.scopes t id (w2n dw) sz /\ type_memory_size entry.type <= sz` by
    metis_tac[tuple_store_destination_region] >>
  `alloca_inv t /\ local_ptrs_rel fn cenv es.scopes t` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv sty))]
    [fresh]) (fn_insts fn)` by
    (simp[Abbr `fresh`] >> drule_all buffer_alloc_code >> simp[]) >>
  Q.SUBGOAL_THEN `regions_disjoint (w2n a) (type_memory_size stv) (w2n dw) sz` assume_tac
  >- (irule local_ptrs_rel_alloca_disjoint >>
      goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
      simp[mk_inst_def]) >>
  Q.SUBGOAL_THEN `w2n dw + type_memory_size entry.type <= w2n a \/
    w2n a + type_memory_size stv <= w2n dw` assume_tac
  >- fs[regions_disjoint_def] >>
  `op_taint tf (Var fresh) = {}` by fs[ptr_covers_def] >>
  `not_fresh_at sn fresh` by
    (simp[Abbr `fresh`] >>
     drule buffer_copy_memory_shape >> strip_tac >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  `compile_store_memory cenv (Var fresh) (Var p) dty sty sn = ((),sb)` by metis_tac[] >>
  drule_all widened_assign_local_store_dispatch_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t')` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`G'`,`tn'`,`t'`] >> simp[] >>
  rpt strip_tac >> fs[ghost_kept_def] >> metis_tac[eval_operand_def, operand_11]
QED

Finalise widened_assign_staged_local_ptr
