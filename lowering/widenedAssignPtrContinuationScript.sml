(* Compiler and execution composition for retained widened local assignments. *)
Theory widenedAssignPtrContinuation
Ancestors widenedAssignPtrTypedLocal widenedAssignPtrRhsInput
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
