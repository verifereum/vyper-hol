(* Memory-checked staging prefixes for place assignment. *)
Theory placeAssignStagingMem
Ancestors
  placeTypedCopyForwardMem exprSimMemUnwrap placeMemoryStaging
  placeTypedCopyPrimitiveMem placeMemoryCopyEffect fragGasPathMem
  valueEncodingProps exprSimAlloc exprLoweringProps compileEnv venomState
  loweringHalt abiTupleProps rich_list fragExec memoryLocalRhsProps
  exprSimProps valueCopy vyperTypeSystem context

Theorem compile_staging_prefix_mem:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op n sm = ((),sn) /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ n = type_memory_size stv /\
  val_wf stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + n <= s.vs_alloca_next /\ alloca_history func s ==>
  ?r u tw. gas_path_mem ctx func s 0 (OK r) /\
    gas_path_mem ctx func s 0 (OK u) /\
    gas_path_mem ctx func r 0 (OK u) /\
    stmt_state_rel ctx func cenv cx ee r /\ alloca_history func r /\
    r.vs_memory = s.vs_memory /\
    s.vs_alloca_next <= r.vs_alloca_next /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw + n < dimword (:256) /\
    w2n tw + n <= r.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    typed_copy_effect ctx func sm sn r u (w2n tw) n /\
    val_in_memory stv v (w2n tw) u.vs_memory
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  rename1 `gas_path_mem ctx func s 0 (OK r)` >>
  `w2n sw + n <= r.vs_alloca_next` by decide_tac >>
  drule_all compile_copy_memory_effect_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `typed_copy_effect ctx func sm sn r u _ _` >>
  `gas_path_mem ctx func s 0 (OK u)` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  `val_in_memory stv v (w2n w) u.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_relocate >> conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `n`, `w2n sw`] >> simp[]) >>
  qexistsl_tac [`r`, `u`, `w`] >> simp[] >> metis_tac[]
QED

Theorem compile_store_memory_nonword_effect_mem:
  ~is_word_type dty /\ ~is_word_type sty /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv dty = SOME dtv /\ evaluate_type tenv sty = SOME stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv + 64 < dimword (:256) /\
  w2n sw + type_memory_size stv <= u.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= u.vs_alloca_next /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  fn_inst_ids_distinct func /\
  (dty <> sty /\ ~is_bytestring_type dty ==>
    w2n sw + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n sw) /\
  compile_store_memory cenv sp dp dty sty a = ((),b) ==>
  ?t. gas_path_mem ctx func u 0 (OK t) /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv)
Proof
  strip_tac >>
  `w2n sw + val_store_size stv v <= u.vs_alloca_next` by
    (qspec_then `stv` (qspec_then `v` mp_tac) val_store_size_le >> simp[]) >>
  Cases_on `dty = sty`
  >- (gvs[] >> irule compile_store_memory_nonword_path_mem >>
      simp[] >> metis_tac[]) >>
  Cases_on `is_bytestring_type dty`
  >- (`is_bytestring_type sty` by
        (gvs[type_widens_to_def] >>
         metis_tac[memoryLocalRhsPropsTheory.arg_type_fits_bytestring_source]) >>
      `compile_store_memory_typed cenv dp dty sp sty a = ((),b)` by
        (simp[Once compile_store_memory_typed_def] >>
         gvs[compile_store_memory_def]) >>
      drule_all typed_memory_bytestring_path_mem >>
      disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  `compile_store_memory_typed cenv dp dty sp sty a = ((),b)` by
    gvs[compile_store_memory_def] >>
  irule typed_memory_rank_forward_mem >> simp[] >>
  goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`stv`, `tenv`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[]
QED
