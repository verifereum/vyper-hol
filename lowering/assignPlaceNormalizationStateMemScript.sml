Theory assignPlaceNormalizationStateMem
Ancestors
  bodyMemBopRestWordPath
  loweringStateRelDefs valueEncodingDefs
  assignPlaceNormalizationMem exprSimCopy
  placeTypedCopyForwardMem
  exprSimStorageCopy localPtrsProps exprSimAlloc exprLoweringProps
  loweringHalt venomInst placeMemoryCopyEffect venomState compileEnv
  stmtSimDefs fragGasPathMem

Theorem normalization_copy_state:
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx ee r /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  FLOOKUP r.vs_allocas sa.cs_next_id = SOME (d,n) /\
  typed_copy_effect ctx func sm sb r t d n ==>
  stmt_state_rel ctx func ce cx ee t
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `copy_static t = copy_static r` by
    (drule typed_copy_effect_record >>
     simp[copy_static_def, venom_state_component_equality]) >>
  irule copy_buffer_state_rel_frame >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  qexistsl_tac [`d`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]`, `sm`, `n`] >>
  simp[mk_inst_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint d n lb len` by
        (irule local_ptrs_rel_alloca_disjoint >>
         goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
         qexistsl_tac [`func`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
           [STRING #"%" (toString sa.cs_next_var)]`] >>
         simp[mk_inst_def] >>
         metis_tac[stmt_state_rel_def, state_rel_def,
                   local_ptrs_reserved_fresh, arithmeticTheory.LESS_EQ_REFL]) >>
      fs[regions_disjoint_def]) >>
  conj_tac >- metis_tac[typed_copy_effect_lookup] >>
  conj_tac >- (rpt strip_tac >> irule typed_copy_effect_bytes >>
               simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  metis_tac[typed_copy_effect_length]
QED

Theorem assign_place_normalization_state_mem:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand ty (vv_operand vv) sty sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx ee s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  type_memory_size dtv < dimword (:256) /\
  vv_at ce cx sty origin sa ee raw vv s /\
  vv_store_bound cx ty sty ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  assignable_type (get_tenv cx) sty /\
  type_widens_to (get_tenv cx) sty ty /\ ty <> sty /\
  ~is_word_type ty /\ ~is_word_type sty /\
  ~is_bytestring_type ty /\ ~is_bytestring_type sty /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  (case vv of StackValue _ _ => T
    | LocatedValue _ p => p.ptr_location = LocMemory) /\
  eval_operand (vv_operand vv) s = SOME sw /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r t dw. gas_path_mem ctx func s 0 (OK t) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    eval_operand buf.buf_operand t = SOME dw /\
    w2n dw + type_memory_size dtv <= t.vs_alloca_next /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    alloca_history func t /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n dw,type_memory_size dtv) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    gas_path_mem ctx func s 0 (OK r) /\
    typed_copy_effect ctx func sm sb r t (w2n dw) (type_memory_size dtv) /\
    stmt_state_rel ctx func ce cx ee r /\ stmt_state_rel ctx func ce cx ee t
Proof
  strip_tac >>
  drule_all normalization_allocate >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[compile_alloc_buffer_parts] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     drule compile_alloc_buffer_parts >> simp[]) >>
  `?t. gas_path_mem ctx func r 0 (OK t) /\
       val_in_memory dtv v (w2n dw) t.vs_memory /\
       typed_copy_effect ctx func sm sb r t (w2n dw) (type_memory_size dtv)` by
    (irule typed_memory_rank_forward_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
     simp[] >> qexistsl_tac [`stv`,`get_tenv cx`] >>
     simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule normalization_copy_state >> metis_tac[]) >>
  `t.vs_alloca_next = r.vs_alloca_next` by
    (drule_all typed_copy_effect_record >>
     simp[venom_state_component_equality]) >>
  `alloca_history func t` by
    (`alloca_inv r` by fs[stmt_state_rel_def] >>
     qpat_assum `gas_path_mem ctx func r 0 (OK t)`
       (mp_tac o MATCH_MP (cj 1 gas_path_mem_exec)) >>
     disch_then (mp_tac o MATCH_MP rest_word_path_alloca) >> simp[]) >>
  drule_all typed_copy_effect_endpoint >> strip_tac >>
  drule_all typed_copy_effect_allocas >> disch_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    metis_tac[typed_copy_effect_lookup] >>
  `eval_operand buf.buf_operand t = SOME dw` by
    (gvs[eval_operand_def] >> metis_tac[typed_copy_effect_lookup]) >>
  qexistsl_tac [`r`,`t`,`dw`] >> asm_simp_tac (srw_ss()) [] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
