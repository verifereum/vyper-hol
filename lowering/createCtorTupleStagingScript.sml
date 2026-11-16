(* Allocation and delayed raw-result stores, followed by the representative
   ABI source-window boundary. No literal ABI typing is imposed on Bytes[0]. *)
Theory createCtorTupleStaging
Ancestors
  createCtorTupleStage2Path createCtorTupleWindow vyperTypeDefaults vyperMisc
  list arithmetic words compileEnv valueEncoding valueEncodingProps
  vyperValue vyperTyping

Theorem ctor_tuple_stage2_correct:
  compile_alloc_buffer (type_memory_bytes ce (TupleT tys)) c_vvs = (buf,c_alloc) /\
  src = buf.buf_operand /\
  compile_extcall_store_values ce (ZIP (vvs,tys)) src 0 c_alloc = ((),c2) /\
  LENGTH vvs = LENGTH tys /\ LENGTH raws = LENGTH tys /\
  LENGTH values = LENGTH tys /\ LENGTH tvs = LENGTH tys /\
  fn_has_code c_vvs c_alloc func /\ fn_has_code c_alloc c2 func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce c_vvs /\
  origin.cs_next_var <= c_vvs.cs_next_var /\
  origin.cs_next_id <= c_vvs.cs_next_id /\
  type_memory_bytes ce (TupleT tys) < dimword (:256) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!t v. evaluate_type (get_tenv cx) t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV values)) = SOME av /\
  (!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i values) /\
    val_wf (EL i tvs) (EL i values) /\
    type_memory_bytes ce (EL i tys) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2 ** 64 /\
    type_memory_size (EL i tvs) + 64 < dimword (:256) /\
    (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
    (!l. vv_operand (EL i vvs) <> Label l) /\
    vv_holds ce cx (EL i tys) (EL i raws) (EL i vvs) es s_vvs /\
    vv_at ce cx (EL i tys) origin c_vvs es (EL i raws) (EL i vvs) s_vvs /\
    read_result cx (EL i raws) es = (INL (EL i values),es)) /\
  stmt_state_rel H ctx func ce cx es s_vvs /\
  storage_well_formed_on cx es (FST H) /\
  ~s_vvs.vs_halted /\ s_vvs.vs_current_bb = c_vvs.cs_current_bb /\
  s_vvs.vs_inst_idx = LENGTH c_vvs.cs_current_insts ==>
  ?s_tup source_base source_cap ct rv.
    gas_marked_path F ctx func s_vvs 0 (OK s_tup) /\
    eval_operand src s_tup = SOME (n2w source_base) /\
    source_cap = type_memory_bytes ce (TupleT tys) /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV values)) source_base s_tup.vs_memory /\
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys))
      ct rv source_base source_cap s_tup.vs_memory /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av /\
    source_rep (get_tenv cx) (TupleT tys)
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys)) ct /\
    stmt_state_rel H ctx func ce cx es s_tup /\
    alloca_inv s_tup /\ alloca_room ctx func s_tup /\ fmp_room ctx func s_tup /\
    ~s_tup.vs_halted /\ s_tup.vs_current_bb = c2.cs_current_bb /\
    s_tup.vs_inst_idx = LENGTH c2.cs_current_insts /\
    FLOOKUP s_tup.vs_allocas c_vvs.cs_next_id = SOME (source_base,source_cap) /\
    source_base + source_cap <= s_tup.vs_alloca_next /\
    wb_frame ce es es c_vvs s_vvs s_tup /\
    s_tup.vs_accounts = s_vvs.vs_accounts /\
    s_tup.vs_transient = s_vvs.vs_transient /\
    s_tup.vs_requests = s_vvs.vs_requests /\
    s_tup.vs_call_ctx = s_vvs.vs_call_ctx /\
    (!n b k. local_region ce es.scopes s_tup n b k <=>
       local_region ce es.scopes s_vvs n b k) /\
    (!aid row. FLOOKUP s_vvs.vs_allocas aid = SOME row ==>
       FLOOKUP s_tup.vs_allocas aid = SOME row) /\
    (!aid b k. aid < c_vvs.cs_next_id /\
       FLOOKUP s_vvs.vs_allocas aid = SOME (b,k) ==>
       source_base + source_cap <= b \/ b + k <= source_base) /\
    (!n b k. local_region ce es.scopes s_tup n b k ==>
       source_base + source_cap <= b \/ b + k <= source_base) /\
    (!aid b k. aid < c_vvs.cs_next_id /\
       FLOOKUP s_vvs.vs_allocas aid = SOME (b,k) /\
       (!n p len. local_region ce es.scopes s_vvs n p len ==>
          b + k <= p \/ p + len <= b) ==>
       mem_bytes_at b k s_tup.vs_memory = mem_bytes_at b k s_vvs.vs_memory) /\
    (!x w. not_fresh_at c_vvs x /\ lookup_var x s_vvs = SOME w ==>
       lookup_var x s_tup = SOME w)
Proof
  strip_tac >>
  `MAP (type_memory_bytes ce) tys = MAP type_memory_size tvs` by
    (irule LIST_EQ >> simp[EL_MAP] >> metis_tac[]) >>
  `type_memory_bytes ce (TupleT tys) = type_memory_size (TupleTV tvs)` by
    simp[type_memory_bytes_def, type_memory_size_def,
         valueEncodingProofsTheory.type_memory_size_list_sum] >>
  `type_slot_size (TupleTV tvs) <= dimword (:256)` by
    (qpat_x_assum `type_memory_bytes ce (TupleT tys) < _` mp_tac >>
     simp[type_memory_size_slots] >> decide_tac) >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs` by
    (simp[OPT_MMAP_SOME_IFF, EVERY_EL, EL_MAP, LIST_EQ_REWRITE] >>
     metis_tac[optionTheory.THE_DEF, optionTheory.IS_SOME_DEF]) >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)` by
    simp[Once evaluate_type_def, evaluate_types_OPT_MMAP] >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV values))` by
    (simp[value_has_type_def, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
     metis_tac[]) >>
  drule_all ctor_tuple_stage2_path >> strip_tac >>
  `source_cap = type_memory_size (TupleTV tvs)` by simp[] >>
  drule_all ctor_tuple_representative_window >> strip_tac >>
  qexistsl [`s_tup`,`source_base`,`source_cap`,`ct`,`rv`] >> gvs[] >>
  metis_tac[]
QED
