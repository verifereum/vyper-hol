Theory createCtorTupleStage2Path
Ancestors
  createCtorTupleStores createCtorTupleCaptureFrame exprSimAlloc
  abiBufferAllocationCode fragGasSeq fragGasMode fragGasPath
  exprSimProps exprSimWordArgs exprSimSubscriptArrayFrame exprBopSimProps
  exprLoweringProps loweringPosts loweringStateRelDefs exprLowering context
  compileEnv emitHelper emitHelperProps fragExec freshWrites
  venomExecSemantics venomInst venomInstProofs venomState venomMemDefs
  valueEncodingProps words finite_map arithmetic list rich_list


(* The common source state and the capture endpoint do not move when the
   tuple allocation is performed; in particular raw PlaceR witnesses survive. *)
Theorem ctor_tuple_stage2_path:
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
  ?s_tup source_base source_cap.
    gas_marked_path F ctx func s_vvs 0 (OK s_tup) /\
    eval_operand src s_tup = SOME (n2w source_base) /\
    source_cap = type_memory_bytes ce (TupleT tys) /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV values)) source_base s_tup.vs_memory /\
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
  `ci_mono c_vvs c_alloc` by
    metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `MEM (mk_inst c_vvs.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes ce (TupleT tys)))]
     [STRING #"%" (toString c_vvs.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`)
    (Q.INST [`semantic_func` |-> `func`, `execution_func` |-> `func`]
      literal_alloc_buffer_counted) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `w` strip_assume_tac)) >>
  `wb_frame ce es es c_vvs s_vvs u` by
    (simp[wb_frame_def, locals_kept_mem] >> metis_tac[]) >>
  `!n b k. local_region ce es.scopes u n b k <=>
            local_region ce es.scopes s_vvs n b k` by
    (rpt gen_tac >> irule local_region_wb_frame >> simp[] >>
     conj_tac
     >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl [`es`,`c_vvs`] >> simp[]) >>
  `!i. i < LENGTH tys ==>
    vv_holds ce cx (EL i tys) (EL i raws) (EL i vvs) es u /\
    vv_at ce cx (EL i tys) origin c_vvs es (EL i raws) (EL i vvs) u /\
    read_result cx (EL i raws) es = (INL (EL i values),es)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH tys ==> _` drule >> strip_tac >>
     drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)
       (INST_TYPE [beta |-> alpha] ctor_capture_frame) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ s_vvs`)) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`)) >>
     disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
     disch_then (qspecl_then [`c_vvs`,`c_vvs`] mp_tac) >>
     simp[contract_storage_def, contract_transient_def] >>
     Cases_on `EL i vvs` >> gvs[vv_operand_def]) >>
  `alloca_inv u /\ alloca_room ctx func u /\ fmp_room ctx func u` by
    gvs[stmt_state_rel_def] >>
  `w2n w + type_memory_bytes ce (TupleT tys) <= u.vs_alloca_next` by
    (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `!i. SUM (MAP (type_memory_bytes ce) (TAKE i tys)) <=
         SUM (MAP (type_memory_bytes ce) tys)` by
    (gen_tac >> irule SUM_SUBLIST >> simp[MAP_TAKE, sublist_take]) >>
  drule_at (Pat `compile_extcall_store_values _ _ _ _ _ = _`)
    ctor_delayed_stores_from_boundaries >>
  disch_then (qspecl_then [`values`,`tvs`] mp_tac) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (qspecl_then [`raws`,`origin`,`c_vvs`] mp_tac) >>
  simp[] >>
  impl_tac >-
    (gvs[ci_mono_def] >>
     conj_tac >-
       (gen_tac >> strip_tac >> conj_tac
        >- (qpat_x_assum `!i. SUM _ <= _` (qspec_then `i` mp_tac) >>
            qpat_x_assum `w2n w + _ < _` mp_tac >>
            pure_rewrite_tac[type_memory_bytes_def] >> decide_tac) >> metis_tac[]) >>
     simp[type_memory_bytes_def] >> conj_tac
     >- (drule_all buffer_alloc_code >> strip_tac >>
         goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
     rpt strip_tac >>
     qpat_x_assum `!name p n. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def,
          type_memory_bytes_def]) >>
  strip_tac >>
  `gas_marked_path F ctx func s_vvs 0 (OK q)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `wb_frame ce es es c_vvs s_vvs q` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl [`es`,`c_vvs`,`u`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  qexistsl [`q`,`w2n w`] >> simp[] >>
  conj_tac >- gvs[wb_frame_def] >>
  conj_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!aid p n. _ ==> regions_disjoint _ _ _ _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     qpat_x_assum `!name p n. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  qpat_x_assum `wb_frame _ _ _ _ s_vvs q` mp_tac >>
  pure_rewrite_tac[wb_frame_def] >>
  rpt (disch_then strip_assume_tac) >>
  conj_tac >-
    (rpt strip_tac >> first_assum irule >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!n p len. local_region _ _ _ _ _ _ ==> _` drule >>
         simp[ADD_COMM]) >>
     qexists `aid` >> simp[]) >>
  first_assum MATCH_ACCEPT_TAC
QED
