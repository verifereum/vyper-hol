(* Stage an ordinary Slice fixed byte source and retain its logical window. *)
Theory bodySliceFixedCaptureMods
Ancestors
  bodySliceFixedAllocMods bodySliceFixedStoreMods bodyFullPostsMods
  exprSimHash exprSimWordArgs loweringHalt stmtSimAugAssignPlace exprLoweringProps
  fragExec freshWrites fragGasOriginPtr gasOriginPtrLabels
  bodyFullHashKeccakFixed ptrDiscipline
  abiCanonicalHeadSize reasonCopySourcePtr bodyPtrDefs compileEnv
  loweringStateRelDefs valueEncodingDefs vyperValue vyperTyping
  venomState arithmetic finite_map pred_set list rich_list byte words

Theorem slice_fixed_capture_source_mods:
  compile_alloc_buffer 32 sm = (buf,sb) /\
  emit_void MSTORE [buf.buf_operand;op] sb = ((),sc) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ (!x. op = Var x ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d ce sm s /\ alloca_history func s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  ptr_val_ok cx (expr_type e) v op G tn s /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    expr_post_mods H ctx func ce cx e es0 sa sm s0 es v op s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t G' tn' root p bs.
    v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
    buf.buf_operand = Var root /\ not_fresh_at sc root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func t /\
    eval_operand (Lit (n2w m)) t = SOME (n2w (LENGTH bs)) /\
    op_taint tn' (Lit (n2w m)) = {} /\ op_prov G' (Lit (n2w m)) = NONE /\
    lookup_var root t = SOME p /\ ptr_covers G' tn' root t (LENGTH bs) /\
    w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= t.vs_alloca_next /\
    mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    lo <= w2n p /\ s.vs_alloca_next <= t.vs_alloca_next /\ allocas_from lo t /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n p,32) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region ce es.scopes t name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!a len. a+len <= w2n p \/ w2n p+32 <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i < s.vs_alloca_next /\ ~(w2n p <= i /\ i < w2n p+32) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    return_buf_frame d ce sc t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G' tn' t)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `?bs. v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
        value_has_type (BaseTV (BytesT (Fixed m))) (BytesV bs)` by
    (Cases_on `v` >> gvs[evaluate_type_def,value_has_type_def]) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `?w. eval_operand op s = SOME w /\ TAKE (LENGTH bs) (word_to_bytes w T) = bs` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule hash_fixed_post_view >> simp[GSYM word_to_bytes_be_def]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def,is_word_type_def] >>
  drule_then assume_tac compile_alloc_buffer_extends >>
  drule_then assume_tac aug_place_emit_void_grows >>
  `fn_has_code sm sb func /\ fn_has_code sb sc func` by
    (irule fn_has_code_split >> simp[]) >>
  pop_assum strip_assume_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s /\ immutable_frame_mods func ce cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[expr_post_mods_def] >> drule expr_post_state >> simp[]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `sm` |-> `sb`] slice_fixed_capture_alloc_mods) >>
  impl_tac >-
    (simp[] >> rpt conj_tac >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`root`,`p`,`u`,`Ga`,`ta`] strip_assume_tac) >>
  suspend "allocate"
QED

Resume slice_fixed_capture_source_mods[allocate]:
  `sm.cs_next_var <= sb.cs_next_var` by
    (drule compile_alloc_buffer_emission >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Ga,ta)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)`
         (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_preserves_labels))) >>
  `eval_operand op u = SOME w /\ op_taint ta op = {}` by
    (Cases_on `op` >> fs[eval_operand_def] >> simp[op_taint_def] >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
     fs[op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp) >>
  `emit_void MSTORE [Var root;op] sb = ((),sc)` by
    (qpat_assum `buf.buf_operand = Var root` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`sm` |-> `sb`, `sb` |-> `sc`, `src` |-> `op`,
                  `aid` |-> `sm.cs_next_id`, `G` |-> `Ga`, `tn` |-> `ta`]
    slice_fixed_capture_store_mods) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac) >>
  suspend "finish"
QED

Resume slice_fixed_capture_source_mods[finish]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Ga,ta)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,Ga,ta) [] (OK t,G',tn')`
       (qspec_then `D` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_append,APPEND]) >>
  `mem_bytes_at (w2n p) (LENGTH bs) t.vs_memory = bs` by
    (qspecl_then [`w2n (p:bytes32)`,`0`,`LENGTH bs`,`32`,`t.vs_memory`]
       mp_tac mem_bytes_at_window >> impl_tac >- simp[] >>
     disch_then (SUBST1_TAC o SYM o SIMP_RULE bool_ss [ADD_CLAUSES,DROP]) >>
     asm_rewrite_tac[] >>
     qpat_assum `LENGTH bs = m` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `ptr_covers G' tn' root t (LENGTH bs)` by
    (irule ptr_covers_mono >> qexists_tac `32` >> simp[]) >>
  `w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= t.vs_alloca_next` by
    decide_tac >>
  `!i. w2n p <= i /\ i < w2n p + LENGTH bs ==> i NOTIN tn'.t_mem` by
    (gen_tac >> strip_tac >> qpat_assum `!i. w2n p <= i /\ i < w2n p+32 ==> _` irule >>
     decide_tac) >>
  suspend "frame"
QED

Resume slice_fixed_capture_source_mods[frame]:
  `!a len. a+len <= w2n p \/ w2n p+32 <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` mp_tac >> simp[]) >>
  `!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory`
       irule >>
     qpat_assum `!aid b len. _ ==> regions_disjoint _ _ _ _`
       (drule_all_then mp_tac) >> simp[regions_disjoint_def,DISJ_COMM]) >>
  `!name b len. local_region ce es.scopes t name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     `local_region ce es.scopes t name b len <=> local_region ce es.scopes u name b len` by
       (irule local_region_lookup_cong >>
        qpat_assum `t = mstore _ _ _ with vs_inst_idx := _` SUBST1_TAC >>
        simp[mstore_def,lookup_var_def]) >>
     `local_region ce es.scopes u name b len` by
       (qpat_assum `local_region ce es.scopes t name b len <=> _`
          (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory`
       irule >>
     qpat_assum `!name b len. local_region ce es.scopes u name b len ==> _`
       (drule_then mp_tac) >> simp[regions_disjoint_def,DISJ_COMM]) >>
  suspend "result"
QED

Resume slice_fixed_capture_source_mods[result]:
  `s.vs_alloca_next <= t.vs_alloca_next /\ FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n p,32)` by
    (asm_rewrite_tac[]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP t.vs_allocas aid = SOME entry` by
    (rpt gen_tac >> disch_tac >> asm_rewrite_tac[] >>
     qpat_assum `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm` by
    asm_rewrite_tac[] >>
  `!i. i < s.vs_alloca_next /\ ~(w2n p <= i /\ i < w2n p+32) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next ==> _` (drule_then (once_rewrite_tac o single o SYM)) >>
     qpat_assum `!i. ~(w2n p <= i /\ i < w2n p+32) ==> _` (drule_then ACCEPT_TAC)) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at sb x` by (irule freshWritesTheory.not_fresh_at_mono >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at sb x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`t`,`G'`,`tn'`,`root`,`p`,`bs`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,simp[eval_operand_def,op_taint_def,op_prov_def]]
QED

Finalise slice_fixed_capture_source_mods
