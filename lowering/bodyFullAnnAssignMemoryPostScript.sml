Theory bodyFullAnnAssignMemoryPost
Ancestors
  bodyFullMemoryStage bodyFullMemoryStore bodyFullPathHistory stateRelProj
  bodyFullLog bodyFullShared
  stmtLowering exprLoweringProps compileEnv context localPtrsProps
  fragGasOriginPtr fragGasSeqPtr fragExec emitHelperProps
  reasonCopySourcePtr allocaSiteResource venomMemDefs venomState
  typedCopyOriginPtrBase stmtSimDefs bodyMemAggregatePath bodyMemBopRestWordPath
  fragGasOrigin fragGasMode fragGasPath assignTuplePtrCopyLen
  stmtSimDeclCopyFrame stmtSimDeclCompose stmtSimDeclSource
  bodyFullMemoryFrames bodySimFull bodyMemoryDefs
  exprSimStorageCopy bodyBinopFragMemory
  loweringPosts vyperState vyperValue finite_map
  stmtSimDeclMem bodyFullAllocaFresh stmtSimDecl stmtSimProps stmtLoweringMono gasOutcomeFullCompose vyperTypeEnvPreservation contextRawReachable unitTransformDefs freshWrites loweringHalt
  gasShadowCompileStmtHelpers gasShadowCompileStmtBase gasShadowCompileContext
  gasShadow gasShadowState loweringSlice emitHelper gasShadowCompileConvert exprLowering

(* The newly visible local is backed by its preserved allocation. For
   every other name the declaration keeps both the binding and the pointer. *)
Theorem annassign_memory_return_buf_sep:
  return_buf_sep d old es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func old cx es s0) /\
  local_ptrs_reserved old sa /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
  MAP FDOM (sc::rest) = MAP FDOM es.scopes /\
  out.scopes = (sc |+ (id,entry))::rest /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p t = SOME w /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) ==>
  return_buf_sep d ce out t
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_allocated_local) >>
  qpat_assum `FLOOKUP ce.ce_vars id = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP t.vs_allocas aid = SOME _` (irule_at Any) >>
  qexistsl_tac [`sa`,`s0`,`func`,`es`,`cx`,`ctx`,`old`,
                `storage_trace_horizon es.storage_trace`] >>
  simp[] >> rpt strip_tac >>
  drule_all_then ACCEPT_TAC lookup_scopes_declared_other
QED

(* Static decomposition shared by the allocation and RHS producers.  In the
   empty branch b is the compile_expr endpoint: no unwrap is performed. *)
Theorem annassign_full_prefix_parts:
  stmt_env old lctx ret_ty (AnnAssign id typ e) sa = (ce,sf) /\
  stmt_env (gas_shadow_env T old) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)) shadow_sa =
    (gas_shadow_env T ce,shadow_sf) /\
  old.ce_alloca_locals /\ ~is_word_type typ /\
  local_ptrs_reserved old sa /\ gas_shadow_state sa shadow_sa /\
  fn_has_code sa sf func /\ fn_has_code shadow_sa shadow_sf shadow_func ==>
  ?r shadow_r p sz a shadow_a vv sv shadow_sv op b shadow_b.
    declare_local old id typ sa = (ce,r) /\
    declare_local (gas_shadow_env T old) id typ shadow_sa = (gas_shadow_env T ce,shadow_r) /\
    compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sf) /\
    compile_stmt (gas_shadow_env T ce) lctx ret_ty
      (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
      ((),shadow_sf) /\
    sz = type_memory_bytes old typ /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
      ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    emit_inst ALLOCA [Lit (n2w sz)] [p] r = ((),a) /\
    emit_inst ALLOCA [Lit (n2w sz)] [p] shadow_r = ((),shadow_a) /\
    compile_alloc_buffer sz sa = (<|buf_operand := Var p; buf_size := sz|>,a) /\
    compile_alloc_buffer sz shadow_sa =
      (<|buf_operand := Var p; buf_size := sz|>,shadow_a) /\
    compile_expr ce (expr_type e) e a = (vv,sv) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a = (vv,shadow_sv) /\
    (if has_length_word typ /\ is_empty_value_expr e then
       b = sv /\ shadow_b = shadow_sv /\ op = Lit 0w /\
       emit_void MSTORE [Var p; Lit 0w] b = ((),sf) /\
       emit_void MSTORE [Var p; Lit 0w] shadow_b = ((),shadow_sf)
     else
       unwrap_value ce vv sv = (op,b) /\
       unwrap_value (gas_shadow_env T ce) vv shadow_sv = (op,shadow_b) /\
       lower_value compile_expr ce (expr_type e) e a = (op,b) /\
       lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a =
         (op,shadow_b) /\
       compile_assign_value ce (Var p) LocMemory op F (vv_location vv)
         typ (lowered_value_type ce e) (type_memory_bytes ce typ) b = ((),sf) /\
       compile_assign_value (gas_shadow_env T ce) (Var p) LocMemory op F (vv_location vv)
         typ (lowered_value_type (gas_shadow_env T ce) (gas_shadow_expr e))
         (type_memory_bytes (gas_shadow_env T ce) typ) shadow_b = ((),shadow_sf)) /\
    gas_shadow_state r shadow_r /\ gas_shadow_state a shadow_a /\
    gas_shadow_state sv shadow_sv /\ gas_shadow_state b shadow_b /\
    cs_extends sa a /\ cs_extends a sv /\ cs_extends sv b /\ cs_extends b sf /\
    cs_extends a b /\ cs_extends shadow_sa shadow_a /\
    cs_extends shadow_a shadow_b /\ cs_extends shadow_b shadow_sf /\
    fn_has_code sa a func /\ fn_has_code a sv func /\
    fn_has_code a b func /\ fn_has_code b sf func /\
    fn_has_code shadow_sa shadow_a shadow_func /\
    fn_has_code shadow_a shadow_b shadow_func /\
    fn_has_code shadow_b shadow_sf shadow_func /\
    local_ptrs_reserved ce a /\ local_ptrs_reserved ce b /\
    not_fresh_at a p /\ not_fresh_at b p /\
    (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x) /\
    sa.cs_next_id < a.cs_next_id /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)
Proof
  strip_tac >>
  drule stmt_env_annassign >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` (mk_asm "original") >>
  drule_all declare_local_ptr >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (strip_assume_tac o MATCH_MP stmt_env_annassign o
     REWRITE_RULE [gas_shadow_stmt_def]) >>
  rename1 `declare_local _ _ _ shadow_sa = (_,shadow_r)` >>
  `gas_shadow_state st shadow_r` by
    (mp_tac (Q.INST [`cenv` |-> `old`, `id` |-> `id`, `ty` |-> `typ`, `sd` |-> `T`]
       gas_shadow_compiles_env_declare_local) >>
     rewrite_tac[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  asm_x "original" mp_tac >>
  simp[Once compile_stmt_def, emit_local_alloca_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  imp_res_tac emit_inst_unit >> gvs[] >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,sv)` >>
  rename1 `emit_inst ALLOCA _ _ _ = ((),a)` >>
  `compile_stmt ce lctx ret_ty (AnnAssign id typ e)
     (sa with cs_next_var := sa.cs_next_var + 1) = ((),sf)` by
    simp[Once compile_stmt_def, emit_local_alloca_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `compile_alloc_buffer (type_memory_bytes old typ) sa =
    (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var));
       buf_size := type_memory_bytes old typ|>,a)` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def,emit_op_def,emit_inst_def,fresh_id_def,
       fresh_var_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       pairTheory.pair_case_thm] >> strip_tac >> gvs[]) >>
  Cases_on `emit_inst ALLOCA [Lit (n2w (type_memory_bytes old typ))]
    [STRING #"%" (toString sa.cs_next_var)] shadow_r` >>
  rename1 `emit_inst _ _ _ shadow_r = (u,shadow_a)` >>
  `u = () /\ gas_shadow_state a shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`,
      `ops` |-> `[Lit (n2w (type_memory_bytes old typ))]`,
      `outs` |-> `[STRING #"%" (toString sa.cs_next_var)]`]
      gas_shadow_compiles_emit_inst) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then
       [`sa with cs_next_var := sa.cs_next_var + 1`,`shadow_r`] mp_tac) >> gvs[]) >>
  gvs[] >>
  `compile_alloc_buffer (type_memory_bytes old typ) shadow_sa =
    (<|buf_operand := Var (STRING #"%" (toString sa.cs_next_var));
       buf_size := type_memory_bytes old typ|>,shadow_a)` by
    (`shadow_r = shadow_sa with cs_next_var := shadow_sa.cs_next_var + 1` by
       (qpat_assum `declare_local _ _ _ shadow_sa = _`
          (mp_then Any mp_tac declare_local_ptr) >> simp[]) >>
     `shadow_sa.cs_next_var = sa.cs_next_var` by fs[gas_shadow_state_def] >>
     qpat_x_assum `emit_inst ALLOCA _ _ shadow_r = _` mp_tac >>
     simp[compile_alloc_buffer_def,emit_op_def,emit_inst_def,fresh_id_def,
       fresh_var_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
       pairTheory.pair_case_thm] >> strip_tac >> gvs[]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) _ = (shadow_vv,shadow_sv)` >>
  `shadow_vv = vv /\ gas_shadow_state sv shadow_sv` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`, `sd` |-> `T`]
       gas_shadow_stmt_compile_expr_env) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`,`shadow_a`] mp_tac) >> simp[]) >>
  gvs[] >>
  Cases_on `has_length_word typ /\ is_empty_value_expr e`
  >- suspend "empty" >>
  gnvs[] >>
  rename1 `unwrap_value ce vv sv = (op,b)` >>
  Cases_on `unwrap_value ce vv shadow_sv` >>
  rename1 `unwrap_value _ _ shadow_sv = (shadow_op,shadow_b)` >>
  `shadow_op = op /\ gas_shadow_state b shadow_b` by
    (mp_tac (Q.INST [`cenv` |-> `ce`] gas_shadow_compiles_unwrap_value) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sv`,`shadow_sv`] mp_tac) >> gvs[]) >>
  gnvs[] >>
  `lower_value compile_expr ce (expr_type e) e a = (op,b) /\
   lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a =
     (op,shadow_b)` by simp[lower_value_def,comp_bind_def] >>
  `compile_assign_value ce (Var (STRING #"%" (toString sa.cs_next_var)))
    LocMemory op F (vv_location vv) typ (lowered_value_type ce e)
    (type_memory_bytes ce typ) shadow_b = ((),shadow_sf)` by
    (Cases_on `has_length_word typ` >> fs[] >>
     qpat_x_assum `compile_stmt _ _ _ (AnnAssign _ _ (gas_shadow_expr _)) _ = _` mp_tac >>
     simp[Once compile_stmt_def,emit_local_alloca_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,gas_shadow_expr_type]) >>
  `cs_extends sa a /\ cs_extends a sv /\ cs_extends sv b /\ cs_extends b sf /\
   cs_extends a b /\ cs_extends shadow_sa shadow_a /\
   cs_extends shadow_a shadow_b /\ cs_extends shadow_b shadow_sf` by
    (mp_tac (cj 1 ci_mono_stmt_helpers) >>
     mp_tac ci_mono_unwrap_value >>
     mp_tac compile_expr_grows >>
     mp_tac compile_alloc_buffer_extends >>
     simp[ci_mono_def] >> metis_tac[pairTheory.SND,cs_extends_trans]) >>
  `fn_has_code (sa with cs_next_var := sa.cs_next_var+1) sf func` by
    fs[fn_has_code_def,emitted_blocks_def] >>
  `cs_extends a sf` by metis_tac[cs_extends_trans] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `a.cs_next_var <= b.cs_next_var` by metis_tac[compile_expr_grows] >>
  `local_ptrs_reserved ce b /\ not_fresh_at b (STRING #"%" (toString sa.cs_next_var))` by
    (conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `sa.cs_next_id < a.cs_next_id /\
   (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x)` by
    (qspecl_then [`type_memory_bytes old typ`,`sa`] mp_tac compile_alloc_buffer_parts >>
     simp[] >> strip_tac >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qspecl_then [`sa`,`a`,`sf`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`a`,`b`,`sf`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`a`,`sv`,`b`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  `cs_extends shadow_a shadow_sf` by metis_tac[cs_extends_trans] >>
  qspecl_then [`shadow_sa`,`shadow_a`,`shadow_sf`,`shadow_func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`shadow_a`,`shadow_b`,`shadow_sf`,`shadow_func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`op`,`b`,`shadow_b`] >>
  `~(has_length_word typ /\ is_empty_value_expr e)` by simp[] >>
  fs[]
QED

Resume annassign_full_prefix_parts[empty]:
  gvs[comp_return_def] >>
  rename1 `compile_expr ce (expr_type e) e a = (vv,sv)` >>
  `emit_void MSTORE [Var (STRING #"%" (toString sa.cs_next_var)); Lit 0w]
    shadow_sv = ((),shadow_sf)` by
    (qpat_x_assum `compile_stmt _ _ _ (AnnAssign _ _ (gas_shadow_expr _)) _ = _` mp_tac >>
     simp[Once compile_stmt_def,emit_local_alloca_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def,gas_shadow_expr_type]) >>
  `cs_extends sa a /\ cs_extends a sv /\ cs_extends sv sf /\
   cs_extends shadow_sa shadow_a /\ cs_extends shadow_a shadow_sv /\
   cs_extends shadow_sv shadow_sf` by
    (mp_tac ci_mono_emit_void >> mp_tac compile_expr_grows >>
     mp_tac compile_alloc_buffer_extends >> simp[ci_mono_def] >>
     metis_tac[pairTheory.SND]) >>
  `cs_extends a sf` by metis_tac[cs_extends_trans] >>
  `fn_has_code (sa with cs_next_var := sa.cs_next_var+1) sf func` by
    fs[fn_has_code_def,emitted_blocks_def] >>
  drule_all annassign_alloca_code >> strip_tac >>
  `a.cs_next_var <= sv.cs_next_var` by metis_tac[compile_expr_grows] >>
  `local_ptrs_reserved ce sv /\ not_fresh_at sv (STRING #"%" (toString sa.cs_next_var))` by
    (conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `sa.cs_next_id < a.cs_next_id /\
   (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at sv x)` by
    (qspecl_then [`type_memory_bytes old typ`,`sa`] mp_tac compile_alloc_buffer_parts >>
     simp[] >> strip_tac >>
     fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qspecl_then [`sa`,`a`,`sf`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`a`,`sv`,`sf`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  `cs_extends shadow_a shadow_sf` by metis_tac[cs_extends_trans] >>
  qspecl_then [`shadow_sa`,`shadow_a`,`shadow_sf`,`shadow_func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`shadow_a`,`shadow_sv`,`shadow_sf`,`shadow_func`] mp_tac fn_has_code_split >>
  (impl_tac >- simp[]) >> strip_tac >>
  fs[cs_extends_refl]
QED

Finalise annassign_full_prefix_parts

Theorem annassign_memory_full_assign_path:
  !H0 ctx func ce cx mid s sa sf xs p sw dw src_loc dty sty stv dtv v
   n sz aid0 start lo explicit PG G tn.
    compile_assign_value ce (Var p) LocMemory (Var xs) F src_loc
      dty sty (type_memory_bytes ce dty) sa = ((),sf) /\
    ~is_word_type dty /\ ~is_word_type sty /\
    stmt_state_rel H0 ctx func ce cx mid s /\
    fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ alloca_history func s /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        len = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    type_memory_bytes ce sty = n /\ type_memory_size stv = n /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    type_memory_size dtv <= sz /\ n < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sa xs /\ not_fresh_at sa p /\
    lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid0 = SOME (w2n dw,sz) /\ aid0 < sa.cs_next_id /\
    ptr_covers G tn xs s n /\ ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw+n < dimword (:256) /\
    w2n dw+type_memory_size dtv < dimword (:256) /\
    (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/ w2n dw+type_memory_size dtv <= s.vs_alloca_next) /\
    (src_loc = SOME LocMemory ==>
      expr_val_at ce cx sty start sa mid v (Var xs) s) /\
    (src_loc <> SOME LocMemory ==>
      w2n sw+n <= w2n dw \/ w2n dw+type_memory_size dtv <= w2n sw) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u sm Gu tnu t Gf tf.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tf)) /\
      (!H. stmt_state_rel H ctx func ce cx mid s ==>
        stmt_state_rel H ctx func ce cx mid u) /\
      (!D d. ghost_inv_at D lo d ce cx mid G tn s ==>
        ghost_inv_at D lo d ce cx mid Gu tnu u) /\
      alloca_frame ce mid sa s ce mid u /\
      (!aid off len i.
        FLOOKUP s.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region ce mid.scopes s name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tnu.t_mem ==> i IN tn.t_mem) /\
      (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP u.vs_allocas aid = SOME ent) /\
      s.vs_alloca_next <= u.vs_alloca_next /\
      sa.cs_next_id <= sm.cs_next_id /\ local_ptrs_reserved ce sm /\
      (!x. not_fresh_at sa x ==>
        not_fresh_at sm x /\ lookup_var x u = lookup_var x s /\
        FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)) /\
      lookup_var p u = SOME dw /\ ptr_covers Gu tnu p u sz /\
      typed_copy_state_frame sm (w2n dw) (type_memory_size dtv) u t /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
        val_in_memory dtv v (w2n dw) mem) /\
      tf.t_stor = tnu.t_stor /\ tf.t_trans = tnu.t_trans /\ tf.t_imm = tnu.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
        (i IN tf.t_mem <=> i IN tnu.t_mem)) /\
      (!x. not_fresh_at sm x ==>
        lookup_var x t = lookup_var x u /\ FLOOKUP Gf x = FLOOKUP Gu x /\
        op_taint tf (Var x) = op_taint tnu (Var x)) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ptr_covers G tn p s (type_memory_size dtv)` by
    metis_tac[ptr_covers_mono] >>
  Cases_on `src_loc = SOME LocMemory`
  >- suspend "staged" >>
  `compile_store_memory ce (Var xs) (Var p) dty sty sa = ((),sf)` by
    gvs[compile_assign_value_def] >>
  qpat_x_assum `type_memory_size stv = n` (SUBST_ALL_TAC o SYM) >>
  drule body_full_memory_store_path >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var p s = _`)) >>
  disch_then (drule_at (Pat `lookup_var xs s = _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `alloca_history func t` by
    metis_tac[body_full_path_alloca_history] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  qexistsl_tac [`s`,`sa`,`G`,`tn`,`t`,`Gf`,`tf`] >>
  simp[alloca_frame_def] >> metis_tac[]
QED

Resume annassign_memory_full_assign_path[staged]:
  gvs[compile_assign_value_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer _ sa = (buf,sb)` >>
  rename1 `compile_copy_memory _ (Var xs) _ sb = ((),sm)` >>
  `ci_mono sa sb /\ ci_mono sb sm /\ ci_mono sm sf` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory,
      ci_mono_compile_store_memory,pairTheory.SND] >>
  `cs_extends sa sb /\ cs_extends sb sm /\ cs_extends sm sf` by fs[ci_mono_def] >>
  `fn_has_code sa sb func /\ fn_has_code sb sm func /\ fn_has_code sm sf func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) body_full_memory_stage_frame_path >>
  disch_then (drule_at (Pat `compile_copy_memory _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `lookup_var xs s = _`)) >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`u`,`root`,`b`,`Gu`,`tnu`] strip_assume_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `cx_dead H0 cx` mp_tac) >>
  disch_then (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  drule gas_origin_path_erase >> strip_tac >>
  `gas_path_mem ctx func s 0 (OK u)` by fs[gas_marked_path_def] >>
  `alloca_inv u` by metis_tac[bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv] >>
  `s.vs_alloca_next <= u.vs_alloca_next` by
    (drule gas_marked_path_exec >> strip_tac >>
     drule bodyMemBopRestWordPathTheory.rest_word_path_frontier >> simp[]) >>
  `not_fresh_at sm p /\ lookup_var p u = SOME dw /\
   FLOOKUP Gu p = FLOOKUP G p /\ op_taint tnu (Var p) = op_taint tn (Var p)` by
    metis_tac[] >>
  `ptr_covers Gu tnu p u sz /\ ptr_covers Gu tnu p u (type_memory_size dtv)` by
    metis_tac[ptr_covers_lookup_frame] >>
  `FLOOKUP u.vs_allocas aid0 = SOME (w2n dw,sz)` by metis_tac[] >>
  (Q.SUBGOAL_THEN `b + type_memory_size stv <= w2n dw \/ w2n dw + sz <= b` assume_tac
  >-
    (qpat_assum `alloca_inv u`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def,allocas_non_overlapping_def]) >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`sa.cs_next_id`,`aid0`,`b`,
         `type_memory_size stv`,`w2n dw`,`sz`] mp_tac) >> simp[])) >>
  `compile_store_memory ce (Var root) (Var p) dty sty sm = ((),sf)` by
    metis_tac[] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n ((n2w b):bytes32) = b` by simp[] >>
  (Q.SUBGOAL_THEN `w2n ((n2w b):bytes32) + type_memory_size stv < dimword (:256) /\
   (type_memory_size stv = 0 \/ w2n ((n2w b):bytes32) + type_memory_size stv <= u.vs_alloca_next) /\
   (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= u.vs_alloca_next) /\
   (w2n ((n2w b):bytes32) + type_memory_size stv <= w2n dw \/
    w2n dw + type_memory_size dtv <= w2n ((n2w b):bytes32))` assume_tac
  >- (simp[] >> decide_tac)) >>
  drule_at (Pat `compile_store_memory ce (Var root) _ _ _ _ = _`)
    body_full_memory_store_path >>
  disch_then (fn th => qpat_assum `evaluate_type _ sty = SOME stv`
    (mp_then (Pat `evaluate_type _ sty = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ dty = SOME dtv`
    (mp_then (Pat `evaluate_type _ dty = _`) mp_tac th)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ root _ _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (drule_at (Pat `allocas_from _ u`)) >>
  disch_then (drule_at (Pat `fn_has_code sm sf _`)) >>
  disch_then (drule_at (Pat `lookup_var p u = _`)) >>
  disch_then (drule_at (Pat `lookup_var root u = _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`u`,`Gu`,`tnu`,`[]`,`OK t`,`Gf`,`tf`] mp_tac) >>
     simp[]) >>
  `alloca_history func t` by metis_tac[body_full_path_alloca_history] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule typed_copy_state_frame_allocas_below_fmp >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `ci_mono sa sb` mp_tac >>
     qpat_assum `ci_mono sb sm` mp_tac >>
     pure_rewrite_tac[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> qpat_assum `ci_mono sa sb` mp_tac >>
     qpat_assum `ci_mono sb sm` mp_tac >>
     pure_rewrite_tac[ci_mono_def] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`u`,`sm`,`Gu`,`tnu`,`t`,`Gf`,`tf`] >>
  simp[] >> rpt conj_tac >>
  FIRST
    [qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >> simp[] >> NO_TAC,
     map_every qx_gen_tac [`aid`,`off`,`len`,`i`] >> strip_tac >>
     qpat_x_assum `!aid off sz i. _`
       (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
     simp[arithmeticTheory.ADD_COMM] >> disch_then irule >>
     rpt strip_tac >>
     qpat_x_assum `!name a cap. local_region ce mid.scopes s name a cap ==> _` drule >>
     simp[]]
QED

Finalise annassign_memory_full_assign_path

(* Capacity-parametric installation after the joint aggregate store. *)

Theorem annassign_memory_full_ghost_store[local]:
  stmt_state_rel H ctx func ce cx mid u /\ fn_inst_ids_distinct func /\
  ghost_inv_at D lo d ce cx mid G1 tn1 u /\ local_ptrs_reserved ce b /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\ lookup_var p u = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
  type_memory_size tyv <= sz /\
  typed_copy_state_frame b (w2n w) (type_memory_size tyv) u t /\
  tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
  (!i. ~(w2n w <= i /\ i < w2n w + type_memory_size tyv) ==>
    (i IN tnf.t_mem <=> i IN tn1.t_mem)) /\
  (!q. not_fresh_at b q ==> FLOOKUP Gf q = FLOOKUP G1 q /\
    op_taint tnf (Var q) = op_taint tn1 (Var q)) ==>
  ghost_inv_at D lo d ce cx mid Gf tnf t
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  `lo <= w2n w` by
    (fs[bodyPtrDefsTheory.ghost_inv_at_def, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  irule bodyFullMemoryFramesTheory.body_full_memory_ghost_frame >>
  conj_tac >- fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  conj_tac >- (fs[bodyPtrDefsTheory.ghost_inv_at_def,
    ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`G1`, `u`, `b`, `tn1`,
    `{i | w2n w <= i /\ i < w2n w + type_memory_size tyv}`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `local_ptrs_rel func ce mid.scopes u /\ alloca_inv u` by
        metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
      `local_region ce mid.scopes u name (w2n w') sz'` by
        (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
      `regions_disjoint (w2n w) sz (w2n w') sz'` by
        (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
         goal_assum (drule_at Any) >> metis_tac[]) >>
      fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule exprSimPropsTheory.val_footprint_le >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (fs[typedMemoryCopyTheory.typed_copy_frame_def] >>
    rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- (rpt strip_tac >>
    `~(w2n w <= i /\ i < w2n w + type_memory_size tyv)` by decide_tac >>
    metis_tac[]) >>
  fs[typedMemoryCopyTheory.typed_copy_frame_def]
QED

Theorem annassign_memory_full_installation_post:
  !H D lo d ctx func old ce cx es mid out sa b sf s0 s t G0 tn0 G tn Gf tf
   id p sz w inst n tyv v sc rest lctx.
    new_variable id tyv v mid = (INL (),out) /\
    mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
    out = mid with scopes :=
      (sc |+ (id,<|assignable := T; type := tyv; value := v; popped := []|>))::rest /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
              ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    FLOOKUP old.ce_vars id = NONE /\
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at D lo d ce cx mid G tn s /\ fn_inst_ids_distinct func /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr ce mid.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    sa.cs_next_id <= inst.inst_id /\ ptr_covers G tn p s sz /\
    local_ptrs_reserved ce b /\ not_fresh_at b p /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
    n <= type_memory_size tyv /\ type_memory_size tyv <= sz /\
    val_wf tyv v /\ value_has_type tyv v /\
    typed_copy_state_frame b (w2n w) n s t /\
    val_in_memory tyv v (w2n w) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory tyv v (w2n w) mem) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n w <= i /\ i < w2n w+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at b x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    alloca_frame old es sa s0 ce mid s /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP s.vs_allocas aid = SOME ent) /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    lookup_var p t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
    cenv_top_ext old ce out.scopes /\
    stmt_state_rel H ctx func ce cx out t /\
    storage_well_formed_on cx out (FST H) /\
    return_buf_frame d ce sf t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d ce cx out Gf tf t /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce out t /\
    (!aid off len i.
      FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
      (!name a cap. local_region old es.scopes s0 name a cap ==>
        off+len <= a \/ a+cap <= off) /\
      off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  `typed_copy_state_frame b (w2n w) (type_memory_size tyv) s t` by
    (irule typedMemoryCopyTheory.typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n w`, `n`] >> simp[]) >>
  `ghost_inv_at D lo d ce cx mid Gf tf t` by
    (irule annassign_memory_full_ghost_store >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ (type_memory_size _) _ _`)) >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
     rpt strip_tac >> (metis_tac[])) >>
  `stmt_state_rel H ctx func ce cx out t` by suspend "state" >>
  `ghost_inv_at D lo d ce cx out Gf tf t` by suspend "ghost" >>
  `cenv_top_ext old ce out.scopes` by suspend "cenv" >>
  `storage_well_formed_on cx out (FST H)` by suspend "storage" >>
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id ==> off+len <= w2n w \/ w2n w+sz <= off` by
    (rpt strip_tac >>
     `allocas_non_overlapping s` by
       (metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca,
         venomMemDefsTheory.alloca_inv_def]) >>
     `FLOOKUP s.vs_allocas aid = SOME (off,len)` by metis_tac[] >>
     `aid <> inst.inst_id` by decide_tac >>
     fs[venomMemDefsTheory.allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule_all >> simp[]) >>
  `!aid off len i. FLOOKUP s0.vs_allocas aid = SOME (off,len) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off+len ==>
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >>
     `off+len <= w2n w \/ w2n w+sz <= off` by metis_tac[] >>
     first_x_assum irule >> decide_tac) >>
  `alloca_frame old es sa s0 ce out t` by suspend "frame" >>
  qpat_assum `typed_copy_state_frame _ _ n _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  simp[loweringPostsTheory.stmt_lands_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!aid off len i. _ ==> i IN tn0.t_mem` irule >>
  conj_tac >- (qexistsl_tac [`aid`, `len`, `off`] >> simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!aid off len i. _ ==> (i IN tf.t_mem <=> _)` drule_all >> simp[]
QED

Resume annassign_memory_full_installation_post[state]:
  simp[] >> irule stmtSimDeclCopyFrameTheory.stmt_state_rel_declare_copy_frame >>
  simp[] >> qexistsl_tac [`inst`, `s`, `b`, `w`] >> simp[] >>
  qpat_assum `typed_copy_state_frame _ _ (type_memory_size _) _ _`
    (strip_assume_tac o SRULE [typedMemoryCopyTheory.typed_copy_state_frame_def,
                              venomStateTheory.venom_state_component_equality]) >>
  fs[exprSimStorageCopyTheory.copy_static_def,
     venomStateTheory.venom_state_component_equality,
     typedMemoryCopyTheory.typed_copy_frame_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> gvs[]
QED

Resume annassign_memory_full_installation_post[ghost]:
  simp[] >> fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `name = id`
  >- (gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
      `lookup_var p t = lookup_var p s` by
        (fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >> metis_tac[]) >>
      conj_tac
      >- (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
          qexistsl_tac [`G`, `s`, `tn`] >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `lookup_scopes name mid.scopes = SOME entry` by
    gvs[lookup_scopes_def, FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Resume annassign_memory_full_installation_post[frame]:
  rewrite_tac[stmtSimDefsTheory.alloca_frame_def] >> rpt gen_tac >> strip_tac >>
  Q.SUBGOAL_THEN `off + sz' <= w2n w \/ w2n w + sz <= off` assume_tac
  >- metis_tac[] >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [stmtSimDefsTheory.alloca_frame_def]) >>
  disch_then drule_all >> strip_tac >>
  `!x. not_fresh_at b x ==> lookup_var x t = lookup_var x s` by
    fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
  conj_tac
  >- (`mem_bytes_at off sz' t.vs_memory = mem_bytes_at off sz' s.vs_memory` by
        (fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
            typedMemoryCopyTheory.typed_copy_frame_def] >>
         first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `!name q cap. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) cap) ==>
    lookup_var q t = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  Cases_on `n' = id`
  >- (gvs[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  qpat_x_assum `!n b sz. local_region ce mid.scopes s _ _ _ ==> _` irule >>
  qexists_tac `n'` >>
  gvs[loweringStateRelDefsTheory.local_region_def, lookup_scopes_def,
      FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume annassign_memory_full_installation_post[cenv]:
  simp[loweringPostsTheory.cenv_top_ext_def] >>
  rpt strip_tac >> `n' = id` by metis_tac[] >> gvs[] >>
  qpat_x_assum `lookup_scopes id _ = NONE` mp_tac >>
  simp[lookup_scopes_def, CaseEq "option"]
QED

Resume annassign_memory_full_installation_post[storage]:
  irule (iffRL vyperStorageFootprintTheory.storage_well_formed_on_backends) >>
  qexists_tac `mid` >> simp[]
QED

Finalise annassign_memory_full_installation_post

(* RHS enrichment at one concrete, already allocated declaration entry. *)
Theorem annassign_full_rhs_from_entry:
  !DF lo d PG ctx shadow_ctx func shadow_func old ce cx es id typ e
   sa r a b shadow_a shadow_b p sz op s0 G0 tn0 lctx st0 w entry Ga tna.
    declare_local old id typ sa = (ce,r) /\ old.ce_alloca_locals /\
    FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
    sz = type_memory_bytes old typ /\ sz < dimword (:256) /\
    compile_alloc_buffer sz sa =
      (<|buf_operand := Var p; buf_size := sz|>,a) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a =
      (op,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa a func /\ fn_has_code a b func /\
    fn_has_code shadow_a shadow_b shadow_func /\ fn_inst_ids_distinct func /\
    cs_extends sa a /\ cs_extends a b /\
    local_ptrs_reserved old sa /\ local_ptrs_reserved ce a /\
    (!H. dead_lo_ok H (DF H) lo old cx) /\ ret_pc_ok old sa s0 /\
    (!x cap. old.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
      not_fresh_at sa x) /\
    return_buf_frame d old sa s0 /\ alloca_history func s0 /\
    (!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z) /\
    storage_trace_domain cx st0 es.storage_trace /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
    ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
      ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
    not_fresh_at a p /\
    ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
    entry.vs_inst_idx = LENGTH a.cs_current_insts /\
    entry with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
      vs_alloca_next := s0.vs_alloca_next; vs_inst_idx := s0.vs_inst_idx|> = s0 /\
    alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
    lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
    FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    FLOOKUP Ga p = SOME (w2n w,sz) /\
    w2n w+sz < dimword (:256) /\ w2n w+sz <= entry.vs_alloca_next /\
    (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
      FLOOKUP entry.vs_allocas aid = SOME ent) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x entry = lookup_var x s0 /\ FLOOKUP Ga x = FLOOKUP G0 x /\
      op_taint tna (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame old es sa s0 ce es entry /\
    ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es entry /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d ce cx es Ga tna entry) ==>
    not_fresh_at b p /\ local_ptrs_reserved ce b /\
    (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x) /\
    (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,entry,Ga,tna)
      (\H res mid G tn u. ?v.
        res = INL v /\
        expr_post H ctx func ce cx e es a b entry mid v op u /\
        expr_store_bound cx (post_value_type ce e) v op u /\
        ~u.vs_halted /\ mid.gas_obs = [] /\
        u.vs_current_bb = b.cs_current_bb /\
        u.vs_inst_idx = LENGTH b.cs_current_insts /\
        alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
        entry.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d ce cx mid G tn u /\
        ptr_val_ok cx (post_value_type ce e) v op G tn u /\
        (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
        ghost_kept_at lo ce es a Ga tna entry G tn /\
        return_buf_frame d ce b u /\
        MAP FDOM mid.scopes = MAP FDOM es.scopes /\
        lookup_scopes id mid.scopes = NONE /\ not_local_ptr ce mid.scopes p /\
        lookup_var p u = SOME w /\ ptr_covers G tn p u sz /\
        FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
        w2n w+sz < dimword (:256) /\ w2n w+sz <= u.vs_alloca_next /\
        (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
          lookup_var x u = SOME z) /\
        (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
          FLOOKUP u.vs_allocas aid = SOME ent) /\
        (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
        s0.vs_alloca_next <= u.vs_alloca_next /\
        alloca_frame ce es a entry ce mid u /\
        alloca_frame old es sa s0 ce mid u /\
        (!aid off len i.
          FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
          (!name x cap. local_region old es.scopes s0 name x cap ==>
            off+len <= x \/ x+cap <= off) /\
          off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem))
      (\H res mid gt rr. expr_exit res rr /\ halt_exit H cx mid res rr /\
        (ctx_has_dalloca ctx ==> !s. rr = Halt s ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sa a /\ ci_mono a b` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_lower_value_compile_expr,
              pairTheory.SND] >>
  `sa.cs_next_var <= a.cs_next_var /\ a.cs_next_var <= b.cs_next_var /\
   sa.cs_next_id <= a.cs_next_id` by fs[ci_mono_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x` by
    (rpt strip_tac >> metis_tac[not_fresh_at_mono,arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at b p /\ local_ptrs_reserved ce b` by
    (conj_tac >- metis_tac[not_fresh_at_mono] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `a` >> simp[]) >>
  `ce.ce_is_ctor = old.ce_is_ctor /\
   ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc` by
    (qpat_assum `ce with <|ce_vars := _; ce_var_type := _;
                         ce_dynarray_capacity := _|> = old` mp_tac >>
     simp[compile_env_component_equality]) >>
  `(!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
   (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x)` by
    (fs[ret_pc_ok_def] >> metis_tac[]) >>
  simp[] >>
  `return_buf_frame d ce a entry` by
    (irule return_buf_frame_frame >> qexistsl_tac [`old`,`s0`,`sa`] >>
     simp[] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (`stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es entry` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `stmt_state_rel _ ctx func ce cx es entry`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,
    `op`,`entry`,`Ga`,`tna`] mp_tac) >>
  (impl_tac >-
    (asm_rewrite_tac[] >> rpt conj_tac
     >- (qpat_x_assum `!H. dead_lo_ok H (DF H) lo old cx` mp_tac >>
         simp[bodyPtrDefsTheory.dead_lo_ok_def])
     >~ [`gas_admissible _ expr_res_ok es`]
     >- metis_tac[annassign_admissible_rhs] >>
     fs[ret_pc_ok_def] >> metis_tac[])) >>
  disch_tac >> irule gas_outcome_full_post_source >>
  goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
  simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "success"
QED

Resume annassign_full_rhs_from_entry[success]:
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP eval_read_preserves_scopes_dom) >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by suspend "horizon" >>
  `stmt_state_rel H ctx func ce cx es entry` by metis_tac[] >>
  `lookup_scopes id ee.scopes = NONE` by
    (Cases_on `lookup_scopes id ee.scopes` >> simp[] >>
     drule_all vyperTypeEnvPreservationTheory.lookup_scopes_same_fdoms_some >> simp[]) >>
  `not_local_ptr ce ee.scopes p` by
    (irule local_ptrs_reserved_not_live >> conj_tac
     >- (qexistsl_tac [`id`,`type_memory_bytes old typ`] >> simp[]) >>
     qexists_tac `a` >> simp[]) >>
  `return_buf_frame d ce b t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`entry`,`a`] >>
     fs[expr_post_def]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_bytes old typ)` by
    (fs[expr_post_def] >> metis_tac[]) >>
  `ptr_covers G' tn' p t (type_memory_bytes old typ)` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Ga`,`entry`,`tna`] >>
     fs[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  `alloca_frame ce es a entry ce ee t` by
    (drule expr_post_alloca_frame >> disch_then irule >> simp[]) >>
  `alloca_frame old es sa s0 ce ee t` by
    (irule alloca_frame_trans >>
     qexistsl_tac [`ce`,`es`,`entry`,`a`] >> simp[]) >>
  `!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name x cap. local_region old es.scopes s0 name x cap ==>
      off+len <= x \/ x+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tn'.t_mem ==> i IN tn0.t_mem` by
    suspend "taint" >>
  fs[expr_post_def,bodyPtrDefsTheory.ghost_kept_at_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]
QED

Resume annassign_full_rhs_from_entry[horizon]:
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> strip_tac >>
  drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  disch_then drule >> simp[]
QED

Resume annassign_full_rhs_from_entry[taint]:
  fs[bodyPtrDefsTheory.ghost_kept_at_def] >>
  qpat_assum `alloca_frame old es sa s0 ce es entry`
    (mp_then Any mp_tac alloca_taint_kept_trans) >>
  disch_then (qspecl_then [`tn'`,`tna`,`tn0`,`a`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`aid`,`off`,`len`,`i`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >>
  (impl_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac)) >> simp[]
QED

Finalise annassign_full_rhs_from_entry

(* Capacity-generic allocation, before the RHS or empty-value execution. *)
Theorem annassign_full_alloc_entry:
  !DF lo d PG explicit ctx func old ce cx es id typ st0 sa r a p sz s0 G0 tn0.
    declare_local old id typ sa = (ce,r) /\ old.ce_alloca_locals /\
    FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
    sz = type_memory_bytes old typ /\ sz < dimword (:256) /\
    compile_alloc_buffer sz sa =
      (<|buf_operand := Var p; buf_size := sz|>,a) /\
    fn_has_code sa a func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved old sa /\ cs_extends sa a /\
    ret_pc_ok old sa s0 /\
    (!x cap. old.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
      not_fresh_at sa x) /\
    return_buf_frame d old sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
      s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp) /\ storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func old cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d old cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?w entry Ga tna.
      FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
      (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
      ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
        ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
      ce.ce_return_buf = old.ce_return_buf /\
      ce.ce_return_pc = old.ce_return_pc /\ ce.ce_imm_alloca = old.ce_imm_alloca /\
      MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
      not_fresh_at a p /\ local_ptrs_reserved ce a /\
      (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
      (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
      (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
      ret_pc_ok ce a entry /\ return_buf_frame d ce a entry /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
      ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
      entry.vs_inst_idx = LENGTH a.cs_current_insts /\
      entry with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
        vs_alloca_next := s0.vs_alloca_next; vs_inst_idx := s0.vs_inst_idx|> = s0 /\
      alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
      lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
      FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      FLOOKUP Ga p = SOME (w2n w,sz) /\
      w2n w+sz < dimword (:256) /\ w2n w+sz <= entry.vs_alloca_next /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
        FLOOKUP entry.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x entry = lookup_var x s0 /\ FLOOKUP Ga x = FLOOKUP G0 x /\
        op_taint tna (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame old es sa s0 ce es entry /\
      ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func ce cx es entry /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d ce cx es Ga tna entry)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func old cx es s0 /\
   ghost_inv_at (DF (storage_trace_horizon es.storage_trace)) lo d old cx es G0 tn0 s0` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by metis_tac[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path_exact) >>
  disch_then (qspecl_then [`tn0`,`explicit`,`PG`,`G0`] strip_assume_tac) >> gvs[] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d old cx es G' tn' t` by
    (rpt strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     rpt (first_assum (irule_at Any)) >>
     qexistsl_tac [`w2n w + type_memory_bytes old typ`,`G0`] >>
     simp[] >> metis_tac[ret_pc_ok_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func old cx es t` by
    (rpt strip_tac >> first_x_assum irule >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  suspend "declare"
QED

Resume annassign_full_alloc_entry[declare]:
  drule_all declare_local_ptr >> strip_tac >>
  drule compile_alloc_buffer_parts >> simp[] >> strip_tac >> gvs[] >>
  `ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc /\
   ce.ce_imm_alloca = old.ce_imm_alloca` by
    (qpat_assum `ce with <|ce_vars := _; ce_dynarray_capacity := _;
      ce_var_type := _|> = old` mp_tac >>
     simp[compile_env_component_equality]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es t /\
    ghost_inv_at (DF H) lo d ce cx es G' tn' t` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule stmt_state_rel_declare_local_entry >>
         goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
         simp[] >> metis_tac[]) >>
     `ghost_inv_at (DF H) lo d old cx es G' tn' t` by metis_tac[] >>
     fs[bodyPtrDefsTheory.ghost_inv_at_def] >> conj_tac
     >- (rpt gen_tac >> strip_tac >> Cases_on `name = id` >> gvs[] >>
         qpat_x_assum `!name entry p sz. _`
           (qspecl_then [`name`,`entry`,`p`,`sz`] mp_tac) >> simp[]) >>
     simp[] >> Cases_on `d` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def] >>
     PairCases_on `x` >> gvs[bodyPtrDefsTheory.return_buf_ptr_def]) >>
  `~t.vs_halted /\ t.vs_memory = s0.vs_memory` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|> = s0` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  suspend "frame"
QED

Resume annassign_full_alloc_entry[frame]:
  `alloca_frame old es sa s0 old es t` by
    (irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
       alloca_frame_of_mem_frame) >> asm_rewrite_tac[] >> simp[] >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`func`] >> simp[]) >>
  `alloca_frame old es sa s0 ce es t` by
    (qpat_x_assum `alloca_frame old es sa s0 old es t`
       (assume_tac o REWRITE_RULE [alloca_frame_def]) >>
     pure_rewrite_tac[alloca_frame_def] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!aid off sz. _` (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
     conj_tac >- simp[] >> rpt strip_tac >>
     qpat_x_assum `!n b sz'. local_region old es.scopes t n b sz' ==> _` irule >>
     qexists_tac `n` >> fs[loweringStateRelDefsTheory.local_region_def] >>
     `n <> id` by (strip_tac >> gvs[]) >> metis_tac[]) >>
  `!aid off cap. FLOOKUP s0.vs_allocas aid = SOME (off,cap) ==>
    off+cap <= s0.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ old _ _ s0`
       (mp_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def,alloca_next_valid_def] >>
     strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!aid base sz. _` drule >> simp[arithmeticTheory.ADD_COMM]) >>
  `!name off cap. local_region old es.scopes s0 name off cap ==>
    off+cap <= s0.vs_alloca_next` by metis_tac[body_local_region_frontier] >>
  `ghost_kept_at lo old es sa G0 tn0 s0 G' tn'` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G0`,`w2n w + type_memory_bytes old typ`,`s0`,`tn0`] >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  suspend "finish"
QED

Resume annassign_full_alloc_entry[finish]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes old typ))]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[exprSimAllocTheory.buffer_alloc_code] >>
  `local_ptrs_reserved ce a` by
    (drule_all declare_local_reserved >>
     disch_then (irule o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
       local_ptrs_reserved_next_var)) >> simp[]) >>
  `ret_pc_ok ce a t` by
    (irule ret_pc_ok_frame >>
     goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >> simp[] >> metis_tac[]) >>
  `return_buf_frame d ce a t` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`w`,`t`,`G'`,`tn'`] >> simp[] >> metis_tac[ret_pc_ok_def]
QED

Finalise annassign_full_alloc_entry

(* The common allocation/RHS prefix: allocation witnesses precede all horizons. *)
Theorem annassign_full_alloc_rhs_prefix:
  !DF lo d PG ctx shadow_ctx func shadow_func old ce cx es id typ e
   st0 sa r a b shadow_a shadow_b p sz op s0 G0 tn0 lctx.
    declare_local old id typ sa = (ce,r) /\ old.ce_alloca_locals /\
    FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
    sz = type_memory_bytes old typ /\ sz < dimword (:256) /\
    compile_alloc_buffer sz sa =
      (<|buf_operand := Var p; buf_size := sz|>,a) /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_a =
      (op,shadow_b) /\
    gas_shadow_state a shadow_a /\ gas_shadow_state b shadow_b /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa a func /\ fn_has_code a b func /\
    fn_has_code shadow_a shadow_b shadow_func /\ fn_inst_ids_distinct func /\
    cs_extends sa a /\ cs_extends a b /\
    local_ptrs_reserved old sa /\ local_ptrs_reserved ce a /\
    (!H. dead_lo_ok H (DF H) lo old cx) /\
    ret_pc_ok old sa s0 /\
    (!x cap. old.ce_return_buf = SOME (PtrVar (Var x) cap) ==>
      not_fresh_at sa x) /\
    return_buf_frame d old sa s0 /\ alloca_history func s0 /\
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
    storage_trace_domain cx st0 es.storage_trace /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func old cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d old cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?w entry Ga tna.
      FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
      (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
      ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
        ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
      MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
      not_fresh_at a p /\ not_fresh_at b p /\
      local_ptrs_reserved ce b /\
      (!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x) /\
      (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
      (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
      (!H. gas_origin_ptr_path
        (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
      ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
      entry.vs_inst_idx = LENGTH a.cs_current_insts /\
      entry with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
        vs_alloca_next := s0.vs_alloca_next; vs_inst_idx := s0.vs_inst_idx|> = s0 /\
      alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
      lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
      FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      FLOOKUP Ga p = SOME (w2n w,sz) /\
      w2n w+sz < dimword (:256) /\ w2n w+sz <= entry.vs_alloca_next /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
        FLOOKUP entry.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x entry = lookup_var x s0 /\ FLOOKUP Ga x = FLOOKUP G0 x /\
        op_taint tna (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame old es sa s0 ce es entry /\
      ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func ce cx es entry /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d ce cx es Ga tna entry) /\
      gas_outcome_full
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
        (es,entry,Ga,tna)
        (\H res mid G tn u. ?v.
          res = INL v /\
          expr_post H ctx func ce cx e es a b entry mid v op u /\
          expr_store_bound cx (post_value_type ce e) v op u /\
          ~u.vs_halted /\ mid.gas_obs = [] /\
          u.vs_current_bb = b.cs_current_bb /\
          u.vs_inst_idx = LENGTH b.cs_current_insts /\
          alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          entry.vs_alloca_next <= u.vs_alloca_next /\
          ghost_inv_at (DF H) lo d ce cx mid G tn u /\
          ptr_val_ok cx (post_value_type ce e) v op G tn u /\
          (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
          ghost_kept_at lo ce es a Ga tna entry G tn /\
          return_buf_frame d ce b u /\
          MAP FDOM mid.scopes = MAP FDOM es.scopes /\
          lookup_scopes id mid.scopes = NONE /\ not_local_ptr ce mid.scopes p /\
          lookup_var p u = SOME w /\ ptr_covers G tn p u sz /\
          FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
          w2n w+sz < dimword (:256) /\ w2n w+sz <= u.vs_alloca_next /\
          (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==>
            lookup_var x u = SOME z) /\
          (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
            FLOOKUP u.vs_allocas aid = SOME ent) /\
          (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
            op_taint tn (Var x) = op_taint tn0 (Var x)) /\
          s0.vs_alloca_next <= u.vs_alloca_next /\
          alloca_frame ce es a entry ce mid u /\
          alloca_frame old es sa s0 ce mid u /\
          (!aid off len i.
            FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
            (!name x cap. local_region old es.scopes s0 name x cap ==>
              off+len <= x \/ x+cap <= off) /\
            off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem))
        (\H res mid gt rr. expr_exit res rr /\ halt_exit H cx mid res rr /\
          (ctx_has_dalloca ctx ==> !s. rr = Halt s ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (strip_tac >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func old cx es s0` by
       metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     conj_tac >- metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
     drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  drule_all annassign_full_alloc_entry >>
  disch_then (qspecl_then [`PG`,`gas_explicit_sites ctx shadow_ctx`]
    (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac)) >>
  `!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`
       (qspec_then `ARB` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
       qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _` (fn safe =>
       ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
         (LIST_CONJ [path,phi,safe]))))))) >>
  qpat_assum `alloca_frame old es sa s0 ce es entry`
    (mp_then Any
      (fn rhs => qpat_assum `lower_value compile_expr ce (expr_type e) e a = (op,b)`
        (mp_then (Pat `lower_value _ _ _ _ _ = _`) drule_all rhs))
      annassign_full_rhs_from_entry) >>
  strip_tac >>
  qexistsl_tac [`w`,`entry`,`Ga`,`tna`] >> asm_rewrite_tac[] >>
  gen_tac >> first_x_assum irule
QED

(* Successful aggregate declarations share this join. *)
Theorem annassign_memory_full_suffix_post:
  compile_assign_value ce (Var p) LocMemory (Var xs) F src_loc
    dty sty (type_memory_bytes ce dty) b = ((),sf) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func ce cx mid s /\
  fn_has_code b sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce b /\ alloca_history func s /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      len = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce sty = n /\ type_memory_size stv = n /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv <= sz /\ n < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at b xs /\ not_fresh_at b p /\
  lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\ inst.inst_id < b.cs_next_id /\
  ptr_covers G tn xs s n /\ ptr_covers G tn p s sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw+n < dimword (:256) /\
  w2n dw+type_memory_size dtv < dimword (:256) /\
  (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw+type_memory_size dtv <= s.vs_alloca_next) /\
  (src_loc = SOME LocMemory ==>
    expr_val_at ce cx sty start b mid v (Var xs) s) /\
  (src_loc <> SOME LocMemory ==>
    w2n sw+n <= w2n dw \/ w2n dw+type_memory_size dtv <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\
  new_variable id dtv v mid = (INL (),out) /\
  mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
  out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest /\
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  (!H. valid_horizon cx st0 H out.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid G tn s) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  sa.cs_next_id <= inst.inst_id /\ sa.cs_next_id <= b.cs_next_id /\
  (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
  alloca_frame old es sa s0 ce mid s /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name a cap. local_region old es.scopes s0 name a cap ==>
      off+len <= a \/ a+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  return_buf_frame d ce b s /\ ~block_is_terminated sf /\
  b.cs_next_var <= sf.cs_next_var ==>
  ?t Gf tf.
    lookup_var p t = SOME dw /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    !H. valid_horizon cx st0 H out.storage_trace ==>
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce out.scopes /\
      stmt_state_rel H ctx func ce cx out t /\
      storage_well_formed_on cx out (FST H) /\
      return_buf_frame d ce sf t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx out Gf tf t /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame old es sa s0 ce out t /\
      (!aid off len i.
        FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region old es.scopes s0 name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (INST_TYPE [beta |-> ``:256``] annassign_memory_full_assign_path) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`u`,`sm`,`Gu`,`tnu`,`t`,`Gf`,`tf`] strip_assume_tac)) >>
  `alloca_frame old es sa s0 ce mid u` by suspend "staging_frame" >>
  `!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name a cap. local_region old es.scopes s0 name a cap ==>
      off+len <= a \/ a+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tnu.t_mem ==> i IN tn0.t_mem` by
    suspend "staging_taint" >>
  `return_buf_frame d ce sf t` by suspend "return_frame" >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac
  >- fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
         venomStateTheory.venom_state_component_equality] >>
  conj_tac
  >- fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
         venomStateTheory.venom_state_component_equality] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx mid u /\
   ghost_inv_at (DF H) lo d ce cx mid Gu tnu u` by
    (conj_tac
     >- (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ s ==>
             stmt_state_rel h _ _ _ _ _ u` irule >> simp[]) >>
     qpat_assum `!dead depth. ghost_inv_at dead _ depth _ _ _ G tn s ==>
       ghost_inv_at dead _ depth _ _ _ Gu tnu u` irule >> simp[]) >>
  match_mp_tac
    (let
       val theorem = annassign_memory_full_installation_post
       val (vars, _) = strip_forall (concl theorem)
       val body = UNDISCH (SPECL vars theorem)
     in
       GENL vars (DISCH_ALL (CONJUNCT2 (CONJUNCT2 body)))
     end) >>
  qexistsl_tac [`mid`,`sm`,`u`,`Gu`,`tnu`,`id`,`p`,`sz`,`dw`,
    `inst`,`type_memory_size dtv`,`dtv`,`v`,`sc`,`rest`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, metis_tac[]]
QED

Resume annassign_memory_full_suffix_post[staging_frame]:
  irule alloca_frame_trans >> qexistsl_tac [`ce`,`mid`,`s`,`b`] >> simp[]
QED

Resume annassign_memory_full_suffix_post[staging_taint]:
  rpt strip_tac >>
  `!name a cap. local_region ce mid.scopes s name a cap ==>
    off+len <= a \/ a+cap <= off` by
    (qpat_x_assum `alloca_frame old es sa s0 ce mid s` mp_tac >>
     rewrite_tac[alloca_frame_def] >>
     disch_then (qspecl_then [`aid`,`off`,`len`] mp_tac) >> asm_rewrite_tac[] >>
     disch_then (assume_tac o CONJUNCT2) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP s.vs_allocas aid = SOME (off,len)` by
    (qpat_x_assum `!aid ent. FLOOKUP s0.vs_allocas _ = _ ==> _` drule_all >> simp[]) >>
  `aid < b.cs_next_id` by decide_tac >>
  `i IN tn.t_mem` by
    (qpat_x_assum `!aid off len i. FLOOKUP s.vs_allocas _ = _ /\ _ ==> _`
       drule_all >> asm_rewrite_tac[]) >>
  qpat_x_assum `!aid off len i. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    drule_all >> asm_rewrite_tac[]
QED

Resume annassign_memory_full_suffix_post[return_frame]:
  `t.vs_alloca_next = u.vs_alloca_next` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_tac o AP_TERM ``\z:venom_state. z.vs_alloca_next``) >> simp[]) >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qexistsl_tac [`ce`,`s`,`b`] >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at b x ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!x. not_fresh_at sm x ==> _` drule_all >> simp[]
QED

Finalise annassign_memory_full_suffix_post

(* Direct bytes copies read the rounded live count, not the maximum source
   capacity.  The existing runtime path already fixes all joint witnesses. *)
Theorem annassign_memory_full_bytes_store_path:
  compile_store_memory cenv (Var xs) (Var xd) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type sty /\ is_bytestring_type dty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
          (?str. v = StringV str /\ len = LENGTH str)) /\
    32 + 32 * word_size len <= type_memory_size stv /\
    32 + 32 * word_size len <= type_memory_size dtv` by
    (qspecl_then [`tenv`,`sty`,`stv`] mp_tac valueCopyBytesTheory.bytestring_type_value >>
     qspecl_then [`tenv`,`dty`,`dtv`] mp_tac valueCopyBytesTheory.bytestring_type_value >>
     simp[] >> rpt strip_tac >> gvs[] >> Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def,valueEncodingTheory.type_memory_size_def] >>
     conj_tac >> irule exprSimPropsTheory.word_size_monotone >> simp[]) >>
  `compile_store_bytestring (Var xs) (Var xd) sa = ((),sb)` by
    gvs[compile_store_memory_def] >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next` by decide_tac >>
  `len + 31 < dimword (:256)` by
    (`len + 31 < ((len+31) DIV 32 + 1)*32` by
       simp[GSYM arithmeticTheory.DIV_LE_X] >>
     gvs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  `ptr_covers G tn xs s (32 + 32 * word_size len) /\
   ptr_covers G tn xd s (32 + 32 * word_size len)` by
    metis_tac[ptr_covers_mono] >>
  drule log_full_bytes_store_runtime_path >>
  disch_then (drule_at (Pat `!mem. mem_agree_outside _ _ mem ==> val_in_memory _ _ _ mem`)) >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (drule_at (Pat `lookup_var xs s = _`)) >>
  disch_then (drule_at (Pat `lookup_var xd s = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `len + 31 < dimword (:256)`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `val_in_memory dtv v (w2n dw) t.vs_memory` by
    (gvs[] >> first_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> simp[] >>
  fs[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, metis_tac[]]
QED

(* Direct bytes installation uses the live byte count for source coverage. *)
Theorem annassign_memory_full_bytes_suffix_post:
  compile_assign_value ce (Var p) LocMemory (Var xs) F src_loc
    dty sty (type_memory_bytes ce dty) b = ((),sf) /\
  ~is_word_type dty /\ ~is_word_type sty /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  src_loc <> SOME LocMemory /\
  stmt_state_rel (H0 : (bool # 256 word # type_value) list # num list)
    ctx func ce cx mid s /\
  fn_has_code b sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce b /\ alloca_history func s /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,len). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      len = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  type_memory_bytes ce sty = n /\ type_memory_size stv = n /\
  type_memory_bytes ce dty = type_memory_size dtv /\
  type_memory_size dtv <= sz /\ n < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at b xs /\ not_fresh_at b p /\
  lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\ inst.inst_id < b.cs_next_id /\
  ptr_covers G tn xs s n /\ ptr_covers G tn p s sz /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n dw+type_memory_size dtv < dimword (:256) /\
  (n = 0 \/ w2n sw+n <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw+type_memory_size dtv <= s.vs_alloca_next) /\
  (src_loc = SOME LocMemory ==>
    expr_val_at ce cx sty start b mid v (Var xs) s) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at b x) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\
  new_variable id dtv v mid = (INL (),out) /\
  mid.scopes = sc::rest /\ lookup_scopes id mid.scopes = NONE /\
  out = mid with scopes :=
    (sc |+ (id,<|assignable := T; type := dtv; value := v; popped := []|>))::rest /\
  (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
  ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
            ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
  FLOOKUP old.ce_vars id = NONE /\
  (!H. valid_horizon cx st0 H out.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid s /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid G tn s) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  not_local_ptr ce mid.scopes p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
  sa.cs_next_id <= inst.inst_id /\ sa.cs_next_id <= b.cs_next_id /\
  (!x. not_fresh_at sa x ==> not_fresh_at b x) /\
  alloca_frame old es sa s0 ce mid s /\
  (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP s.vs_allocas aid = SOME ent) /\
  (!aid off len i.
    FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name a cap. local_region old es.scopes s0 name a cap ==>
      off+len <= a \/ a+cap <= off) /\
    off <= i /\ i < off+len /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x s = SOME z) /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  return_buf_frame d ce b s /\ ~block_is_terminated sf /\
  b.cs_next_var <= sf.cs_next_var ==>
  ?t Gf tf.
    lookup_var p t = SOME dw /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    !H. valid_horizon cx st0 H out.storage_trace ==>
      stmt_lands lctx sf (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sf /\
      cenv_top_ext old ce out.scopes /\
      stmt_state_rel H ctx func ce cx out t /\
      storage_well_formed_on cx out (FST H) /\
      return_buf_frame d ce sf t /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx out Gf tf t /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x t = SOME z) /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame old es sa s0 ce out t /\
      (!aid off len i.
        FLOOKUP s0.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
        (!name a cap. local_region old es.scopes s0 name a cap ==>
          off+len <= a \/ a+cap <= off) /\
        off <= i /\ i < off+len /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `ptr_covers G tn p s (type_memory_size dtv)` by
    (metis_tac[ptr_covers_mono]) >>
  `compile_store_memory ce (Var xs) (Var p) dty sty b = ((),sf)` by
    gvs[compile_assign_value_def] >>
  qpat_x_assum `type_memory_size stv = n` (SUBST_ALL_TAC o SYM) >>
  drule annassign_memory_full_bytes_store_path >>
  disch_then (drule_at (Pat `evaluate_type _ sty = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `value_has_type stv _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var p s = _`)) >>
  disch_then (drule_at (Pat `lookup_var xs s = _`)) >>
  disch_then (qspecl_then [`explicit`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, metis_tac[]])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`] strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `typed_copy_state_frame _ _ _ s t`
       (fn th => rewrite_tac[MATCH_MP
         typedCopyOriginPtrBaseTheory.typed_copy_state_frame_allocas_below_fmp th]) >>
     first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (metis_tac[body_full_path_alloca_history]) >>
  `return_buf_frame d ce sf t` by suspend "return_frame" >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac
  >- fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
         venomStateTheory.venom_state_component_equality] >>
  conj_tac
  >- fs[typedMemoryCopyTheory.typed_copy_state_frame_def,
         venomStateTheory.venom_state_component_equality] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  match_mp_tac
    (let
       val theorem = annassign_memory_full_installation_post
       val (vars, _) = strip_forall (concl theorem)
       val body = UNDISCH (SPECL vars theorem)
     in
       GENL vars (DISCH_ALL (CONJUNCT2 (CONJUNCT2 body)))
     end) >>
  qexistsl_tac [`mid`,`b`,`s`,`G`,`tn`,`id`,`p`,`sz`,`dw`,
    `inst`,`type_memory_size dtv`,`dtv`,`v`,`sc`,`rest`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, metis_tac[]]
QED

Resume annassign_memory_full_bytes_suffix_post[return_frame]:
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (mp_tac o AP_TERM ``\z:venom_state. z.vs_alloca_next``) >> simp[]) >>
  irule bodyMemoryDefsTheory.return_buf_frame_frame >>
  qexistsl_tac [`ce`,`s`,`b`] >> simp[] >>
  rpt strip_tac >> qpat_x_assum `!x. not_fresh_at b x ==> _` drule_all >> simp[]
QED

Finalise annassign_memory_full_bytes_suffix_post
