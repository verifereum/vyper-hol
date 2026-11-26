(* The forced snapshot allocates its destination before unwrapping the base. *)
Theory bodyCopiedArrayForcedAllocMods
Ancestors
  bodyCopiedArrayCutDefsMods bodyIfExpAllocMods bodyCopyReadPhysicalTypeMods
  exprSimSubscriptArray loweringHalt exprSimAlloc exprOperandVar
  exprSimProps stateRelProj abiCallerAllocation vyperEvalExprPreservesScopesDom
  bodyFullAllocaFresh vyperState compileEnv allocLimits exprSimHypsDefs
  valueTypingMemoryProps context loweringPosts exprLowering exprLoweringProps
  fragExec vyperStorageFootprint freshWrites arithmetic venomInst finite_map
  loweringStateRelDefs exprSimHyps bodyFullPostsMods exprSimUnwrap
  bodyMemoryDefs bodyFullShadowBodyInv gasExplicitSites

Theorem copied_array_read_type_mods[local]:
  expr_body_pre_mods mods ce cx env obj es /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL saved,mid) ==>
  ?atv. copied_array_type_mods ce cx (obj,mid,raw,saved,et,bd,atv)
Proof
  strip_tac >>
  `bind (eval_expr cx obj) (read_result cx) (es with gas_obs := gs) =
     (INL saved,mid)` by simp[bind_def] >>
  `~is_word_type (expr_type obj)` by simp[is_word_type_def] >>
  drule_all copy_read_physical_type_gas_obs_mods >>
  simp[is_bytestring_type_def] >> strip_tac >>
  `type_alloc_ok ce (expr_type obj)` by
    (irule alloc_limits_expr_type_alloc_ok >>
     fs[expr_body_pre_mods_def]) >>
  qpat_x_assum `type_alloc_ok _ _`
    (mp_tac o REWRITE_RULE [type_alloc_ok_def]) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexists `pt` >>
  gvs[copied_array_type_mods_def,value_has_type_memory_wf]
QED

Theorem copied_array_vv_type_mods[local]:
  compile_expr ce ty obj sa = (bvv,sm) /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  vv_post_mods H ctx fn ce cx obj es sa sm s0 mid raw bvv s ==>
  vv_type bvv = ArrayT et bd
Proof
  Cases_on `bvv` >> strip_tac
  >- (irule compile_array_vv_type >> simp[] >>
      goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
      qexistsl [`H`,`ctx`,`cx`,`es`,`mid`,`fn`,`s`,`s0`,`raw`] >>
      rename1 `StackValue _ op` >>
      qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ raw _ _`
        (mp_tac o REWRITE_RULE [vv_post_mods_def, vv_holds_mods_def]) >>
      simp[vv_post_def] >>
      `vv_place_ptr ce cx mid s raw (StackValue t op)` by
        (Cases_on `raw` >> simp[vv_place_ptr_def] >>
         rename1 `PlaceR pl` >> Cases_on `pl` >> simp[vv_place_ptr_def]) >>
      simp[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  rename1 `LocatedValue _ p` >>
  `~is_bytestring_type (post_value_type ce obj)` by simp[is_bytestring_type_def] >>
  Cases_on `p.ptr_location = LocCode` >>
  fs[vv_type_def,vv_post_mods_def,vv_holds_mods_def,vv_holds_def,
     is_bytestring_type_def]
QED

Theorem copied_array_forced_parts[local]:
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
  vv_type bvv = ArrayT et bd /\ fn_has_code sm sc fn ==>
  ?buf k src l.
    compile_alloc_buffer (type_memory_bytes ce (ArrayT et bd)) sm = (buf,k) /\
    unwrap_value ce bvv k = (src,l) /\
    compile_store_memory ce src buf.buf_operand (ArrayT et bd) (ArrayT et bd) l = ((),sc) /\
    cvv = LocatedValue (ArrayT et bd) (mk_ptr buf.buf_operand LocMemory) /\
    cs_extends sm k /\ cs_extends k l /\ cs_extends l sc /\
    fn_has_code sm k fn /\ fn_has_code k l fn /\ fn_has_code l sc fn
Proof
  strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce (ArrayT et bd)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,k)` >>
  Cases_on `unwrap_value ce bvv k` >>
  rename1 `unwrap_value ce bvv k = (src,l)` >>
  Cases_on `compile_store_memory ce src buf.buf_operand (ArrayT et bd) (ArrayT et bd) l` >>
  rename1 `compile_store_memory _ _ _ _ _ l = (u,last)` >> Cases_on `u` >>
  `cvv = LocatedValue (ArrayT et bd) (mk_ptr buf.buf_operand LocMemory) /\ sc = last` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def,is_word_type_def,compile_materialize_vv_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  qpat_x_assum `sc = last` (SUBST_ALL_TAC o SYM) >>
  `cs_extends sm k` by (drule compile_alloc_buffer_extends >> simp[]) >>
  `cs_extends k l` by (drule unwrap_value_extends >> simp[]) >>
  `cs_extends l sc` by
    (mp_tac (Q.SPECL [`ce`,`src`,`buf.buf_operand`,`ArrayT et bd`,`ArrayT et bd`,`l`]
      ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  `cs_extends k sc` by (irule cs_extends_trans >> qexists `l` >> simp[]) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `fn_has_code k l fn /\ fn_has_code l sc fn` by
    (qspecl_then [`k`,`l`,`sc`,`fn`] irule fn_has_code_split >> simp[]) >>
  qexistsl [`buf`,`k`,`src`,`l`] >> simp[]
QED

Theorem copied_array_forced_alloc_mods:
  expr_body_pre_mods mods ce cx env obj es /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
  read_result cx raw mid = (INL saved,mid) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
  fn_has_code sm sc fn /\ fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx fn ce cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    vv_post_mods H ctx fn ce cx obj es sa sm s0 mid raw bvv s /\
    ghost_inv_at_mods (DF H) lo d ce cx mid G tn s) /\
  ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G tn s /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
  (!tag op. bvv = StackValue tag op /\ ~is_word_type (post_value_type ce obj) ==>
    ptr_buf_ok ce obj op G s) /\
  (!tag p. bvv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce obj p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
    ?v. read_result cx raw mid = (INL v,mid) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
             eval_operand (vv_operand bvv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  alloca_history fn s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?atv buf k src l p w a Ga ta run.
    compile_alloc_buffer (type_memory_size atv) sm = (buf,k) /\
    buf.buf_operand = Var p /\ buf.buf_size = type_memory_size atv /\
    fn_has_code sm k fn /\
    run_inst_seq (emitted_insts sm k) s = OK run /\
    a = run with vs_inst_idx := LENGTH k.cs_current_insts /\
    copied_alloc_cut_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
      (st0,es,sa,s0,G0,tn0) (obj,mid,raw,saved,et,bd,atv)
      (sm,s,G,tn) (k,a,Ga,ta) (l,src,sc,cvv,bvv) (p,w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choose_then `atv` assume_tac) copied_array_read_type_mods >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `vv_type bvv = ArrayT et bd` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     drule_all_then ACCEPT_TAC copied_array_vv_type_mods) >>
  drule_all_then (qx_choosel_then [`buf`,`k`,`src`,`l`] strip_assume_tac)
    copied_array_forced_parts >>
  `!v rt. read_result cx raw mid = (INL v,mid) /\
    evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt ==>
    value_has_type rt v` by fs[copied_array_type_mods_def] >>
  `type_memory_bytes ce (ArrayT et bd) < dimword (:256)` by
    (irule arithmeticTheory.LESS_TRANS >> qexists `2 ** 64` >>
     fs[copied_array_type_mods_def,wordsTheory.dimword_def]) >>
  drule_all ifexp_arm_result_alloc_mods >>
  disch_then (qspecl_then [`gasExplicitSites$gas_explicit_sites ctx shctx`,`PG`] mp_tac) >>
  disch_then (qx_choosel_then [`p`,`w`,`a`,`Ga`,`ta`,`alloc_raw`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "package"
QED

Resume copied_array_forced_alloc_mods[package]:
  `type_memory_bytes ce (ArrayT et bd) = type_memory_size atv /\
   evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv` by
    fs[copied_array_type_mods_def] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `sm.cs_next_var <= k.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gen_tac >> strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at k x` by
    (gen_tac >> strip_tac >> irule not_fresh_at_mono >> qexists `sm` >> simp[] >>
     drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >> simp[]) >>
  `return_buf_frame d ce k a` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sa s0` (irule_at Any) >>
     `sa.cs_next_var <= k.cs_next_var` by decide_tac >>
     `s0.vs_alloca_next <= a.vs_alloca_next` by decide_tac >> simp[] >>
     rpt strip_tac >> first_x_assum (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >> simp[]) >>
  suspend "ghost_kept"
QED

Resume copied_array_forced_alloc_mods[ghost_kept]:
  `ghost_kept_at lo ce es sa G0 tn0 s0 Ga ta` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ sm _ _ _ _ s /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def,ghost_inv_at_mods_def])) >>
     qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
     qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
     irule alloc_buffer_ghost_kept_at >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl [`s`,`w2n w + type_memory_bytes ce (ArrayT et bd)`] >>
     asm_rewrite_tac[] >> rpt conj_tac
     >- (gen_tac >> strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then assume_tac) >>
         qpat_assum `!x. not_fresh_at sm x ==> _ /\ _` (drule_then strip_assume_tac) >> simp[])
     >- (rpt gen_tac >> strip_tac >>
         `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
           (drule eval_expr_preserves_scopes_dom >> simp[]) >>
         `local_region ce mid.scopes s name b sz` by
           (irule local_region_frame_fwd >> qexistsl [`s0`,`sa`,`es.scopes`] >> simp[]) >>
         drule_all_then ACCEPT_TAC body_local_region_frontier) >>
     rpt gen_tac >> strip_tac >>
     `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
     irule abi_caller_allocation_end >> simp[] >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[]) >>
  suspend "close"
QED

Resume copied_array_forced_alloc_mods[close]:
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size atv))] [p])
       (fn_insts fn)` by
    (drule_all_then mp_tac buffer_alloc_code >>
     drule_then strip_assume_tac compile_alloc_buffer_parts >> fs[]) >>
  `lo <= a.vs_alloca_next /\ sm.cs_next_id < k.cs_next_id /\
   s0.vs_alloca_next <= a.vs_alloca_next` by decide_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post_mods H ctx fn ce cx obj es sa k s0 mid raw bvv a` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ a /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `copied_parent_frame_mods (DF,lo,d,ctx,shctx,PG,fn,shfn) ce cx
    (st0,es,sa,s0,G0,tn0) mid obj (k,a,Ga,ta)` by
    (qpat_x_assum `a = alloc_raw with vs_inst_idx := _` kall_tac >>
     qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
     qpat_x_assum `ta = step_taint _ _ _ _` kall_tac >>
     simp[copied_parent_frame_mods_def] >> rpt conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ a /\ _`
           (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >> simp[])
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ a /\ _`
           (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
         pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ k _ _ _ _ a /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >> simp[]) >>
  `ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
    !sw. eval_operand (vv_operand bvv) a = SOME sw ==>
      w2n sw + type_memory_size atv <= lo /\
      (!m. mem_agree_outside ta.t_mem a.vs_memory m ==>
         val_in_memory atv saved (w2n sw) m)` by
    (strip_tac >> qpat_assum `_ /\ _ ==> ?v. _ /\ !rt w. _`
       (drule_all_then strip_assume_tac) >> gvs[]) >>
  `!tag op. bvv = StackValue tag op ==> ptr_buf_ok ce obj op Ga a` by
    (rpt strip_tac >>
     `~is_word_type (post_value_type ce obj)` by simp[is_word_type_def] >>
     qpat_assum `!tag op. _ /\ ~is_word_type _ ==> ptr_buf_ok _ _ _ Ga a`
       (drule_all_then ACCEPT_TAC)) >>
  qexistsl [`atv`,`buf`,`k`,`src`,`l`,`p`,`w`,`a`,`Ga`,`ta`,`alloc_raw`] >>
  `cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var p) LocMemory) /\
   compile_store_memory ce src (Var p) (ArrayT et bd) (ArrayT et bd) l = ((),sc)` by
    (qpat_assum `buf.buf_operand = _` (SUBST1_TAC o SYM) >> simp[]) >>
  pure_rewrite_tac[copied_alloc_cut_mods_def,copied_cursor_mods_def,
    copied_base_frame_mods_def,copied_snapshot_dest_mods_def] >>
  qpat_x_assum `type_memory_bytes _ _ = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise copied_array_forced_alloc_mods
